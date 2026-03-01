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
static const lean_string_object l_Lake_defaultExeRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l_Lake_defaultExeRoot___closed__0 = (const lean_object*)&l_Lake_defaultExeRoot___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lake_defaultExeRoot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_defaultExeRoot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 217, 115, 245, 30, 114, 54, 221)}};
static const lean_object* l_Lake_defaultExeRoot___closed__1 = (const lean_object*)&l_Lake_defaultExeRoot___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_defaultExeRoot = (const lean_object*)&l_Lake_defaultExeRoot___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value;
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
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
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lake_instReprInitTemplate_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__10;
static lean_once_cell_t l_Lake_instReprInitTemplate_repr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__11;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprInitTemplate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprInitTemplate_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprInitTemplate___closed__0 = (const lean_object*)&l_Lake_instReprInitTemplate___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprInitTemplate = (const lean_object*)&l_Lake_instReprInitTemplate___closed__0_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value;
extern uint32_t l_Lean_idBeginEscape;
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
extern uint32_t l_Lean_idEndEscape;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lake.CLI.Init"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "_private.Lake.CLI.Init.0.Lake.escapeName!"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value;
lean_object* l_Lake_StdVer_toString(lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
size_t lean_usize_of_nat(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "failed to initialize git repository"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value;
extern lean_object* l_Lake_Git_upstreamBranch;
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
extern lean_object* l_Lake_defaultConfigFile;
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
extern lean_object* l_Lake_toolchainFileName;
lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_ofString(lean_object*);
lean_object* l_Lake_toUpperCamelCase(lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2;
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "illegal package name '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
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
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_init(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_defaultLakeDir;
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_2 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1, &l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3, &l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0));
x_4 = lean_string_append(x_3, x_1);
x_5 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1));
x_6 = lean_string_append(x_4, x_5);
x_7 = 1;
x_8 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2));
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0));
x_3 = 1;
x_4 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2));
x_7 = lean_string_append(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lake_defaultExeRoot));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1));
x_2 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0, &l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0_once, _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2, &l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0));
x_3 = 1;
x_4 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0));
x_7 = lean_string_append(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_2);
x_14 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2));
x_15 = lean_string_append(x_13, x_14);
x_16 = l_String_quote(x_3);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Std_Format_pretty(x_17, x_7, x_8, x_8);
x_19 = lean_string_append(x_15, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3));
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2));
x_18 = lean_string_append(x_16, x_17);
x_19 = l_String_quote(x_2);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Std_Format_pretty(x_20, x_7, x_8, x_8);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec_ref(x_15);
x_26 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4));
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Std_Format_defWidth;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0));
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3));
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Std_Format_defWidth;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec_ref(x_14);
x_19 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4));
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Std_Format_defWidth;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1));
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Std_Format_defWidth;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec_ref(x_14);
x_19 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_2);
x_20 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2));
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_2);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = l_String_quote(x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Std_Format_pretty(x_20, x_7, x_8, x_8);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec_ref(x_15);
x_26 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_2);
x_20 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2));
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_2);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = l_String_quote(x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Std_Format_pretty(x_20, x_7, x_8, x_8);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec_ref(x_15);
x_26 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0));
x_3 = lean_string_append(x_2, x_1);
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0));
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_InitTemplate_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_InitTemplate_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_InitTemplate_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_std_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_std_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_exe_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_exe_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_lib_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_lib_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_mathLax_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_mathLax_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_math_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_math_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; lean_object* x_31; 
switch (x_1) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(1024u);
x_39 = lean_nat_dec_le(x_38, x_2);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
x_3 = x_40;
goto block_9;
}
else
{
lean_object* x_41; 
x_41 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
x_3 = x_41;
goto block_9;
}
}
case 1:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(1024u);
x_43 = lean_nat_dec_le(x_42, x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
x_10 = x_44;
goto block_16;
}
else
{
lean_object* x_45; 
x_45 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
x_10 = x_45;
goto block_16;
}
}
case 2:
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(1024u);
x_47 = lean_nat_dec_le(x_46, x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
x_17 = x_48;
goto block_23;
}
else
{
lean_object* x_49; 
x_49 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
x_17 = x_49;
goto block_23;
}
}
case 3:
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
x_24 = x_52;
goto block_30;
}
else
{
lean_object* x_53; 
x_53 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
x_24 = x_53;
goto block_30;
}
}
default: 
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(1024u);
x_55 = lean_nat_dec_le(x_54, x_2);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
x_31 = x_56;
goto block_37;
}
else
{
lean_object* x_57; 
x_57 = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
x_31 = x_57;
goto block_37;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__3));
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__5));
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__7));
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
block_37:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__9));
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = l_Repr_addAppParen(x_35, x_2);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_instReprInitTemplate_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 4;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 3;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_le(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_InitTemplate_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_InitTemplate_ctorIdx(x_1);
x_4 = l_Lake_InitTemplate_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instDecidableEqInitTemplate(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__0));
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__1));
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__2));
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__3));
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__4));
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__5));
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__6));
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__7));
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__8));
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__9));
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_ofString_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_idBeginEscape;
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2(void) {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_idEndEscape;
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1);
x_3 = lean_string_append(x_2, x_1);
x_4 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2);
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeIdent(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(350u);
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
x_5 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(353u);
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
x_5 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3);
x_3 = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lake_CLI_Init_0__Lake_escapeIdent(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
x_9 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
x_10 = lean_string_append(x_8, x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_escapeIdent(x_7);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
return x_12;
}
}
default: 
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5);
x_14 = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get_fast(x_1, x_2);
x_12 = 46;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_14; 
x_14 = 45;
x_3 = x_14;
goto block_8;
}
}
else
{
lean_dec(x_2);
return x_1;
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_4 = lean_string_utf8_set(x_1, x_2, x_3);
x_5 = l_Char_utf8Size(x_3);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get_fast(x_1, x_2);
x_12 = 65;
x_13 = lean_uint32_dec_le(x_12, x_11);
if (x_13 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 90;
x_15 = lean_uint32_dec_le(x_11, x_14);
if (x_15 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_16; uint32_t x_17; 
x_16 = 32;
x_17 = lean_uint32_add(x_11, x_16);
x_3 = x_17;
goto block_8;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_4 = lean_string_utf8_set(x_1, x_2, x_3);
x_5 = l_Char_utf8Size(x_3);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_39; 
x_39 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
x_7 = x_39;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_5, 0);
lean_inc(x_40);
lean_dec_ref(x_5);
x_41 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1));
x_42 = l_Lake_StdVer_toString(x_40);
x_43 = lean_string_append(x_41, x_42);
lean_dec_ref(x_42);
x_7 = x_43;
goto block_38;
}
block_38:
{
switch (x_1) {
case 0:
{
lean_dec_ref(x_7);
if (x_2 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_10 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(x_6, x_8, x_10);
lean_dec_ref(x_8);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 1;
x_13 = l_Lean_Name_toString(x_4, x_12);
x_14 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_15 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_14);
x_16 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(x_6, x_13, x_15);
return x_16;
}
}
case 1:
{
lean_dec_ref(x_7);
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_18 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_17);
x_19 = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(x_6, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_21 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_20);
x_22 = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(x_6, x_21);
return x_22;
}
}
case 2:
{
lean_dec_ref(x_7);
if (x_2 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_24 = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(x_6, x_23);
lean_dec_ref(x_23);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 1;
x_26 = l_Lean_Name_toString(x_4, x_25);
x_27 = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(x_6, x_26);
return x_27;
}
}
case 3:
{
if (x_2 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_29 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(x_6, x_28, x_7);
lean_dec_ref(x_28);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = l_Lean_Name_toString(x_4, x_30);
x_32 = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(x_6, x_31, x_7);
return x_32;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_34 = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(x_6, x_33, x_7);
lean_dec_ref(x_33);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 1;
x_36 = l_Lean_Name_toString(x_4, x_35);
x_37 = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(x_6, x_36, x_7);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = 0;
x_6 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1));
x_7 = lean_array_push(x_3, x_6);
x_8 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2));
x_9 = l_Lake_joinRelative(x_1, x_8);
x_10 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3));
x_11 = l_Lake_joinRelative(x_9, x_10);
lean_inc_ref(x_11);
x_12 = l_IO_FS_createDirAll(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_72; 
lean_dec_ref(x_12);
x_13 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(x_11);
x_14 = l_Lake_joinRelative(x_11, x_13);
x_72 = l_System_FilePath_pathExists(x_14);
if (x_72 == 0)
{
uint8_t x_73; uint8_t x_74; 
x_73 = 4;
x_74 = l_Lake_instDecidableEqInitTemplate(x_2, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
x_76 = l_IO_FS_writeFile(x_14, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_76);
x_15 = x_7;
x_16 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_io_error_to_string(x_77);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_array_get_size(x_7);
x_82 = lean_array_push(x_7, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
x_85 = l_IO_FS_writeFile(x_14, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
x_15 = x_7;
x_16 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_io_error_to_string(x_86);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_get_size(x_7);
x_91 = lean_array_push(x_7, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_93 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16));
x_94 = lean_array_push(x_7, x_93);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
block_71:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
x_18 = lean_string_append(x_17, x_14);
lean_dec_ref(x_14);
x_19 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_5);
x_22 = lean_array_push(x_15, x_21);
x_23 = 4;
x_24 = l_Lake_instDecidableEqInitTemplate(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_11);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7));
lean_inc_ref(x_11);
x_28 = l_Lake_joinRelative(x_11, x_27);
x_29 = l_System_FilePath_pathExists(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
x_31 = l_IO_FS_writeFile(x_28, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_31);
x_32 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
x_33 = l_Lake_joinRelative(x_11, x_32);
x_34 = l_System_FilePath_pathExists(x_33);
x_35 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
x_36 = lean_string_append(x_35, x_28);
lean_dec_ref(x_28);
x_37 = lean_string_append(x_36, x_19);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_5);
x_39 = lean_array_push(x_22, x_38);
if (x_34 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
x_41 = l_IO_FS_writeFile(x_33, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_41);
x_42 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
x_43 = lean_string_append(x_42, x_33);
lean_dec_ref(x_33);
x_44 = lean_string_append(x_43, x_19);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_5);
x_46 = lean_box(0);
x_47 = lean_array_push(x_39, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_33);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec_ref(x_41);
x_50 = lean_io_error_to_string(x_49);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_get_size(x_39);
x_54 = lean_array_push(x_39, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_33);
x_56 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12));
x_57 = lean_array_push(x_39, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_28);
lean_dec_ref(x_11);
x_60 = lean_ctor_get(x_31, 0);
lean_inc(x_60);
lean_dec_ref(x_31);
x_61 = lean_io_error_to_string(x_60);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_22);
x_65 = lean_array_push(x_22, x_63);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_28);
lean_dec_ref(x_11);
x_67 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14));
x_68 = lean_array_push(x_22, x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_11);
x_97 = lean_ctor_get(x_12, 0);
lean_inc(x_97);
lean_dec_ref(x_12);
x_98 = lean_io_error_to_string(x_97);
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_array_get_size(x_7);
x_102 = lean_array_push(x_7, x_100);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_8);
lean_inc_ref(x_5);
x_9 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10(void) {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
x_2 = l_Lake_Git_upstreamBranch;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_510; lean_object* x_525; uint8_t x_527; lean_object* x_528; lean_object* x_561; uint8_t x_562; 
x_13 = l_Lake_defaultConfigFile;
x_426 = l_Lake_ConfigLang_fileExtension(x_4);
x_427 = l_System_FilePath_addExtension(x_13, x_426);
lean_dec_ref(x_426);
lean_inc_ref(x_1);
x_428 = l_Lake_joinRelative(x_1, x_427);
x_527 = l_System_FilePath_pathExists(x_428);
x_561 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_562 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_562 == 0)
{
x_528 = lean_box(0);
goto block_560;
}
else
{
lean_object* x_563; uint8_t x_564; 
x_563 = lean_box(0);
x_564 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_564 == 0)
{
if (x_562 == 0)
{
x_528 = lean_box(0);
goto block_560;
}
else
{
size_t x_565; size_t x_566; lean_object* x_567; 
x_565 = 0;
x_566 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_567 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_561, x_565, x_566, x_563, x_7);
if (lean_obj_tag(x_567) == 0)
{
lean_dec_ref(x_567);
x_528 = lean_box(0);
goto block_560;
}
else
{
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_567;
}
}
}
else
{
size_t x_568; size_t x_569; lean_object* x_570; 
x_568 = 0;
x_569 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_570 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_561, x_568, x_569, x_563, x_7);
if (lean_obj_tag(x_570) == 0)
{
lean_dec_ref(x_570);
x_528 = lean_box(0);
goto block_560;
}
else
{
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_570;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_31:
{
if (x_6 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_box(0);
x_19 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(x_1);
x_20 = l_Lake_joinRelative(x_1, x_19);
lean_inc_ref(x_20);
x_21 = l_Lake_joinRelative(x_20, x_13);
x_22 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
x_23 = lean_box(1);
x_24 = l_Lean_Options_empty;
x_25 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
x_26 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_1);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_19);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_13);
lean_ctor_set(x_26, 8, x_21);
lean_ctor_set(x_26, 9, x_22);
lean_ctor_set(x_26, 10, x_23);
lean_ctor_set(x_26, 11, x_24);
lean_ctor_set(x_26, 12, x_25);
lean_ctor_set(x_26, 13, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*14, x_6);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 1, x_6);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 2, x_6);
x_27 = l_Lean_NameSet_empty;
x_28 = l_Lake_updateManifest(x_26, x_27, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_14);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
block_37:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(x_32);
x_36 = lean_apply_2(x_32, x_35, lean_box(0));
x_14 = x_32;
x_15 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_34);
x_14 = x_32;
x_15 = lean_box(0);
goto block_31;
}
}
block_43:
{
switch (x_3) {
case 3:
{
x_32 = x_39;
x_33 = lean_box(0);
x_34 = x_38;
goto block_37;
}
case 4:
{
x_32 = x_39;
x_33 = lean_box(0);
x_34 = x_38;
goto block_37;
}
default: 
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
block_50:
{
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(x_45);
x_49 = lean_apply_2(x_45, x_48, lean_box(0));
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
else
{
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
}
block_124:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(x_1);
x_57 = l_Lake_joinRelative(x_1, x_56);
x_58 = 4;
x_59 = lean_io_prim_handle_mk(x_57, x_58);
lean_dec_ref(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_62 = lean_io_prim_handle_put_str(x_60, x_61);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec_ref(x_62);
x_63 = l_Lake_toolchainFileName;
lean_inc_ref(x_1);
x_64 = l_Lake_joinRelative(x_1, x_63);
x_65 = lean_string_utf8_byte_size(x_51);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_52);
x_68 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_69 = lean_string_append(x_51, x_68);
x_70 = l_IO_FS_writeFile(x_64, x_69);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_38 = x_53;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_83; 
lean_dec(x_53);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_70, 0);
x_83 = !lean_is_exclusive(x_70);
if (x_83 == 0)
{
x_72 = x_70;
x_73 = x_83;
goto block_82;
}
else
{
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_io_error_to_string(x_71);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_apply_2(x_54, x_76, lean_box(0));
x_78 = lean_box(0);
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_78);
x_79 = x_72;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_78);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec_ref(x_51);
x_84 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_84);
lean_dec_ref(x_52);
x_85 = lean_string_utf8_byte_size(x_84);
lean_dec_ref(x_84);
x_86 = lean_nat_dec_eq(x_85, x_66);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_System_FilePath_pathExists(x_64);
lean_dec_ref(x_64);
x_88 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_89 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_89 == 0)
{
x_44 = x_53;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_box(0);
x_91 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_91 == 0)
{
if (x_89 == 0)
{
x_44 = x_53;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; 
x_92 = 0;
x_93 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_54);
x_94 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_88, x_92, x_93, x_90, x_54);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
x_44 = x_53;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_94;
}
}
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; 
x_95 = 0;
x_96 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_54);
x_97 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_88, x_95, x_96, x_90, x_54);
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_97);
x_44 = x_53;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_97;
}
}
}
}
else
{
lean_dec_ref(x_64);
x_38 = x_53;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_110; 
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_62, 0);
x_110 = !lean_is_exclusive(x_62);
if (x_110 == 0)
{
x_99 = x_62;
x_100 = x_110;
goto block_109;
}
else
{
lean_inc(x_98);
lean_dec(x_62);
x_99 = lean_box(0);
x_100 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_io_error_to_string(x_98);
x_102 = 3;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = lean_apply_2(x_54, x_103, lean_box(0));
x_105 = lean_box(0);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_105);
x_106 = x_99;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_123; 
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_59, 0);
x_123 = !lean_is_exclusive(x_59);
if (x_123 == 0)
{
x_112 = x_59;
x_113 = x_123;
goto block_122;
}
else
{
lean_inc(x_111);
lean_dec(x_59);
x_112 = lean_box(0);
x_113 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_io_error_to_string(x_111);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_apply_2(x_54, x_116, lean_box(0));
x_118 = lean_box(0);
if (x_113 == 0)
{
lean_ctor_set(x_112, 0, x_118);
x_119 = x_112;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(x_126);
x_131 = lean_apply_2(x_126, x_130, lean_box(0));
x_51 = x_125;
x_52 = x_127;
x_53 = x_128;
x_54 = x_126;
x_55 = lean_box(0);
goto block_124;
}
block_138:
{
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_51 = x_133;
x_52 = x_135;
x_53 = x_136;
x_54 = x_134;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_dec_ref(x_137);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
}
block_171:
{
lean_object* x_144; uint8_t x_145; 
x_144 = l_Lake_Git_upstreamBranch;
x_145 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_1);
x_148 = l_Lake_GitRepo_checkoutBranch(x_144, x_1, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_array_get_size(x_149);
x_151 = lean_nat_dec_lt(x_146, x_150);
if (x_151 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_141;
x_53 = x_142;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_box(0);
x_153 = lean_nat_dec_le(x_150, x_150);
if (x_153 == 0)
{
if (x_151 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_141;
x_53 = x_142;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
size_t x_154; size_t x_155; lean_object* x_156; 
x_154 = 0;
x_155 = lean_usize_of_nat(x_150);
lean_inc_ref(x_140);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_149, x_154, x_155, x_152, x_140);
lean_dec(x_149);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
x_51 = x_139;
x_52 = x_141;
x_53 = x_142;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_156;
goto block_138;
}
}
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_150);
lean_inc_ref(x_140);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_149, x_157, x_158, x_152, x_140);
lean_dec(x_149);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
x_51 = x_139;
x_52 = x_141;
x_53 = x_142;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_159;
goto block_138;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_148, 1);
lean_inc(x_160);
lean_dec_ref(x_148);
x_161 = lean_array_get_size(x_160);
x_162 = lean_nat_dec_lt(x_146, x_161);
if (x_162 == 0)
{
lean_dec(x_160);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_box(0);
x_164 = lean_nat_dec_le(x_161, x_161);
if (x_164 == 0)
{
if (x_162 == 0)
{
lean_dec(x_160);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
size_t x_165; size_t x_166; lean_object* x_167; 
x_165 = 0;
x_166 = lean_usize_of_nat(x_161);
lean_inc_ref(x_140);
x_167 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_160, x_165, x_166, x_163, x_140);
lean_dec(x_160);
if (lean_obj_tag(x_167) == 0)
{
lean_dec_ref(x_167);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_167;
goto block_138;
}
}
}
else
{
size_t x_168; size_t x_169; lean_object* x_170; 
x_168 = 0;
x_169 = lean_usize_of_nat(x_161);
lean_inc_ref(x_140);
x_170 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_160, x_168, x_169, x_163, x_140);
lean_dec(x_160);
if (lean_obj_tag(x_170) == 0)
{
lean_dec_ref(x_170);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_170;
goto block_138;
}
}
}
}
}
else
{
x_51 = x_139;
x_52 = x_141;
x_53 = x_142;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
}
block_177:
{
if (lean_obj_tag(x_176) == 0)
{
lean_dec_ref(x_176);
x_139 = x_172;
x_140 = x_173;
x_141 = x_174;
x_142 = x_175;
x_143 = lean_box(0);
goto block_171;
}
else
{
lean_dec_ref(x_176);
x_125 = x_172;
x_126 = x_173;
x_127 = x_174;
x_128 = x_175;
x_129 = lean_box(0);
goto block_132;
}
}
block_209:
{
if (x_182 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_unsigned_to_nat(0u);
x_185 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_1);
x_186 = l_Lake_GitRepo_quietInit(x_1, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = lean_array_get_size(x_187);
x_189 = lean_nat_dec_lt(x_184, x_188);
if (x_189 == 0)
{
lean_dec(x_187);
x_139 = x_178;
x_140 = x_179;
x_141 = x_180;
x_142 = x_181;
x_143 = lean_box(0);
goto block_171;
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_box(0);
x_191 = lean_nat_dec_le(x_188, x_188);
if (x_191 == 0)
{
if (x_189 == 0)
{
lean_dec(x_187);
x_139 = x_178;
x_140 = x_179;
x_141 = x_180;
x_142 = x_181;
x_143 = lean_box(0);
goto block_171;
}
else
{
size_t x_192; size_t x_193; lean_object* x_194; 
x_192 = 0;
x_193 = lean_usize_of_nat(x_188);
lean_inc_ref(x_179);
x_194 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_187, x_192, x_193, x_190, x_179);
lean_dec(x_187);
if (lean_obj_tag(x_194) == 0)
{
lean_dec_ref(x_194);
x_139 = x_178;
x_140 = x_179;
x_141 = x_180;
x_142 = x_181;
x_143 = lean_box(0);
goto block_171;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_194;
goto block_177;
}
}
}
else
{
size_t x_195; size_t x_196; lean_object* x_197; 
x_195 = 0;
x_196 = lean_usize_of_nat(x_188);
lean_inc_ref(x_179);
x_197 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_187, x_195, x_196, x_190, x_179);
lean_dec(x_187);
if (lean_obj_tag(x_197) == 0)
{
lean_dec_ref(x_197);
x_139 = x_178;
x_140 = x_179;
x_141 = x_180;
x_142 = x_181;
x_143 = lean_box(0);
goto block_171;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_197;
goto block_177;
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_ctor_get(x_186, 1);
lean_inc(x_198);
lean_dec_ref(x_186);
x_199 = lean_array_get_size(x_198);
x_200 = lean_nat_dec_lt(x_184, x_199);
if (x_200 == 0)
{
lean_dec(x_198);
x_125 = x_178;
x_126 = x_179;
x_127 = x_180;
x_128 = x_181;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_box(0);
x_202 = lean_nat_dec_le(x_199, x_199);
if (x_202 == 0)
{
if (x_200 == 0)
{
lean_dec(x_198);
x_125 = x_178;
x_126 = x_179;
x_127 = x_180;
x_128 = x_181;
x_129 = lean_box(0);
goto block_132;
}
else
{
size_t x_203; size_t x_204; lean_object* x_205; 
x_203 = 0;
x_204 = lean_usize_of_nat(x_199);
lean_inc_ref(x_179);
x_205 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_198, x_203, x_204, x_201, x_179);
lean_dec(x_198);
if (lean_obj_tag(x_205) == 0)
{
lean_dec_ref(x_205);
x_125 = x_178;
x_126 = x_179;
x_127 = x_180;
x_128 = x_181;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_205;
goto block_177;
}
}
}
else
{
size_t x_206; size_t x_207; lean_object* x_208; 
x_206 = 0;
x_207 = lean_usize_of_nat(x_199);
lean_inc_ref(x_179);
x_208 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_198, x_206, x_207, x_201, x_179);
lean_dec(x_198);
if (lean_obj_tag(x_208) == 0)
{
lean_dec_ref(x_208);
x_125 = x_178;
x_126 = x_179;
x_127 = x_180;
x_128 = x_181;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_208;
goto block_177;
}
}
}
}
}
else
{
x_51 = x_178;
x_52 = x_180;
x_53 = x_181;
x_54 = x_179;
x_55 = lean_box(0);
goto block_124;
}
}
block_226:
{
uint8_t x_215; lean_object* x_216; uint8_t x_217; 
lean_inc_ref(x_1);
x_215 = l_Lake_GitRepo_insideWorkTree(x_1);
x_216 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_217 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_217 == 0)
{
x_178 = x_210;
x_179 = x_213;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_box(0);
x_219 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_219 == 0)
{
if (x_217 == 0)
{
x_178 = x_210;
x_179 = x_213;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
size_t x_220; size_t x_221; lean_object* x_222; 
x_220 = 0;
x_221 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_213);
x_222 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_216, x_220, x_221, x_218, x_213);
if (lean_obj_tag(x_222) == 0)
{
lean_dec_ref(x_222);
x_178 = x_210;
x_179 = x_213;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
lean_dec_ref(x_213);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_222;
}
}
}
else
{
size_t x_223; size_t x_224; lean_object* x_225; 
x_223 = 0;
x_224 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_213);
x_225 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_216, x_223, x_224, x_218, x_213);
if (lean_obj_tag(x_225) == 0)
{
lean_dec_ref(x_225);
x_178 = x_210;
x_179 = x_213;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
lean_dec_ref(x_213);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_225;
}
}
}
}
block_248:
{
lean_object* x_234; 
x_234 = l_IO_FS_writeFile(x_227, x_233);
lean_dec_ref(x_233);
lean_dec_ref(x_227);
if (lean_obj_tag(x_234) == 0)
{
lean_dec_ref(x_234);
x_210 = x_228;
x_211 = x_229;
x_212 = x_230;
x_213 = x_231;
x_214 = lean_box(0);
goto block_226;
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_247; 
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_235 = lean_ctor_get(x_234, 0);
x_247 = !lean_is_exclusive(x_234);
if (x_247 == 0)
{
x_236 = x_234;
x_237 = x_247;
goto block_246;
}
else
{
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_box(0);
x_237 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_238 = lean_io_error_to_string(x_235);
x_239 = 3;
x_240 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*1, x_239);
x_241 = lean_apply_2(x_231, x_240, lean_box(0));
x_242 = lean_box(0);
if (x_237 == 0)
{
lean_ctor_set(x_236, 0, x_242);
x_243 = x_236;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_242);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
block_262:
{
if (x_254 == 0)
{
uint8_t x_256; uint8_t x_257; 
x_256 = 4;
x_257 = l_Lake_instDecidableEqInitTemplate(x_3, x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_259 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_258);
lean_dec_ref(x_258);
x_227 = x_249;
x_228 = x_250;
x_229 = x_251;
x_230 = x_252;
x_231 = x_253;
x_232 = lean_box(0);
x_233 = x_259;
goto block_248;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_261 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_260);
lean_dec_ref(x_260);
x_227 = x_249;
x_228 = x_250;
x_229 = x_251;
x_230 = x_252;
x_231 = x_253;
x_232 = lean_box(0);
x_233 = x_261;
goto block_248;
}
}
else
{
lean_dec_ref(x_249);
lean_dec(x_2);
x_210 = x_250;
x_211 = x_251;
x_212 = x_252;
x_213 = x_253;
x_214 = lean_box(0);
goto block_226;
}
}
block_281:
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; uint8_t x_272; 
x_268 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(x_1);
x_269 = l_Lake_joinRelative(x_1, x_268);
x_270 = l_System_FilePath_pathExists(x_269);
x_271 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_272 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_272 == 0)
{
x_249 = x_269;
x_250 = x_263;
x_251 = x_264;
x_252 = x_265;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_box(0);
x_274 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_274 == 0)
{
if (x_272 == 0)
{
x_249 = x_269;
x_250 = x_263;
x_251 = x_264;
x_252 = x_265;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
size_t x_275; size_t x_276; lean_object* x_277; 
x_275 = 0;
x_276 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_266);
x_277 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_271, x_275, x_276, x_273, x_266);
if (lean_obj_tag(x_277) == 0)
{
lean_dec_ref(x_277);
x_249 = x_269;
x_250 = x_263;
x_251 = x_264;
x_252 = x_265;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
lean_dec_ref(x_269);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_277;
}
}
}
else
{
size_t x_278; size_t x_279; lean_object* x_280; 
x_278 = 0;
x_279 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_266);
x_280 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_271, x_278, x_279, x_273, x_266);
if (lean_obj_tag(x_280) == 0)
{
lean_dec_ref(x_280);
x_249 = x_269;
x_250 = x_263;
x_251 = x_264;
x_252 = x_265;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
lean_dec_ref(x_269);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_280;
}
}
}
}
block_322:
{
if (x_288 == 0)
{
uint8_t x_290; uint8_t x_291; 
x_290 = 1;
x_291 = l_Lake_instDecidableEqInitTemplate(x_3, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_284);
x_293 = l_IO_FS_writeFile(x_282, x_292);
lean_dec_ref(x_292);
lean_dec_ref(x_282);
if (lean_obj_tag(x_293) == 0)
{
lean_dec_ref(x_293);
x_263 = x_285;
x_264 = x_286;
x_265 = x_287;
x_266 = x_283;
x_267 = lean_box(0);
goto block_281;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_306; 
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_294 = lean_ctor_get(x_293, 0);
x_306 = !lean_is_exclusive(x_293);
if (x_306 == 0)
{
x_295 = x_293;
x_296 = x_306;
goto block_305;
}
else
{
lean_inc(x_294);
lean_dec(x_293);
x_295 = lean_box(0);
x_296 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_297 = lean_io_error_to_string(x_294);
x_298 = 3;
x_299 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*1, x_298);
x_300 = lean_apply_2(x_283, x_299, lean_box(0));
x_301 = lean_box(0);
if (x_296 == 0)
{
lean_ctor_set(x_295, 0, x_301);
x_302 = x_295;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_301);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_284);
x_307 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
x_308 = l_IO_FS_writeFile(x_282, x_307);
lean_dec_ref(x_282);
if (lean_obj_tag(x_308) == 0)
{
lean_dec_ref(x_308);
x_263 = x_285;
x_264 = x_286;
x_265 = x_287;
x_266 = x_283;
x_267 = lean_box(0);
goto block_281;
}
else
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; uint8_t x_321; 
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_309 = lean_ctor_get(x_308, 0);
x_321 = !lean_is_exclusive(x_308);
if (x_321 == 0)
{
x_310 = x_308;
x_311 = x_321;
goto block_320;
}
else
{
lean_inc(x_309);
lean_dec(x_308);
x_310 = lean_box(0);
x_311 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_io_error_to_string(x_309);
x_313 = 3;
x_314 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set_uint8(x_314, sizeof(void*)*1, x_313);
x_315 = lean_apply_2(x_283, x_314, lean_box(0));
x_316 = lean_box(0);
if (x_311 == 0)
{
lean_ctor_set(x_310, 0, x_316);
x_317 = x_310;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_316);
x_317 = x_319;
goto block_318;
}
block_318:
{
return x_317;
}
}
}
}
}
else
{
lean_dec(x_284);
lean_dec_ref(x_282);
x_263 = x_285;
x_264 = x_286;
x_265 = x_287;
x_266 = x_283;
x_267 = lean_box(0);
goto block_281;
}
}
block_342:
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; 
x_329 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_1);
x_330 = l_Lake_joinRelative(x_1, x_329);
x_331 = l_System_FilePath_pathExists(x_330);
x_332 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_333 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_333 == 0)
{
x_282 = x_330;
x_283 = x_324;
x_284 = x_325;
x_285 = x_326;
x_286 = x_327;
x_287 = x_328;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_box(0);
x_335 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_335 == 0)
{
if (x_333 == 0)
{
x_282 = x_330;
x_283 = x_324;
x_284 = x_325;
x_285 = x_326;
x_286 = x_327;
x_287 = x_328;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
size_t x_336; size_t x_337; lean_object* x_338; 
x_336 = 0;
x_337 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_324);
x_338 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_332, x_336, x_337, x_334, x_324);
if (lean_obj_tag(x_338) == 0)
{
lean_dec_ref(x_338);
x_282 = x_330;
x_283 = x_324;
x_284 = x_325;
x_285 = x_326;
x_286 = x_327;
x_287 = x_328;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
lean_dec_ref(x_330);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec_ref(x_326);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_338;
}
}
}
else
{
size_t x_339; size_t x_340; lean_object* x_341; 
x_339 = 0;
x_340 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_324);
x_341 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_332, x_339, x_340, x_334, x_324);
if (lean_obj_tag(x_341) == 0)
{
lean_dec_ref(x_341);
x_282 = x_330;
x_283 = x_324;
x_284 = x_325;
x_285 = x_326;
x_286 = x_327;
x_287 = x_328;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
lean_dec_ref(x_330);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec_ref(x_326);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_341;
}
}
}
}
block_349:
{
switch (x_3) {
case 0:
{
x_323 = lean_box(0);
x_324 = x_347;
x_325 = x_343;
x_326 = x_344;
x_327 = x_345;
x_328 = x_346;
goto block_342;
}
case 1:
{
x_323 = lean_box(0);
x_324 = x_347;
x_325 = x_343;
x_326 = x_344;
x_327 = x_345;
x_328 = x_346;
goto block_342;
}
default: 
{
lean_dec(x_343);
x_263 = x_344;
x_264 = x_345;
x_265 = x_346;
x_266 = x_347;
x_267 = lean_box(0);
goto block_281;
}
}
}
block_372:
{
lean_object* x_358; 
x_358 = l_IO_FS_writeFile(x_350, x_357);
lean_dec_ref(x_357);
lean_dec_ref(x_350);
if (lean_obj_tag(x_358) == 0)
{
lean_dec_ref(x_358);
x_343 = x_352;
x_344 = x_353;
x_345 = x_354;
x_346 = x_356;
x_347 = x_351;
x_348 = lean_box(0);
goto block_349;
}
else
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; uint8_t x_371; 
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_359 = lean_ctor_get(x_358, 0);
x_371 = !lean_is_exclusive(x_358);
if (x_371 == 0)
{
x_360 = x_358;
x_361 = x_371;
goto block_370;
}
else
{
lean_inc(x_359);
lean_dec(x_358);
x_360 = lean_box(0);
x_361 = x_371;
goto block_370;
}
block_370:
{
lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_362 = lean_io_error_to_string(x_359);
x_363 = 3;
x_364 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*1, x_363);
x_365 = lean_apply_2(x_351, x_364, lean_box(0));
x_366 = lean_box(0);
if (x_361 == 0)
{
lean_ctor_set(x_360, 0, x_366);
x_367 = x_360;
goto block_368;
}
else
{
lean_object* x_369; 
x_369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_369, 0, x_366);
x_367 = x_369;
goto block_368;
}
block_368:
{
return x_367;
}
}
}
}
block_386:
{
uint8_t x_380; uint8_t x_381; 
x_380 = 4;
x_381 = l_Lake_instDecidableEqInitTemplate(x_3, x_380);
if (x_381 == 0)
{
uint8_t x_382; lean_object* x_383; lean_object* x_384; 
x_382 = 1;
lean_inc(x_374);
x_383 = l_Lean_Name_toString(x_374, x_382);
lean_inc(x_374);
x_384 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_383, x_374);
lean_dec_ref(x_383);
x_350 = x_373;
x_351 = x_378;
x_352 = x_374;
x_353 = x_375;
x_354 = x_376;
x_355 = lean_box(0);
x_356 = x_377;
x_357 = x_384;
goto block_372;
}
else
{
lean_object* x_385; 
lean_inc(x_374);
x_385 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_374);
x_350 = x_373;
x_351 = x_378;
x_352 = x_374;
x_353 = x_375;
x_354 = x_376;
x_355 = lean_box(0);
x_356 = x_377;
x_357 = x_385;
goto block_372;
}
}
block_425:
{
if (x_394 == 0)
{
lean_object* x_396; 
x_396 = l_IO_FS_createDirAll(x_388);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; 
lean_dec_ref(x_396);
x_397 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
x_398 = l_IO_FS_writeFile(x_391, x_397);
lean_dec_ref(x_391);
if (lean_obj_tag(x_398) == 0)
{
lean_dec_ref(x_398);
x_373 = x_387;
x_374 = x_389;
x_375 = x_390;
x_376 = x_392;
x_377 = x_393;
x_378 = x_7;
x_379 = lean_box(0);
goto block_386;
}
else
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; uint8_t x_411; 
lean_dec(x_393);
lean_dec_ref(x_392);
lean_dec_ref(x_390);
lean_dec(x_389);
lean_dec_ref(x_387);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_399 = lean_ctor_get(x_398, 0);
x_411 = !lean_is_exclusive(x_398);
if (x_411 == 0)
{
x_400 = x_398;
x_401 = x_411;
goto block_410;
}
else
{
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_box(0);
x_401 = x_411;
goto block_410;
}
block_410:
{
lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_402 = lean_io_error_to_string(x_399);
x_403 = 3;
x_404 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set_uint8(x_404, sizeof(void*)*1, x_403);
x_405 = lean_apply_2(x_7, x_404, lean_box(0));
x_406 = lean_box(0);
if (x_401 == 0)
{
lean_ctor_set(x_400, 0, x_406);
x_407 = x_400;
goto block_408;
}
else
{
lean_object* x_409; 
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_406);
x_407 = x_409;
goto block_408;
}
block_408:
{
return x_407;
}
}
}
}
else
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; uint8_t x_424; 
lean_dec(x_393);
lean_dec_ref(x_392);
lean_dec_ref(x_391);
lean_dec_ref(x_390);
lean_dec(x_389);
lean_dec_ref(x_387);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_412 = lean_ctor_get(x_396, 0);
x_424 = !lean_is_exclusive(x_396);
if (x_424 == 0)
{
x_413 = x_396;
x_414 = x_424;
goto block_423;
}
else
{
lean_inc(x_412);
lean_dec(x_396);
x_413 = lean_box(0);
x_414 = x_424;
goto block_423;
}
block_423:
{
lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_415 = lean_io_error_to_string(x_412);
x_416 = 3;
x_417 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*1, x_416);
x_418 = lean_apply_2(x_7, x_417, lean_box(0));
x_419 = lean_box(0);
if (x_414 == 0)
{
lean_ctor_set(x_413, 0, x_419);
x_420 = x_413;
goto block_421;
}
else
{
lean_object* x_422; 
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_419);
x_420 = x_422;
goto block_421;
}
block_421:
{
return x_420;
}
}
}
}
else
{
lean_dec_ref(x_391);
lean_dec_ref(x_388);
x_373 = x_387;
x_374 = x_389;
x_375 = x_390;
x_376 = x_392;
x_377 = x_393;
x_378 = x_7;
x_379 = lean_box(0);
goto block_386;
}
}
block_466:
{
lean_object* x_435; lean_object* x_436; 
lean_inc(x_434);
lean_inc(x_429);
lean_inc(x_2);
x_435 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_429, x_434);
x_436 = l_IO_FS_writeFile(x_428, x_435);
lean_dec_ref(x_435);
lean_dec_ref(x_428);
if (lean_obj_tag(x_436) == 0)
{
lean_dec_ref(x_436);
if (lean_obj_tag(x_430) == 1)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; uint8_t x_444; 
x_437 = lean_ctor_get(x_430, 0);
lean_inc(x_437);
lean_dec_ref(x_430);
x_438 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
lean_inc(x_437);
x_439 = l_System_FilePath_withExtension(x_437, x_438);
x_440 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(x_439);
x_441 = l_Lake_joinRelative(x_439, x_440);
x_442 = l_System_FilePath_pathExists(x_441);
x_443 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_444 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_444 == 0)
{
x_387 = x_437;
x_388 = x_439;
x_389 = x_429;
x_390 = x_431;
x_391 = x_441;
x_392 = x_432;
x_393 = x_434;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_445; uint8_t x_446; 
x_445 = lean_box(0);
x_446 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_446 == 0)
{
if (x_444 == 0)
{
x_387 = x_437;
x_388 = x_439;
x_389 = x_429;
x_390 = x_431;
x_391 = x_441;
x_392 = x_432;
x_393 = x_434;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
size_t x_447; size_t x_448; lean_object* x_449; 
x_447 = 0;
x_448 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_449 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_443, x_447, x_448, x_445, x_7);
if (lean_obj_tag(x_449) == 0)
{
lean_dec_ref(x_449);
x_387 = x_437;
x_388 = x_439;
x_389 = x_429;
x_390 = x_431;
x_391 = x_441;
x_392 = x_432;
x_393 = x_434;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
lean_dec_ref(x_441);
lean_dec_ref(x_439);
lean_dec(x_437);
lean_dec(x_434);
lean_dec_ref(x_432);
lean_dec_ref(x_431);
lean_dec(x_429);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_449;
}
}
}
else
{
size_t x_450; size_t x_451; lean_object* x_452; 
x_450 = 0;
x_451 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_452 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_443, x_450, x_451, x_445, x_7);
if (lean_obj_tag(x_452) == 0)
{
lean_dec_ref(x_452);
x_387 = x_437;
x_388 = x_439;
x_389 = x_429;
x_390 = x_431;
x_391 = x_441;
x_392 = x_432;
x_393 = x_434;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
lean_dec_ref(x_441);
lean_dec_ref(x_439);
lean_dec(x_437);
lean_dec(x_434);
lean_dec_ref(x_432);
lean_dec_ref(x_431);
lean_dec(x_429);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_452;
}
}
}
}
else
{
lean_dec(x_430);
x_343 = x_429;
x_344 = x_431;
x_345 = x_432;
x_346 = x_434;
x_347 = x_7;
x_348 = lean_box(0);
goto block_349;
}
}
else
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; uint8_t x_465; 
lean_dec(x_434);
lean_dec_ref(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_453 = lean_ctor_get(x_436, 0);
x_465 = !lean_is_exclusive(x_436);
if (x_465 == 0)
{
x_454 = x_436;
x_455 = x_465;
goto block_464;
}
else
{
lean_inc(x_453);
lean_dec(x_436);
x_454 = lean_box(0);
x_455 = x_465;
goto block_464;
}
block_464:
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_456 = lean_io_error_to_string(x_453);
x_457 = 3;
x_458 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*1, x_457);
x_459 = lean_apply_2(x_7, x_458, lean_box(0));
x_460 = lean_box(0);
if (x_455 == 0)
{
lean_ctor_set(x_454, 0, x_460);
x_461 = x_454;
goto block_462;
}
else
{
lean_object* x_463; 
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_460);
x_461 = x_463;
goto block_462;
}
block_462:
{
return x_461;
}
}
}
}
block_476:
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_5, 1);
x_471 = lean_ctor_get(x_5, 18);
lean_inc_ref(x_471);
x_472 = l_Lake_ToolchainVer_ofString(x_471);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_472, 1);
lean_inc_ref(x_473);
lean_dec_ref(x_472);
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_473);
lean_inc_ref(x_470);
lean_inc_ref(x_471);
x_429 = x_467;
x_430 = x_468;
x_431 = x_471;
x_432 = x_470;
x_433 = lean_box(0);
x_434 = x_474;
goto block_466;
}
else
{
lean_object* x_475; 
lean_dec_ref(x_472);
x_475 = lean_box(0);
lean_inc_ref(x_470);
lean_inc_ref(x_471);
x_429 = x_467;
x_430 = x_468;
x_431 = x_471;
x_432 = x_470;
x_433 = lean_box(0);
x_434 = x_475;
goto block_466;
}
}
block_483:
{
if (x_479 == 0)
{
lean_object* x_481; 
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_478);
x_467 = x_477;
x_468 = x_481;
x_469 = lean_box(0);
goto block_476;
}
else
{
lean_object* x_482; 
lean_dec_ref(x_478);
x_482 = lean_box(0);
x_467 = x_477;
x_468 = x_482;
x_469 = lean_box(0);
goto block_476;
}
}
block_502:
{
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; 
lean_dec_ref(x_486);
lean_inc(x_2);
x_488 = l_Lake_toUpperCamelCase(x_2);
lean_inc(x_488);
x_489 = l_Lean_modToFilePath(x_1, x_488, x_484);
lean_dec_ref(x_484);
x_490 = l_System_FilePath_pathExists(x_489);
x_491 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_492 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_492 == 0)
{
x_477 = x_488;
x_478 = x_489;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
lean_object* x_493; uint8_t x_494; 
x_493 = lean_box(0);
x_494 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_494 == 0)
{
if (x_492 == 0)
{
x_477 = x_488;
x_478 = x_489;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
size_t x_495; size_t x_496; lean_object* x_497; 
x_495 = 0;
x_496 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_497 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_491, x_495, x_496, x_493, x_7);
if (lean_obj_tag(x_497) == 0)
{
lean_dec_ref(x_497);
x_477 = x_488;
x_478 = x_489;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
lean_dec_ref(x_489);
lean_dec(x_488);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_497;
}
}
}
else
{
size_t x_498; size_t x_499; lean_object* x_500; 
x_498 = 0;
x_499 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_500 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_491, x_498, x_499, x_493, x_7);
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
x_477 = x_488;
x_478 = x_489;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
lean_dec_ref(x_489);
lean_dec(x_488);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_500;
}
}
}
}
else
{
lean_object* x_501; 
lean_dec_ref(x_484);
x_501 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_501, 0, x_486);
lean_inc(x_2);
x_467 = x_2;
x_468 = x_501;
x_469 = lean_box(0);
goto block_476;
}
}
block_509:
{
uint8_t x_507; uint8_t x_508; 
x_507 = 1;
x_508 = l_Lake_instDecidableEqInitTemplate(x_3, x_507);
if (x_508 == 0)
{
x_484 = x_503;
x_485 = lean_box(0);
x_486 = x_504;
x_487 = x_505;
goto block_502;
}
else
{
x_484 = x_503;
x_485 = lean_box(0);
x_486 = x_504;
x_487 = x_508;
goto block_502;
}
}
block_524:
{
lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; 
x_511 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(x_2);
x_512 = l_Lean_modToFilePath(x_1, x_2, x_511);
x_513 = l_System_FilePath_pathExists(x_512);
x_514 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_515 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_515 == 0)
{
x_503 = x_511;
x_504 = x_512;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
lean_object* x_516; uint8_t x_517; 
x_516 = lean_box(0);
x_517 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_517 == 0)
{
if (x_515 == 0)
{
x_503 = x_511;
x_504 = x_512;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
size_t x_518; size_t x_519; lean_object* x_520; 
x_518 = 0;
x_519 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_520 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_514, x_518, x_519, x_516, x_7);
if (lean_obj_tag(x_520) == 0)
{
lean_dec_ref(x_520);
x_503 = x_511;
x_504 = x_512;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
lean_dec_ref(x_512);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_520;
}
}
}
else
{
size_t x_521; size_t x_522; lean_object* x_523; 
x_521 = 0;
x_522 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_523 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_514, x_521, x_522, x_516, x_7);
if (lean_obj_tag(x_523) == 0)
{
lean_dec_ref(x_523);
x_503 = x_511;
x_504 = x_512;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
lean_dec_ref(x_512);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_523;
}
}
}
}
block_526:
{
if (lean_obj_tag(x_525) == 0)
{
lean_dec_ref(x_525);
x_510 = lean_box(0);
goto block_524;
}
else
{
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_525;
}
}
block_560:
{
if (x_527 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_unsigned_to_nat(0u);
x_530 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_1);
x_531 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_1, x_3, x_530);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
lean_dec_ref(x_531);
x_533 = lean_array_get_size(x_532);
x_534 = lean_nat_dec_lt(x_529, x_533);
if (x_534 == 0)
{
lean_dec(x_532);
x_510 = lean_box(0);
goto block_524;
}
else
{
lean_object* x_535; uint8_t x_536; 
x_535 = lean_box(0);
x_536 = lean_nat_dec_le(x_533, x_533);
if (x_536 == 0)
{
if (x_534 == 0)
{
lean_dec(x_532);
x_510 = lean_box(0);
goto block_524;
}
else
{
size_t x_537; size_t x_538; lean_object* x_539; 
x_537 = 0;
x_538 = lean_usize_of_nat(x_533);
lean_inc_ref(x_7);
x_539 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_532, x_537, x_538, x_535, x_7);
lean_dec(x_532);
if (lean_obj_tag(x_539) == 0)
{
lean_dec_ref(x_539);
x_510 = lean_box(0);
goto block_524;
}
else
{
x_525 = x_539;
goto block_526;
}
}
}
else
{
size_t x_540; size_t x_541; lean_object* x_542; 
x_540 = 0;
x_541 = lean_usize_of_nat(x_533);
lean_inc_ref(x_7);
x_542 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_532, x_540, x_541, x_535, x_7);
lean_dec(x_532);
if (lean_obj_tag(x_542) == 0)
{
lean_dec_ref(x_542);
x_510 = lean_box(0);
goto block_524;
}
else
{
x_525 = x_542;
goto block_526;
}
}
}
}
else
{
lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_543 = lean_ctor_get(x_531, 1);
lean_inc(x_543);
lean_dec_ref(x_531);
x_544 = lean_array_get_size(x_543);
x_545 = lean_nat_dec_lt(x_529, x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_543);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_546 = lean_box(0);
x_547 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_547, 0, x_546);
return x_547;
}
else
{
lean_object* x_548; uint8_t x_549; 
x_548 = lean_box(0);
x_549 = lean_nat_dec_le(x_544, x_544);
if (x_549 == 0)
{
if (x_545 == 0)
{
lean_dec(x_543);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_550; size_t x_551; lean_object* x_552; 
x_550 = 0;
x_551 = lean_usize_of_nat(x_544);
lean_inc_ref(x_7);
x_552 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_543, x_550, x_551, x_548, x_7);
lean_dec(x_543);
if (lean_obj_tag(x_552) == 0)
{
lean_dec_ref(x_552);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_525 = x_552;
goto block_526;
}
}
}
else
{
size_t x_553; size_t x_554; lean_object* x_555; 
x_553 = 0;
x_554 = lean_usize_of_nat(x_544);
lean_inc_ref(x_7);
x_555 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_543, x_553, x_554, x_548, x_7);
lean_dec(x_543);
if (lean_obj_tag(x_555) == 0)
{
lean_dec_ref(x_555);
lean_dec_ref(x_428);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_525 = x_555;
goto block_526;
}
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec_ref(x_428);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_556 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
x_557 = lean_apply_2(x_7, x_556, lean_box(0));
x_558 = lean_box(0);
x_559 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_559, 0, x_558);
return x_559;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
x_10 = lean_unbox(x_4);
x_11 = lean_unbox(x_6);
x_12 = l___private_Lake_CLI_Init_0__Lake_initPkg(x_1, x_2, x_9, x_10, x_5, x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
lean_inc(x_5);
lean_inc(x_6);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_sub(x_5, x_6);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get_fast(x_3, x_6);
x_12 = 46;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_string_utf8_next_fast(x_3, x_6);
x_15 = lean_nat_sub(x_14, x_6);
lean_dec(x_6);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_15);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_2);
if (x_17 == 0)
{
lean_dec(x_16);
return x_7;
}
else
{
lean_dec_ref(x_7);
x_2 = x_16;
goto _start;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1);
x_2 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_nat_add(x_5, x_2);
lean_dec(x_2);
x_10 = lean_string_utf8_get_fast(x_4, x_9);
x_11 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0);
x_12 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2);
x_13 = lean_box_uint32(x_10);
x_14 = l_List_elem___redArg(x_11, x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_string_utf8_next_fast(x_4, x_9);
lean_dec(x_9);
x_16 = lean_nat_sub(x_15, x_5);
x_2 = x_16;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_9);
return x_14;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(x_1, x_2, x_4);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_14; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_string_utf8_byte_size(x_1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc_ref(x_1);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_30);
x_34 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(x_33, x_31);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_nat_sub(x_36, x_35);
lean_dec(x_35);
lean_dec(x_36);
x_38 = lean_nat_dec_eq(x_37, x_31);
lean_dec(x_37);
x_14 = x_38;
goto block_29;
}
else
{
x_14 = x_32;
goto block_29;
}
block_13:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0));
x_5 = lean_string_append(x_4, x_1);
lean_dec_ref(x_1);
x_6 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
x_7 = lean_string_append(x_5, x_6);
x_8 = 3;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_array_get_size(x_2);
x_11 = lean_array_push(x_2, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_29:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(x_17);
lean_dec_ref(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1, &l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1);
x_20 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_1, x_15);
x_21 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8));
x_22 = l_List_elem___redArg(x_19, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10));
x_26 = lean_array_get_size(x_2);
x_27 = lean_array_push(x_2, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
goto block_13;
}
}
else
{
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_510; lean_object* x_525; uint8_t x_527; lean_object* x_528; lean_object* x_561; uint8_t x_562; 
x_13 = l_Lake_defaultConfigFile;
x_426 = l_Lake_ConfigLang_fileExtension(x_5);
x_427 = l_System_FilePath_addExtension(x_13, x_426);
lean_dec_ref(x_426);
lean_inc_ref(x_2);
x_428 = l_Lake_joinRelative(x_2, x_427);
x_527 = l_System_FilePath_pathExists(x_428);
x_561 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_562 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_562 == 0)
{
x_528 = lean_box(0);
goto block_560;
}
else
{
lean_object* x_563; uint8_t x_564; 
x_563 = lean_box(0);
x_564 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_564 == 0)
{
if (x_562 == 0)
{
x_528 = lean_box(0);
goto block_560;
}
else
{
size_t x_565; size_t x_566; lean_object* x_567; 
x_565 = 0;
x_566 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_567 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_561, x_565, x_566, x_563, x_1);
if (lean_obj_tag(x_567) == 0)
{
lean_dec_ref(x_567);
x_528 = lean_box(0);
goto block_560;
}
else
{
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_567;
}
}
}
else
{
size_t x_568; size_t x_569; lean_object* x_570; 
x_568 = 0;
x_569 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_570 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_561, x_568, x_569, x_563, x_1);
if (lean_obj_tag(x_570) == 0)
{
lean_dec_ref(x_570);
x_528 = lean_box(0);
goto block_560;
}
else
{
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_570;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_31:
{
if (x_7 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_box(0);
x_19 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(x_2);
x_20 = l_Lake_joinRelative(x_2, x_19);
lean_inc_ref(x_20);
x_21 = l_Lake_joinRelative(x_20, x_13);
x_22 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
x_23 = lean_box(1);
x_24 = l_Lean_Options_empty;
x_25 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
x_26 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_2);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_19);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_13);
lean_ctor_set(x_26, 8, x_21);
lean_ctor_set(x_26, 9, x_22);
lean_ctor_set(x_26, 10, x_23);
lean_ctor_set(x_26, 11, x_24);
lean_ctor_set(x_26, 12, x_25);
lean_ctor_set(x_26, 13, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*14, x_7);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 1, x_7);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 2, x_7);
x_27 = l_Lean_NameSet_empty;
x_28 = l_Lake_updateManifest(x_26, x_27, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_14);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
block_37:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(x_33);
x_36 = lean_apply_2(x_33, x_35, lean_box(0));
x_14 = x_33;
x_15 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_32);
x_14 = x_33;
x_15 = lean_box(0);
goto block_31;
}
}
block_43:
{
switch (x_4) {
case 3:
{
x_32 = x_38;
x_33 = x_39;
x_34 = lean_box(0);
goto block_37;
}
case 4:
{
x_32 = x_38;
x_33 = x_39;
x_34 = lean_box(0);
goto block_37;
}
default: 
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
block_50:
{
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(x_45);
x_49 = lean_apply_2(x_45, x_48, lean_box(0));
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
else
{
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
}
block_124:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(x_2);
x_57 = l_Lake_joinRelative(x_2, x_56);
x_58 = 4;
x_59 = lean_io_prim_handle_mk(x_57, x_58);
lean_dec_ref(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_62 = lean_io_prim_handle_put_str(x_60, x_61);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec_ref(x_62);
x_63 = l_Lake_toolchainFileName;
lean_inc_ref(x_2);
x_64 = l_Lake_joinRelative(x_2, x_63);
x_65 = lean_string_utf8_byte_size(x_53);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_52);
x_68 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_69 = lean_string_append(x_53, x_68);
x_70 = l_IO_FS_writeFile(x_64, x_69);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_38 = x_51;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_83; 
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_70, 0);
x_83 = !lean_is_exclusive(x_70);
if (x_83 == 0)
{
x_72 = x_70;
x_73 = x_83;
goto block_82;
}
else
{
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_io_error_to_string(x_71);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_apply_2(x_54, x_76, lean_box(0));
x_78 = lean_box(0);
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_78);
x_79 = x_72;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_78);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec_ref(x_53);
x_84 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_84);
lean_dec_ref(x_52);
x_85 = lean_string_utf8_byte_size(x_84);
lean_dec_ref(x_84);
x_86 = lean_nat_dec_eq(x_85, x_66);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_System_FilePath_pathExists(x_64);
lean_dec_ref(x_64);
x_88 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_89 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_89 == 0)
{
x_44 = x_51;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_box(0);
x_91 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_91 == 0)
{
if (x_89 == 0)
{
x_44 = x_51;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; 
x_92 = 0;
x_93 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_54);
x_94 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_88, x_92, x_93, x_90, x_54);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
x_44 = x_51;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_94;
}
}
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; 
x_95 = 0;
x_96 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_54);
x_97 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_88, x_95, x_96, x_90, x_54);
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_97);
x_44 = x_51;
x_45 = x_54;
x_46 = x_87;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_97;
}
}
}
}
else
{
lean_dec_ref(x_64);
x_38 = x_51;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_110; 
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_98 = lean_ctor_get(x_62, 0);
x_110 = !lean_is_exclusive(x_62);
if (x_110 == 0)
{
x_99 = x_62;
x_100 = x_110;
goto block_109;
}
else
{
lean_inc(x_98);
lean_dec(x_62);
x_99 = lean_box(0);
x_100 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_io_error_to_string(x_98);
x_102 = 3;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = lean_apply_2(x_54, x_103, lean_box(0));
x_105 = lean_box(0);
if (x_100 == 0)
{
lean_ctor_set(x_99, 0, x_105);
x_106 = x_99;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_123; 
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_111 = lean_ctor_get(x_59, 0);
x_123 = !lean_is_exclusive(x_59);
if (x_123 == 0)
{
x_112 = x_59;
x_113 = x_123;
goto block_122;
}
else
{
lean_inc(x_111);
lean_dec(x_59);
x_112 = lean_box(0);
x_113 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_io_error_to_string(x_111);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_apply_2(x_54, x_116, lean_box(0));
x_118 = lean_box(0);
if (x_113 == 0)
{
lean_ctor_set(x_112, 0, x_118);
x_119 = x_112;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(x_126);
x_131 = lean_apply_2(x_126, x_130, lean_box(0));
x_51 = x_125;
x_52 = x_128;
x_53 = x_127;
x_54 = x_126;
x_55 = lean_box(0);
goto block_124;
}
block_138:
{
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_51 = x_133;
x_52 = x_136;
x_53 = x_135;
x_54 = x_134;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_dec_ref(x_137);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
}
block_171:
{
lean_object* x_144; uint8_t x_145; 
x_144 = l_Lake_Git_upstreamBranch;
x_145 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_2);
x_148 = l_Lake_GitRepo_checkoutBranch(x_144, x_2, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_array_get_size(x_149);
x_151 = lean_nat_dec_lt(x_146, x_150);
if (x_151 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_142;
x_53 = x_141;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_box(0);
x_153 = lean_nat_dec_le(x_150, x_150);
if (x_153 == 0)
{
if (x_151 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_142;
x_53 = x_141;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
size_t x_154; size_t x_155; lean_object* x_156; 
x_154 = 0;
x_155 = lean_usize_of_nat(x_150);
lean_inc_ref(x_140);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_149, x_154, x_155, x_152, x_140);
lean_dec(x_149);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
x_51 = x_139;
x_52 = x_142;
x_53 = x_141;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_156;
goto block_138;
}
}
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_150);
lean_inc_ref(x_140);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_149, x_157, x_158, x_152, x_140);
lean_dec(x_149);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
x_51 = x_139;
x_52 = x_142;
x_53 = x_141;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_159;
goto block_138;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_148, 1);
lean_inc(x_160);
lean_dec_ref(x_148);
x_161 = lean_array_get_size(x_160);
x_162 = lean_nat_dec_lt(x_146, x_161);
if (x_162 == 0)
{
lean_dec(x_160);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_box(0);
x_164 = lean_nat_dec_le(x_161, x_161);
if (x_164 == 0)
{
if (x_162 == 0)
{
lean_dec(x_160);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
size_t x_165; size_t x_166; lean_object* x_167; 
x_165 = 0;
x_166 = lean_usize_of_nat(x_161);
lean_inc_ref(x_140);
x_167 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_160, x_165, x_166, x_163, x_140);
lean_dec(x_160);
if (lean_obj_tag(x_167) == 0)
{
lean_dec_ref(x_167);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_167;
goto block_138;
}
}
}
else
{
size_t x_168; size_t x_169; lean_object* x_170; 
x_168 = 0;
x_169 = lean_usize_of_nat(x_161);
lean_inc_ref(x_140);
x_170 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_160, x_168, x_169, x_163, x_140);
lean_dec(x_160);
if (lean_obj_tag(x_170) == 0)
{
lean_dec_ref(x_170);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_170;
goto block_138;
}
}
}
}
}
else
{
x_51 = x_139;
x_52 = x_142;
x_53 = x_141;
x_54 = x_140;
x_55 = lean_box(0);
goto block_124;
}
}
block_177:
{
if (lean_obj_tag(x_176) == 0)
{
lean_dec_ref(x_176);
x_139 = x_173;
x_140 = x_172;
x_141 = x_175;
x_142 = x_174;
x_143 = lean_box(0);
goto block_171;
}
else
{
lean_dec_ref(x_176);
x_125 = x_173;
x_126 = x_172;
x_127 = x_175;
x_128 = x_174;
x_129 = lean_box(0);
goto block_132;
}
}
block_209:
{
if (x_182 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_unsigned_to_nat(0u);
x_185 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_2);
x_186 = l_Lake_GitRepo_quietInit(x_2, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = lean_array_get_size(x_187);
x_189 = lean_nat_dec_lt(x_184, x_188);
if (x_189 == 0)
{
lean_dec(x_187);
x_139 = x_179;
x_140 = x_178;
x_141 = x_181;
x_142 = x_180;
x_143 = lean_box(0);
goto block_171;
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_box(0);
x_191 = lean_nat_dec_le(x_188, x_188);
if (x_191 == 0)
{
if (x_189 == 0)
{
lean_dec(x_187);
x_139 = x_179;
x_140 = x_178;
x_141 = x_181;
x_142 = x_180;
x_143 = lean_box(0);
goto block_171;
}
else
{
size_t x_192; size_t x_193; lean_object* x_194; 
x_192 = 0;
x_193 = lean_usize_of_nat(x_188);
lean_inc_ref(x_178);
x_194 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_187, x_192, x_193, x_190, x_178);
lean_dec(x_187);
if (lean_obj_tag(x_194) == 0)
{
lean_dec_ref(x_194);
x_139 = x_179;
x_140 = x_178;
x_141 = x_181;
x_142 = x_180;
x_143 = lean_box(0);
goto block_171;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_194;
goto block_177;
}
}
}
else
{
size_t x_195; size_t x_196; lean_object* x_197; 
x_195 = 0;
x_196 = lean_usize_of_nat(x_188);
lean_inc_ref(x_178);
x_197 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_187, x_195, x_196, x_190, x_178);
lean_dec(x_187);
if (lean_obj_tag(x_197) == 0)
{
lean_dec_ref(x_197);
x_139 = x_179;
x_140 = x_178;
x_141 = x_181;
x_142 = x_180;
x_143 = lean_box(0);
goto block_171;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_197;
goto block_177;
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_ctor_get(x_186, 1);
lean_inc(x_198);
lean_dec_ref(x_186);
x_199 = lean_array_get_size(x_198);
x_200 = lean_nat_dec_lt(x_184, x_199);
if (x_200 == 0)
{
lean_dec(x_198);
x_125 = x_179;
x_126 = x_178;
x_127 = x_181;
x_128 = x_180;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_box(0);
x_202 = lean_nat_dec_le(x_199, x_199);
if (x_202 == 0)
{
if (x_200 == 0)
{
lean_dec(x_198);
x_125 = x_179;
x_126 = x_178;
x_127 = x_181;
x_128 = x_180;
x_129 = lean_box(0);
goto block_132;
}
else
{
size_t x_203; size_t x_204; lean_object* x_205; 
x_203 = 0;
x_204 = lean_usize_of_nat(x_199);
lean_inc_ref(x_178);
x_205 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_198, x_203, x_204, x_201, x_178);
lean_dec(x_198);
if (lean_obj_tag(x_205) == 0)
{
lean_dec_ref(x_205);
x_125 = x_179;
x_126 = x_178;
x_127 = x_181;
x_128 = x_180;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_205;
goto block_177;
}
}
}
else
{
size_t x_206; size_t x_207; lean_object* x_208; 
x_206 = 0;
x_207 = lean_usize_of_nat(x_199);
lean_inc_ref(x_178);
x_208 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_198, x_206, x_207, x_201, x_178);
lean_dec(x_198);
if (lean_obj_tag(x_208) == 0)
{
lean_dec_ref(x_208);
x_125 = x_179;
x_126 = x_178;
x_127 = x_181;
x_128 = x_180;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_172 = x_178;
x_173 = x_179;
x_174 = x_180;
x_175 = x_181;
x_176 = x_208;
goto block_177;
}
}
}
}
}
else
{
x_51 = x_179;
x_52 = x_180;
x_53 = x_181;
x_54 = x_178;
x_55 = lean_box(0);
goto block_124;
}
}
block_226:
{
uint8_t x_215; lean_object* x_216; uint8_t x_217; 
lean_inc_ref(x_2);
x_215 = l_Lake_GitRepo_insideWorkTree(x_2);
x_216 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_217 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_217 == 0)
{
x_178 = x_213;
x_179 = x_210;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_box(0);
x_219 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_219 == 0)
{
if (x_217 == 0)
{
x_178 = x_213;
x_179 = x_210;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
size_t x_220; size_t x_221; lean_object* x_222; 
x_220 = 0;
x_221 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_213);
x_222 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_216, x_220, x_221, x_218, x_213);
if (lean_obj_tag(x_222) == 0)
{
lean_dec_ref(x_222);
x_178 = x_213;
x_179 = x_210;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_222;
}
}
}
else
{
size_t x_223; size_t x_224; lean_object* x_225; 
x_223 = 0;
x_224 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_213);
x_225 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_216, x_223, x_224, x_218, x_213);
if (lean_obj_tag(x_225) == 0)
{
lean_dec_ref(x_225);
x_178 = x_213;
x_179 = x_210;
x_180 = x_211;
x_181 = x_212;
x_182 = x_215;
x_183 = lean_box(0);
goto block_209;
}
else
{
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_225;
}
}
}
}
block_248:
{
lean_object* x_234; 
x_234 = l_IO_FS_writeFile(x_232, x_233);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
if (lean_obj_tag(x_234) == 0)
{
lean_dec_ref(x_234);
x_210 = x_228;
x_211 = x_230;
x_212 = x_229;
x_213 = x_231;
x_214 = lean_box(0);
goto block_226;
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_247; 
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_235 = lean_ctor_get(x_234, 0);
x_247 = !lean_is_exclusive(x_234);
if (x_247 == 0)
{
x_236 = x_234;
x_237 = x_247;
goto block_246;
}
else
{
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_box(0);
x_237 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_238 = lean_io_error_to_string(x_235);
x_239 = 3;
x_240 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*1, x_239);
x_241 = lean_apply_2(x_231, x_240, lean_box(0));
x_242 = lean_box(0);
if (x_237 == 0)
{
lean_ctor_set(x_236, 0, x_242);
x_243 = x_236;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_242);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
block_262:
{
if (x_254 == 0)
{
uint8_t x_256; uint8_t x_257; 
x_256 = 4;
x_257 = l_Lake_instDecidableEqInitTemplate(x_4, x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_259 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_258);
lean_dec_ref(x_258);
x_227 = lean_box(0);
x_228 = x_249;
x_229 = x_251;
x_230 = x_250;
x_231 = x_253;
x_232 = x_252;
x_233 = x_259;
goto block_248;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_261 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_260);
lean_dec_ref(x_260);
x_227 = lean_box(0);
x_228 = x_249;
x_229 = x_251;
x_230 = x_250;
x_231 = x_253;
x_232 = x_252;
x_233 = x_261;
goto block_248;
}
}
else
{
lean_dec_ref(x_252);
lean_dec(x_3);
x_210 = x_249;
x_211 = x_250;
x_212 = x_251;
x_213 = x_253;
x_214 = lean_box(0);
goto block_226;
}
}
block_281:
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; uint8_t x_272; 
x_268 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(x_2);
x_269 = l_Lake_joinRelative(x_2, x_268);
x_270 = l_System_FilePath_pathExists(x_269);
x_271 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_272 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_272 == 0)
{
x_249 = x_263;
x_250 = x_265;
x_251 = x_264;
x_252 = x_269;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_box(0);
x_274 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_274 == 0)
{
if (x_272 == 0)
{
x_249 = x_263;
x_250 = x_265;
x_251 = x_264;
x_252 = x_269;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
size_t x_275; size_t x_276; lean_object* x_277; 
x_275 = 0;
x_276 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_266);
x_277 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_271, x_275, x_276, x_273, x_266);
if (lean_obj_tag(x_277) == 0)
{
lean_dec_ref(x_277);
x_249 = x_263;
x_250 = x_265;
x_251 = x_264;
x_252 = x_269;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
lean_dec_ref(x_269);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_277;
}
}
}
else
{
size_t x_278; size_t x_279; lean_object* x_280; 
x_278 = 0;
x_279 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_266);
x_280 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_271, x_278, x_279, x_273, x_266);
if (lean_obj_tag(x_280) == 0)
{
lean_dec_ref(x_280);
x_249 = x_263;
x_250 = x_265;
x_251 = x_264;
x_252 = x_269;
x_253 = x_266;
x_254 = x_270;
x_255 = lean_box(0);
goto block_262;
}
else
{
lean_dec_ref(x_269);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_280;
}
}
}
}
block_322:
{
if (x_288 == 0)
{
uint8_t x_290; uint8_t x_291; 
x_290 = 1;
x_291 = l_Lake_instDecidableEqInitTemplate(x_4, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_286);
x_293 = l_IO_FS_writeFile(x_287, x_292);
lean_dec_ref(x_292);
lean_dec_ref(x_287);
if (lean_obj_tag(x_293) == 0)
{
lean_dec_ref(x_293);
x_263 = x_282;
x_264 = x_284;
x_265 = x_283;
x_266 = x_285;
x_267 = lean_box(0);
goto block_281;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_306; 
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_294 = lean_ctor_get(x_293, 0);
x_306 = !lean_is_exclusive(x_293);
if (x_306 == 0)
{
x_295 = x_293;
x_296 = x_306;
goto block_305;
}
else
{
lean_inc(x_294);
lean_dec(x_293);
x_295 = lean_box(0);
x_296 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_297 = lean_io_error_to_string(x_294);
x_298 = 3;
x_299 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*1, x_298);
x_300 = lean_apply_2(x_285, x_299, lean_box(0));
x_301 = lean_box(0);
if (x_296 == 0)
{
lean_ctor_set(x_295, 0, x_301);
x_302 = x_295;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_301);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_286);
x_307 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
x_308 = l_IO_FS_writeFile(x_287, x_307);
lean_dec_ref(x_287);
if (lean_obj_tag(x_308) == 0)
{
lean_dec_ref(x_308);
x_263 = x_282;
x_264 = x_284;
x_265 = x_283;
x_266 = x_285;
x_267 = lean_box(0);
goto block_281;
}
else
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; uint8_t x_321; 
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_309 = lean_ctor_get(x_308, 0);
x_321 = !lean_is_exclusive(x_308);
if (x_321 == 0)
{
x_310 = x_308;
x_311 = x_321;
goto block_320;
}
else
{
lean_inc(x_309);
lean_dec(x_308);
x_310 = lean_box(0);
x_311 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_io_error_to_string(x_309);
x_313 = 3;
x_314 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set_uint8(x_314, sizeof(void*)*1, x_313);
x_315 = lean_apply_2(x_285, x_314, lean_box(0));
x_316 = lean_box(0);
if (x_311 == 0)
{
lean_ctor_set(x_310, 0, x_316);
x_317 = x_310;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_316);
x_317 = x_319;
goto block_318;
}
block_318:
{
return x_317;
}
}
}
}
}
else
{
lean_dec_ref(x_287);
lean_dec(x_286);
x_263 = x_282;
x_264 = x_284;
x_265 = x_283;
x_266 = x_285;
x_267 = lean_box(0);
goto block_281;
}
}
block_342:
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; 
x_329 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_2);
x_330 = l_Lake_joinRelative(x_2, x_329);
x_331 = l_System_FilePath_pathExists(x_330);
x_332 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_333 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_333 == 0)
{
x_282 = x_324;
x_283 = x_326;
x_284 = x_325;
x_285 = x_327;
x_286 = x_328;
x_287 = x_330;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_box(0);
x_335 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_335 == 0)
{
if (x_333 == 0)
{
x_282 = x_324;
x_283 = x_326;
x_284 = x_325;
x_285 = x_327;
x_286 = x_328;
x_287 = x_330;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
size_t x_336; size_t x_337; lean_object* x_338; 
x_336 = 0;
x_337 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_327);
x_338 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_332, x_336, x_337, x_334, x_327);
if (lean_obj_tag(x_338) == 0)
{
lean_dec_ref(x_338);
x_282 = x_324;
x_283 = x_326;
x_284 = x_325;
x_285 = x_327;
x_286 = x_328;
x_287 = x_330;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
lean_dec_ref(x_330);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_338;
}
}
}
else
{
size_t x_339; size_t x_340; lean_object* x_341; 
x_339 = 0;
x_340 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_327);
x_341 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_332, x_339, x_340, x_334, x_327);
if (lean_obj_tag(x_341) == 0)
{
lean_dec_ref(x_341);
x_282 = x_324;
x_283 = x_326;
x_284 = x_325;
x_285 = x_327;
x_286 = x_328;
x_287 = x_330;
x_288 = x_331;
x_289 = lean_box(0);
goto block_322;
}
else
{
lean_dec_ref(x_330);
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_341;
}
}
}
}
block_349:
{
switch (x_4) {
case 0:
{
x_323 = lean_box(0);
x_324 = x_343;
x_325 = x_345;
x_326 = x_344;
x_327 = x_347;
x_328 = x_346;
goto block_342;
}
case 1:
{
x_323 = lean_box(0);
x_324 = x_343;
x_325 = x_345;
x_326 = x_344;
x_327 = x_347;
x_328 = x_346;
goto block_342;
}
default: 
{
lean_dec(x_346);
x_263 = x_343;
x_264 = x_345;
x_265 = x_344;
x_266 = x_347;
x_267 = lean_box(0);
goto block_281;
}
}
}
block_372:
{
lean_object* x_358; 
x_358 = l_IO_FS_writeFile(x_354, x_357);
lean_dec_ref(x_357);
lean_dec_ref(x_354);
if (lean_obj_tag(x_358) == 0)
{
lean_dec_ref(x_358);
x_343 = x_350;
x_344 = x_352;
x_345 = x_351;
x_346 = x_356;
x_347 = x_353;
x_348 = lean_box(0);
goto block_349;
}
else
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; uint8_t x_371; 
lean_dec(x_356);
lean_dec_ref(x_352);
lean_dec_ref(x_351);
lean_dec(x_350);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_359 = lean_ctor_get(x_358, 0);
x_371 = !lean_is_exclusive(x_358);
if (x_371 == 0)
{
x_360 = x_358;
x_361 = x_371;
goto block_370;
}
else
{
lean_inc(x_359);
lean_dec(x_358);
x_360 = lean_box(0);
x_361 = x_371;
goto block_370;
}
block_370:
{
lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_362 = lean_io_error_to_string(x_359);
x_363 = 3;
x_364 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*1, x_363);
x_365 = lean_apply_2(x_353, x_364, lean_box(0));
x_366 = lean_box(0);
if (x_361 == 0)
{
lean_ctor_set(x_360, 0, x_366);
x_367 = x_360;
goto block_368;
}
else
{
lean_object* x_369; 
x_369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_369, 0, x_366);
x_367 = x_369;
goto block_368;
}
block_368:
{
return x_367;
}
}
}
}
block_386:
{
uint8_t x_380; uint8_t x_381; 
x_380 = 4;
x_381 = l_Lake_instDecidableEqInitTemplate(x_4, x_380);
if (x_381 == 0)
{
uint8_t x_382; lean_object* x_383; lean_object* x_384; 
x_382 = 1;
lean_inc(x_377);
x_383 = l_Lean_Name_toString(x_377, x_382);
lean_inc(x_377);
x_384 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_383, x_377);
lean_dec_ref(x_383);
x_350 = x_373;
x_351 = x_375;
x_352 = x_374;
x_353 = x_378;
x_354 = x_376;
x_355 = lean_box(0);
x_356 = x_377;
x_357 = x_384;
goto block_372;
}
else
{
lean_object* x_385; 
lean_inc(x_377);
x_385 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_377);
x_350 = x_373;
x_351 = x_375;
x_352 = x_374;
x_353 = x_378;
x_354 = x_376;
x_355 = lean_box(0);
x_356 = x_377;
x_357 = x_385;
goto block_372;
}
}
block_425:
{
if (x_394 == 0)
{
lean_object* x_396; 
x_396 = l_IO_FS_createDirAll(x_387);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; 
lean_dec_ref(x_396);
x_397 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
x_398 = l_IO_FS_writeFile(x_391, x_397);
lean_dec_ref(x_391);
if (lean_obj_tag(x_398) == 0)
{
lean_dec_ref(x_398);
x_373 = x_388;
x_374 = x_390;
x_375 = x_389;
x_376 = x_392;
x_377 = x_393;
x_378 = x_1;
x_379 = lean_box(0);
goto block_386;
}
else
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; uint8_t x_411; 
lean_dec(x_393);
lean_dec_ref(x_392);
lean_dec_ref(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_399 = lean_ctor_get(x_398, 0);
x_411 = !lean_is_exclusive(x_398);
if (x_411 == 0)
{
x_400 = x_398;
x_401 = x_411;
goto block_410;
}
else
{
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_box(0);
x_401 = x_411;
goto block_410;
}
block_410:
{
lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_402 = lean_io_error_to_string(x_399);
x_403 = 3;
x_404 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set_uint8(x_404, sizeof(void*)*1, x_403);
x_405 = lean_apply_2(x_1, x_404, lean_box(0));
x_406 = lean_box(0);
if (x_401 == 0)
{
lean_ctor_set(x_400, 0, x_406);
x_407 = x_400;
goto block_408;
}
else
{
lean_object* x_409; 
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_406);
x_407 = x_409;
goto block_408;
}
block_408:
{
return x_407;
}
}
}
}
else
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; uint8_t x_424; 
lean_dec(x_393);
lean_dec_ref(x_392);
lean_dec_ref(x_391);
lean_dec_ref(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_412 = lean_ctor_get(x_396, 0);
x_424 = !lean_is_exclusive(x_396);
if (x_424 == 0)
{
x_413 = x_396;
x_414 = x_424;
goto block_423;
}
else
{
lean_inc(x_412);
lean_dec(x_396);
x_413 = lean_box(0);
x_414 = x_424;
goto block_423;
}
block_423:
{
lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_415 = lean_io_error_to_string(x_412);
x_416 = 3;
x_417 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*1, x_416);
x_418 = lean_apply_2(x_1, x_417, lean_box(0));
x_419 = lean_box(0);
if (x_414 == 0)
{
lean_ctor_set(x_413, 0, x_419);
x_420 = x_413;
goto block_421;
}
else
{
lean_object* x_422; 
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_419);
x_420 = x_422;
goto block_421;
}
block_421:
{
return x_420;
}
}
}
}
else
{
lean_dec_ref(x_391);
lean_dec_ref(x_387);
x_373 = x_388;
x_374 = x_390;
x_375 = x_389;
x_376 = x_392;
x_377 = x_393;
x_378 = x_1;
x_379 = lean_box(0);
goto block_386;
}
}
block_466:
{
lean_object* x_435; lean_object* x_436; 
lean_inc(x_434);
lean_inc(x_432);
lean_inc(x_3);
x_435 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_4, x_5, x_3, x_432, x_434);
x_436 = l_IO_FS_writeFile(x_428, x_435);
lean_dec_ref(x_435);
lean_dec_ref(x_428);
if (lean_obj_tag(x_436) == 0)
{
lean_dec_ref(x_436);
if (lean_obj_tag(x_433) == 1)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; uint8_t x_444; 
x_437 = lean_ctor_get(x_433, 0);
lean_inc(x_437);
lean_dec_ref(x_433);
x_438 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
lean_inc(x_437);
x_439 = l_System_FilePath_withExtension(x_437, x_438);
x_440 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(x_439);
x_441 = l_Lake_joinRelative(x_439, x_440);
x_442 = l_System_FilePath_pathExists(x_441);
x_443 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_444 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_444 == 0)
{
x_387 = x_439;
x_388 = x_434;
x_389 = x_429;
x_390 = x_430;
x_391 = x_441;
x_392 = x_437;
x_393 = x_432;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_445; uint8_t x_446; 
x_445 = lean_box(0);
x_446 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_446 == 0)
{
if (x_444 == 0)
{
x_387 = x_439;
x_388 = x_434;
x_389 = x_429;
x_390 = x_430;
x_391 = x_441;
x_392 = x_437;
x_393 = x_432;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
size_t x_447; size_t x_448; lean_object* x_449; 
x_447 = 0;
x_448 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_449 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_443, x_447, x_448, x_445, x_1);
if (lean_obj_tag(x_449) == 0)
{
lean_dec_ref(x_449);
x_387 = x_439;
x_388 = x_434;
x_389 = x_429;
x_390 = x_430;
x_391 = x_441;
x_392 = x_437;
x_393 = x_432;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
lean_dec_ref(x_441);
lean_dec_ref(x_439);
lean_dec(x_437);
lean_dec(x_434);
lean_dec(x_432);
lean_dec_ref(x_430);
lean_dec_ref(x_429);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_449;
}
}
}
else
{
size_t x_450; size_t x_451; lean_object* x_452; 
x_450 = 0;
x_451 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_452 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_443, x_450, x_451, x_445, x_1);
if (lean_obj_tag(x_452) == 0)
{
lean_dec_ref(x_452);
x_387 = x_439;
x_388 = x_434;
x_389 = x_429;
x_390 = x_430;
x_391 = x_441;
x_392 = x_437;
x_393 = x_432;
x_394 = x_442;
x_395 = lean_box(0);
goto block_425;
}
else
{
lean_dec_ref(x_441);
lean_dec_ref(x_439);
lean_dec(x_437);
lean_dec(x_434);
lean_dec(x_432);
lean_dec_ref(x_430);
lean_dec_ref(x_429);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_452;
}
}
}
}
else
{
lean_dec(x_433);
x_343 = x_434;
x_344 = x_430;
x_345 = x_429;
x_346 = x_432;
x_347 = x_1;
x_348 = lean_box(0);
goto block_349;
}
}
else
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; uint8_t x_465; 
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_432);
lean_dec_ref(x_430);
lean_dec_ref(x_429);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_453 = lean_ctor_get(x_436, 0);
x_465 = !lean_is_exclusive(x_436);
if (x_465 == 0)
{
x_454 = x_436;
x_455 = x_465;
goto block_464;
}
else
{
lean_inc(x_453);
lean_dec(x_436);
x_454 = lean_box(0);
x_455 = x_465;
goto block_464;
}
block_464:
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_456 = lean_io_error_to_string(x_453);
x_457 = 3;
x_458 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*1, x_457);
x_459 = lean_apply_2(x_1, x_458, lean_box(0));
x_460 = lean_box(0);
if (x_455 == 0)
{
lean_ctor_set(x_454, 0, x_460);
x_461 = x_454;
goto block_462;
}
else
{
lean_object* x_463; 
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_460);
x_461 = x_463;
goto block_462;
}
block_462:
{
return x_461;
}
}
}
}
block_476:
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_6, 1);
x_471 = lean_ctor_get(x_6, 18);
lean_inc_ref(x_471);
x_472 = l_Lake_ToolchainVer_ofString(x_471);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_472, 1);
lean_inc_ref(x_473);
lean_dec_ref(x_472);
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_473);
lean_inc_ref(x_470);
lean_inc_ref(x_471);
x_429 = x_471;
x_430 = x_470;
x_431 = lean_box(0);
x_432 = x_467;
x_433 = x_468;
x_434 = x_474;
goto block_466;
}
else
{
lean_object* x_475; 
lean_dec_ref(x_472);
x_475 = lean_box(0);
lean_inc_ref(x_470);
lean_inc_ref(x_471);
x_429 = x_471;
x_430 = x_470;
x_431 = lean_box(0);
x_432 = x_467;
x_433 = x_468;
x_434 = x_475;
goto block_466;
}
}
block_483:
{
if (x_479 == 0)
{
lean_object* x_481; 
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_477);
x_467 = x_478;
x_468 = x_481;
x_469 = lean_box(0);
goto block_476;
}
else
{
lean_object* x_482; 
lean_dec_ref(x_477);
x_482 = lean_box(0);
x_467 = x_478;
x_468 = x_482;
x_469 = lean_box(0);
goto block_476;
}
}
block_502:
{
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; 
lean_dec_ref(x_484);
lean_inc(x_3);
x_488 = l_Lake_toUpperCamelCase(x_3);
lean_inc(x_488);
x_489 = l_Lean_modToFilePath(x_2, x_488, x_486);
lean_dec_ref(x_486);
x_490 = l_System_FilePath_pathExists(x_489);
x_491 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_492 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_492 == 0)
{
x_477 = x_489;
x_478 = x_488;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
lean_object* x_493; uint8_t x_494; 
x_493 = lean_box(0);
x_494 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_494 == 0)
{
if (x_492 == 0)
{
x_477 = x_489;
x_478 = x_488;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
size_t x_495; size_t x_496; lean_object* x_497; 
x_495 = 0;
x_496 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_497 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_491, x_495, x_496, x_493, x_1);
if (lean_obj_tag(x_497) == 0)
{
lean_dec_ref(x_497);
x_477 = x_489;
x_478 = x_488;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
lean_dec_ref(x_489);
lean_dec(x_488);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_497;
}
}
}
else
{
size_t x_498; size_t x_499; lean_object* x_500; 
x_498 = 0;
x_499 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_500 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_491, x_498, x_499, x_493, x_1);
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
x_477 = x_489;
x_478 = x_488;
x_479 = x_490;
x_480 = lean_box(0);
goto block_483;
}
else
{
lean_dec_ref(x_489);
lean_dec(x_488);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_500;
}
}
}
}
else
{
lean_object* x_501; 
lean_dec_ref(x_486);
x_501 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_501, 0, x_484);
lean_inc(x_3);
x_467 = x_3;
x_468 = x_501;
x_469 = lean_box(0);
goto block_476;
}
}
block_509:
{
uint8_t x_507; uint8_t x_508; 
x_507 = 1;
x_508 = l_Lake_instDecidableEqInitTemplate(x_4, x_507);
if (x_508 == 0)
{
x_484 = x_503;
x_485 = lean_box(0);
x_486 = x_504;
x_487 = x_505;
goto block_502;
}
else
{
x_484 = x_503;
x_485 = lean_box(0);
x_486 = x_504;
x_487 = x_508;
goto block_502;
}
}
block_524:
{
lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; 
x_511 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(x_3);
x_512 = l_Lean_modToFilePath(x_2, x_3, x_511);
x_513 = l_System_FilePath_pathExists(x_512);
x_514 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_515 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_515 == 0)
{
x_503 = x_512;
x_504 = x_511;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
lean_object* x_516; uint8_t x_517; 
x_516 = lean_box(0);
x_517 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_517 == 0)
{
if (x_515 == 0)
{
x_503 = x_512;
x_504 = x_511;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
size_t x_518; size_t x_519; lean_object* x_520; 
x_518 = 0;
x_519 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_520 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_514, x_518, x_519, x_516, x_1);
if (lean_obj_tag(x_520) == 0)
{
lean_dec_ref(x_520);
x_503 = x_512;
x_504 = x_511;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
lean_dec_ref(x_512);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_520;
}
}
}
else
{
size_t x_521; size_t x_522; lean_object* x_523; 
x_521 = 0;
x_522 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_523 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_514, x_521, x_522, x_516, x_1);
if (lean_obj_tag(x_523) == 0)
{
lean_dec_ref(x_523);
x_503 = x_512;
x_504 = x_511;
x_505 = x_513;
x_506 = lean_box(0);
goto block_509;
}
else
{
lean_dec_ref(x_512);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_523;
}
}
}
}
block_526:
{
if (lean_obj_tag(x_525) == 0)
{
lean_dec_ref(x_525);
x_510 = lean_box(0);
goto block_524;
}
else
{
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_525;
}
}
block_560:
{
if (x_527 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_unsigned_to_nat(0u);
x_530 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_2);
x_531 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_2, x_4, x_530);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
lean_dec_ref(x_531);
x_533 = lean_array_get_size(x_532);
x_534 = lean_nat_dec_lt(x_529, x_533);
if (x_534 == 0)
{
lean_dec(x_532);
x_510 = lean_box(0);
goto block_524;
}
else
{
lean_object* x_535; uint8_t x_536; 
x_535 = lean_box(0);
x_536 = lean_nat_dec_le(x_533, x_533);
if (x_536 == 0)
{
if (x_534 == 0)
{
lean_dec(x_532);
x_510 = lean_box(0);
goto block_524;
}
else
{
size_t x_537; size_t x_538; lean_object* x_539; 
x_537 = 0;
x_538 = lean_usize_of_nat(x_533);
lean_inc_ref(x_1);
x_539 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_532, x_537, x_538, x_535, x_1);
lean_dec(x_532);
if (lean_obj_tag(x_539) == 0)
{
lean_dec_ref(x_539);
x_510 = lean_box(0);
goto block_524;
}
else
{
x_525 = x_539;
goto block_526;
}
}
}
else
{
size_t x_540; size_t x_541; lean_object* x_542; 
x_540 = 0;
x_541 = lean_usize_of_nat(x_533);
lean_inc_ref(x_1);
x_542 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_532, x_540, x_541, x_535, x_1);
lean_dec(x_532);
if (lean_obj_tag(x_542) == 0)
{
lean_dec_ref(x_542);
x_510 = lean_box(0);
goto block_524;
}
else
{
x_525 = x_542;
goto block_526;
}
}
}
}
else
{
lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_543 = lean_ctor_get(x_531, 1);
lean_inc(x_543);
lean_dec_ref(x_531);
x_544 = lean_array_get_size(x_543);
x_545 = lean_nat_dec_lt(x_529, x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_543);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_546 = lean_box(0);
x_547 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_547, 0, x_546);
return x_547;
}
else
{
lean_object* x_548; uint8_t x_549; 
x_548 = lean_box(0);
x_549 = lean_nat_dec_le(x_544, x_544);
if (x_549 == 0)
{
if (x_545 == 0)
{
lean_dec(x_543);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_550; size_t x_551; lean_object* x_552; 
x_550 = 0;
x_551 = lean_usize_of_nat(x_544);
lean_inc_ref(x_1);
x_552 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_543, x_550, x_551, x_548, x_1);
lean_dec(x_543);
if (lean_obj_tag(x_552) == 0)
{
lean_dec_ref(x_552);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_525 = x_552;
goto block_526;
}
}
}
else
{
size_t x_553; size_t x_554; lean_object* x_555; 
x_553 = 0;
x_554 = lean_usize_of_nat(x_544);
lean_inc_ref(x_1);
x_555 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_543, x_553, x_554, x_548, x_1);
lean_dec(x_543);
if (lean_obj_tag(x_555) == 0)
{
lean_dec_ref(x_555);
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_525 = x_555;
goto block_526;
}
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec_ref(x_428);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_556 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
x_557 = lean_apply_2(x_1, x_556, lean_box(0));
x_558 = lean_box(0);
x_559 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_559, 0, x_558);
return x_559;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_4);
x_10 = lean_unbox(x_5);
x_11 = lean_unbox(x_7);
x_12 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_32; lean_object* x_33; lean_object* x_35; lean_object* x_36; lean_object* x_72; uint8_t x_73; 
x_72 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
x_73 = lean_string_dec_eq(x_1, x_72);
if (x_73 == 0)
{
x_35 = x_1;
x_36 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_74; 
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_74 = lean_io_realpath(x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_92; 
x_75 = lean_ctor_get(x_74, 0);
x_92 = !lean_is_exclusive(x_74);
if (x_92 == 0)
{
x_76 = x_74;
x_77 = x_92;
goto block_91;
}
else
{
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_78; 
lean_inc(x_75);
x_78 = l_System_FilePath_fileName(x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_79 = ((lean_object*)(l_Lake_init___closed__0));
x_80 = lean_string_append(x_79, x_75);
lean_dec(x_75);
x_81 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
x_82 = lean_string_append(x_80, x_81);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_apply_2(x_7, x_84, lean_box(0));
x_86 = lean_box(0);
if (x_77 == 0)
{
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_86);
x_87 = x_76;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_86);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
else
{
lean_object* x_90; 
lean_del_object(x_76);
lean_dec(x_75);
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
lean_dec_ref(x_78);
x_35 = x_90;
x_36 = lean_box(0);
goto block_71;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_105; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_93 = lean_ctor_get(x_74, 0);
x_105 = !lean_is_exclusive(x_74);
if (x_105 == 0)
{
x_94 = x_74;
x_95 = x_105;
goto block_104;
}
else
{
lean_inc(x_93);
lean_dec(x_74);
x_94 = lean_box(0);
x_95 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_io_error_to_string(x_93);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_apply_2(x_7, x_98, lean_box(0));
x_100 = lean_box(0);
if (x_95 == 0)
{
lean_ctor_set(x_94, 0, x_100);
x_101 = x_94;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_100);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_31:
{
lean_object* x_15; 
lean_inc_ref(x_5);
x_15 = l_IO_FS_createDirAll(x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_15);
x_16 = l_Lake_stringToLegalOrSimpleName(x_13);
x_17 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_7, x_5, x_16, x_2, x_3, x_4, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_30; 
lean_dec_ref(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_18 = lean_ctor_get(x_15, 0);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
x_19 = x_15;
x_20 = x_30;
goto block_29;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_io_error_to_string(x_18);
x_22 = 3;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_apply_2(x_7, x_23, lean_box(0));
x_25 = lean_box(0);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_25);
x_26 = x_19;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
block_34:
{
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_13 = x_32;
x_14 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_32);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_33;
}
}
block_71:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_string_utf8_byte_size(x_35);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_String_Slice_trimAscii(x_39);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 2);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = lean_string_utf8_extract(x_41, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
x_45 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_44);
x_46 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_44, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_array_get_size(x_47);
x_49 = lean_nat_dec_lt(x_37, x_48);
if (x_49 == 0)
{
lean_dec(x_47);
x_13 = x_44;
x_14 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
if (x_49 == 0)
{
lean_dec(x_47);
x_13 = x_44;
x_14 = lean_box(0);
goto block_31;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
lean_inc_ref(x_7);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_47, x_52, x_53, x_50, x_7);
lean_dec(x_47);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_13 = x_44;
x_14 = lean_box(0);
goto block_31;
}
else
{
x_32 = x_44;
x_33 = x_54;
goto block_34;
}
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_48);
lean_inc_ref(x_7);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_47, x_55, x_56, x_50, x_7);
lean_dec(x_47);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
x_13 = x_44;
x_14 = lean_box(0);
goto block_31;
}
else
{
x_32 = x_44;
x_33 = x_57;
goto block_34;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_dec_ref(x_46);
x_59 = lean_array_get_size(x_58);
x_60 = lean_nat_dec_lt(x_37, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_box(0);
x_64 = lean_nat_dec_le(x_59, x_59);
if (x_64 == 0)
{
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_65; size_t x_66; lean_object* x_67; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_59);
lean_inc_ref(x_7);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_58, x_65, x_66, x_63, x_7);
lean_dec(x_58);
if (lean_obj_tag(x_67) == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_32 = x_44;
x_33 = x_67;
goto block_34;
}
}
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_59);
lean_inc_ref(x_7);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_58, x_68, x_69, x_63, x_7);
lean_dec(x_58);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
lean_dec_ref(x_44);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_32 = x_44;
x_33 = x_70;
goto block_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_6);
x_12 = l_Lake_init(x_1, x_9, x_10, x_4, x_5, x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_41; lean_object* x_43; lean_object* x_44; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_String_Slice_trimAscii(x_15);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_string_utf8_extract(x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
x_43 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_20);
x_44 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_20, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_array_get_size(x_45);
x_47 = lean_nat_dec_lt(x_13, x_46);
if (x_47 == 0)
{
lean_dec(x_45);
x_21 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(0);
x_49 = lean_nat_dec_le(x_46, x_46);
if (x_49 == 0)
{
if (x_47 == 0)
{
lean_dec(x_45);
x_21 = lean_box(0);
goto block_40;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_46);
lean_inc_ref(x_7);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_45, x_50, x_51, x_48, x_7);
lean_dec(x_45);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_21 = lean_box(0);
goto block_40;
}
else
{
x_41 = x_52;
goto block_42;
}
}
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_46);
lean_inc_ref(x_7);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_45, x_53, x_54, x_48, x_7);
lean_dec(x_45);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_21 = lean_box(0);
goto block_40;
}
else
{
x_41 = x_55;
goto block_42;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
lean_dec_ref(x_44);
x_57 = lean_array_get_size(x_56);
x_58 = lean_nat_dec_lt(x_13, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_box(0);
x_62 = lean_nat_dec_le(x_57, x_57);
if (x_62 == 0)
{
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_57);
lean_inc_ref(x_7);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_56, x_63, x_64, x_61, x_7);
lean_dec(x_56);
if (lean_obj_tag(x_65) == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_41 = x_65;
goto block_42;
}
}
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_57);
lean_inc_ref(x_7);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_56, x_66, x_67, x_61, x_7);
lean_dec(x_56);
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_41 = x_68;
goto block_42;
}
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_40:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lake_stringToLegalOrSimpleName(x_20);
lean_inc(x_22);
x_23 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_22);
x_24 = l_Lake_joinRelative(x_5, x_23);
lean_inc_ref(x_24);
x_25 = l_IO_FS_createDirAll(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_7, x_24, x_22, x_2, x_3, x_4, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_39; 
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec_ref(x_4);
x_27 = lean_ctor_get(x_25, 0);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
x_28 = x_25;
x_29 = x_39;
goto block_38;
}
else
{
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_io_error_to_string(x_27);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_apply_2(x_7, x_32, lean_box(0));
x_34 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_34);
x_35 = x_28;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
block_42:
{
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
x_21 = lean_box(0);
goto block_40;
}
else
{
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_6);
x_12 = l_Lake_new(x_1, x_9, x_10, x_4, x_5, x_11, x_7);
return x_12;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Lang(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin)
;
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
res = initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Lang(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Init(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Init(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Init(builtin);
}
#ifdef __cplusplus
}
#endif
