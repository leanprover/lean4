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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_71; 
lean_dec_ref(x_12);
x_13 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(x_11);
x_14 = l_Lake_joinRelative(x_11, x_13);
x_71 = l_System_FilePath_pathExists(x_14);
if (x_71 == 0)
{
uint8_t x_72; uint8_t x_73; 
x_72 = 4;
x_73 = l_Lake_instDecidableEqInitTemplate(x_2, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
x_75 = l_IO_FS_writeFile(x_14, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_dec_ref(x_75);
x_15 = x_7;
goto block_70;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_io_error_to_string(x_76);
x_78 = 3;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_get_size(x_7);
x_81 = lean_array_push(x_7, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
x_84 = l_IO_FS_writeFile(x_14, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
x_15 = x_7;
goto block_70;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_io_error_to_string(x_85);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_array_get_size(x_7);
x_90 = lean_array_push(x_7, x_88);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_92 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16));
x_93 = lean_array_push(x_7, x_92);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
block_70:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_16 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
x_17 = lean_string_append(x_16, x_14);
lean_dec_ref(x_14);
x_18 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_5);
x_21 = lean_array_push(x_15, x_20);
x_22 = 4;
x_23 = l_Lake_instDecidableEqInitTemplate(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7));
lean_inc_ref(x_11);
x_27 = l_Lake_joinRelative(x_11, x_26);
x_28 = l_System_FilePath_pathExists(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
x_30 = l_IO_FS_writeFile(x_27, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_30);
x_31 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
x_32 = l_Lake_joinRelative(x_11, x_31);
x_33 = l_System_FilePath_pathExists(x_32);
x_34 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
x_35 = lean_string_append(x_34, x_27);
lean_dec_ref(x_27);
x_36 = lean_string_append(x_35, x_18);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_5);
x_38 = lean_array_push(x_21, x_37);
if (x_33 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
x_40 = l_IO_FS_writeFile(x_32, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_40);
x_41 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
x_42 = lean_string_append(x_41, x_32);
lean_dec_ref(x_32);
x_43 = lean_string_append(x_42, x_18);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_5);
x_45 = lean_box(0);
x_46 = lean_array_push(x_38, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_32);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec_ref(x_40);
x_49 = lean_io_error_to_string(x_48);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_get_size(x_38);
x_53 = lean_array_push(x_38, x_51);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_32);
x_55 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12));
x_56 = lean_array_push(x_38, x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_27);
lean_dec_ref(x_11);
x_59 = lean_ctor_get(x_30, 0);
lean_inc(x_59);
lean_dec_ref(x_30);
x_60 = lean_io_error_to_string(x_59);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_get_size(x_21);
x_64 = lean_array_push(x_21, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_27);
lean_dec_ref(x_11);
x_66 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14));
x_67 = lean_array_push(x_21, x_66);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_11);
x_96 = lean_ctor_get(x_12, 0);
lean_inc(x_96);
lean_dec_ref(x_12);
x_97 = lean_io_error_to_string(x_96);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_get_size(x_7);
x_101 = lean_array_push(x_7, x_99);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
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
lean_object* x_12; lean_object* x_13; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_447; lean_object* x_448; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_500; uint8_t x_502; lean_object* x_535; uint8_t x_536; 
x_12 = l_Lake_defaultConfigFile;
x_407 = l_Lake_ConfigLang_fileExtension(x_4);
x_408 = l_System_FilePath_addExtension(x_12, x_407);
lean_dec_ref(x_407);
lean_inc_ref(x_1);
x_409 = l_Lake_joinRelative(x_1, x_408);
x_502 = l_System_FilePath_pathExists(x_409);
x_535 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_536 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_536 == 0)
{
goto block_534;
}
else
{
lean_object* x_537; uint8_t x_538; 
x_537 = lean_box(0);
x_538 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_538 == 0)
{
if (x_536 == 0)
{
goto block_534;
}
else
{
size_t x_539; size_t x_540; lean_object* x_541; 
x_539 = 0;
x_540 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_541 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_535, x_539, x_540, x_537, x_7);
if (lean_obj_tag(x_541) == 0)
{
lean_dec_ref(x_541);
goto block_534;
}
else
{
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_541;
}
}
}
else
{
size_t x_542; size_t x_543; lean_object* x_544; 
x_542 = 0;
x_543 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_544 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_535, x_542, x_543, x_537, x_7);
if (lean_obj_tag(x_544) == 0)
{
lean_dec_ref(x_544);
goto block_534;
}
else
{
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_544;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_29:
{
if (x_6 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(x_1);
x_18 = l_Lake_joinRelative(x_1, x_17);
lean_inc_ref(x_18);
x_19 = l_Lake_joinRelative(x_18, x_12);
x_20 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
x_21 = lean_box(1);
x_22 = l_Lean_Options_empty;
x_23 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
x_24 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set(x_24, 4, x_16);
lean_ctor_set(x_24, 5, x_17);
lean_ctor_set(x_24, 6, x_18);
lean_ctor_set(x_24, 7, x_12);
lean_ctor_set(x_24, 8, x_19);
lean_ctor_set(x_24, 9, x_20);
lean_ctor_set(x_24, 10, x_21);
lean_ctor_set(x_24, 11, x_22);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set(x_24, 13, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*14, x_6);
lean_ctor_set_uint8(x_24, sizeof(void*)*14 + 1, x_6);
lean_ctor_set_uint8(x_24, sizeof(void*)*14 + 2, x_6);
x_25 = l_Lean_NameSet_empty;
x_26 = l_Lake_updateManifest(x_24, x_25, x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
block_34:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(x_30);
x_33 = lean_apply_2(x_30, x_32, lean_box(0));
x_13 = x_30;
goto block_29;
}
else
{
lean_dec_ref(x_31);
x_13 = x_30;
goto block_29;
}
}
block_39:
{
switch (x_3) {
case 3:
{
x_30 = x_36;
x_31 = x_35;
goto block_34;
}
case 4:
{
x_30 = x_36;
x_31 = x_35;
goto block_34;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
block_45:
{
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(x_40);
x_44 = lean_apply_2(x_40, x_43, lean_box(0));
x_35 = x_41;
x_36 = x_40;
goto block_39;
}
else
{
x_35 = x_41;
x_36 = x_40;
goto block_39;
}
}
block_118:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(x_1);
x_51 = l_Lake_joinRelative(x_1, x_50);
x_52 = 4;
x_53 = lean_io_prim_handle_mk(x_51, x_52);
lean_dec_ref(x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_56 = lean_io_prim_handle_put_str(x_54, x_55);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec_ref(x_56);
x_57 = l_Lake_toolchainFileName;
lean_inc_ref(x_1);
x_58 = l_Lake_joinRelative(x_1, x_57);
x_59 = lean_string_utf8_byte_size(x_47);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_46);
x_62 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_63 = lean_string_append(x_47, x_62);
x_64 = l_IO_FS_writeFile(x_58, x_63);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_35 = x_48;
x_36 = x_49;
goto block_39;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_77; 
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_64, 0);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
x_66 = x_64;
x_67 = x_77;
goto block_76;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_io_error_to_string(x_65);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_apply_2(x_49, x_70, lean_box(0));
x_72 = lean_box(0);
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_72);
x_73 = x_66;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec_ref(x_47);
x_78 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_78);
lean_dec_ref(x_46);
x_79 = lean_string_utf8_byte_size(x_78);
lean_dec_ref(x_78);
x_80 = lean_nat_dec_eq(x_79, x_60);
if (x_80 == 0)
{
uint8_t x_81; lean_object* x_82; uint8_t x_83; 
x_81 = l_System_FilePath_pathExists(x_58);
lean_dec_ref(x_58);
x_82 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_83 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_83 == 0)
{
x_40 = x_49;
x_41 = x_48;
x_42 = x_81;
goto block_45;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_box(0);
x_85 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_85 == 0)
{
if (x_83 == 0)
{
x_40 = x_49;
x_41 = x_48;
x_42 = x_81;
goto block_45;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; 
x_86 = 0;
x_87 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_49);
x_88 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_82, x_86, x_87, x_84, x_49);
if (lean_obj_tag(x_88) == 0)
{
lean_dec_ref(x_88);
x_40 = x_49;
x_41 = x_48;
x_42 = x_81;
goto block_45;
}
else
{
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_88;
}
}
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_49);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_82, x_89, x_90, x_84, x_49);
if (lean_obj_tag(x_91) == 0)
{
lean_dec_ref(x_91);
x_40 = x_49;
x_41 = x_48;
x_42 = x_81;
goto block_45;
}
else
{
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_91;
}
}
}
}
else
{
lean_dec_ref(x_58);
x_35 = x_48;
x_36 = x_49;
goto block_39;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_104; 
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_56, 0);
x_104 = !lean_is_exclusive(x_56);
if (x_104 == 0)
{
x_93 = x_56;
x_94 = x_104;
goto block_103;
}
else
{
lean_inc(x_92);
lean_dec(x_56);
x_93 = lean_box(0);
x_94 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_io_error_to_string(x_92);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_apply_2(x_49, x_97, lean_box(0));
x_99 = lean_box(0);
if (x_94 == 0)
{
lean_ctor_set(x_93, 0, x_99);
x_100 = x_93;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_99);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_117; 
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_105 = lean_ctor_get(x_53, 0);
x_117 = !lean_is_exclusive(x_53);
if (x_117 == 0)
{
x_106 = x_53;
x_107 = x_117;
goto block_116;
}
else
{
lean_inc(x_105);
lean_dec(x_53);
x_106 = lean_box(0);
x_107 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_io_error_to_string(x_105);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_apply_2(x_49, x_110, lean_box(0));
x_112 = lean_box(0);
if (x_107 == 0)
{
lean_ctor_set(x_106, 0, x_112);
x_113 = x_106;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
block_125:
{
lean_object* x_123; lean_object* x_124; 
x_123 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(x_122);
x_124 = lean_apply_2(x_122, x_123, lean_box(0));
x_46 = x_119;
x_47 = x_121;
x_48 = x_120;
x_49 = x_122;
goto block_118;
}
block_131:
{
if (lean_obj_tag(x_130) == 0)
{
lean_dec_ref(x_130);
x_46 = x_126;
x_47 = x_128;
x_48 = x_127;
x_49 = x_129;
goto block_118;
}
else
{
lean_dec_ref(x_130);
x_119 = x_126;
x_120 = x_127;
x_121 = x_128;
x_122 = x_129;
goto block_125;
}
}
block_163:
{
lean_object* x_136; uint8_t x_137; 
x_136 = l_Lake_Git_upstreamBranch;
x_137 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_unsigned_to_nat(0u);
x_139 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_1);
x_140 = l_Lake_GitRepo_checkoutBranch(x_136, x_1, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_array_get_size(x_141);
x_143 = lean_nat_dec_lt(x_138, x_142);
if (x_143 == 0)
{
lean_dec(x_141);
x_46 = x_132;
x_47 = x_134;
x_48 = x_133;
x_49 = x_135;
goto block_118;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_box(0);
x_145 = lean_nat_dec_le(x_142, x_142);
if (x_145 == 0)
{
if (x_143 == 0)
{
lean_dec(x_141);
x_46 = x_132;
x_47 = x_134;
x_48 = x_133;
x_49 = x_135;
goto block_118;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; 
x_146 = 0;
x_147 = lean_usize_of_nat(x_142);
lean_inc_ref(x_135);
x_148 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_141, x_146, x_147, x_144, x_135);
lean_dec(x_141);
if (lean_obj_tag(x_148) == 0)
{
lean_dec_ref(x_148);
x_46 = x_132;
x_47 = x_134;
x_48 = x_133;
x_49 = x_135;
goto block_118;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_148;
goto block_131;
}
}
}
else
{
size_t x_149; size_t x_150; lean_object* x_151; 
x_149 = 0;
x_150 = lean_usize_of_nat(x_142);
lean_inc_ref(x_135);
x_151 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_141, x_149, x_150, x_144, x_135);
lean_dec(x_141);
if (lean_obj_tag(x_151) == 0)
{
lean_dec_ref(x_151);
x_46 = x_132;
x_47 = x_134;
x_48 = x_133;
x_49 = x_135;
goto block_118;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_151;
goto block_131;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_140, 1);
lean_inc(x_152);
lean_dec_ref(x_140);
x_153 = lean_array_get_size(x_152);
x_154 = lean_nat_dec_lt(x_138, x_153);
if (x_154 == 0)
{
lean_dec(x_152);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_box(0);
x_156 = lean_nat_dec_le(x_153, x_153);
if (x_156 == 0)
{
if (x_154 == 0)
{
lean_dec(x_152);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_153);
lean_inc_ref(x_135);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_152, x_157, x_158, x_155, x_135);
lean_dec(x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_159;
goto block_131;
}
}
}
else
{
size_t x_160; size_t x_161; lean_object* x_162; 
x_160 = 0;
x_161 = lean_usize_of_nat(x_153);
lean_inc_ref(x_135);
x_162 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_152, x_160, x_161, x_155, x_135);
lean_dec(x_152);
if (lean_obj_tag(x_162) == 0)
{
lean_dec_ref(x_162);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_162;
goto block_131;
}
}
}
}
}
else
{
x_46 = x_132;
x_47 = x_134;
x_48 = x_133;
x_49 = x_135;
goto block_118;
}
}
block_169:
{
if (lean_obj_tag(x_168) == 0)
{
lean_dec_ref(x_168);
x_132 = x_164;
x_133 = x_167;
x_134 = x_166;
x_135 = x_165;
goto block_163;
}
else
{
lean_dec_ref(x_168);
x_119 = x_164;
x_120 = x_167;
x_121 = x_166;
x_122 = x_165;
goto block_125;
}
}
block_200:
{
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_unsigned_to_nat(0u);
x_176 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_1);
x_177 = l_Lake_GitRepo_quietInit(x_1, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = lean_array_get_size(x_178);
x_180 = lean_nat_dec_lt(x_175, x_179);
if (x_180 == 0)
{
lean_dec(x_178);
x_132 = x_170;
x_133 = x_173;
x_134 = x_172;
x_135 = x_171;
goto block_163;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_box(0);
x_182 = lean_nat_dec_le(x_179, x_179);
if (x_182 == 0)
{
if (x_180 == 0)
{
lean_dec(x_178);
x_132 = x_170;
x_133 = x_173;
x_134 = x_172;
x_135 = x_171;
goto block_163;
}
else
{
size_t x_183; size_t x_184; lean_object* x_185; 
x_183 = 0;
x_184 = lean_usize_of_nat(x_179);
lean_inc_ref(x_171);
x_185 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_178, x_183, x_184, x_181, x_171);
lean_dec(x_178);
if (lean_obj_tag(x_185) == 0)
{
lean_dec_ref(x_185);
x_132 = x_170;
x_133 = x_173;
x_134 = x_172;
x_135 = x_171;
goto block_163;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_185;
goto block_169;
}
}
}
else
{
size_t x_186; size_t x_187; lean_object* x_188; 
x_186 = 0;
x_187 = lean_usize_of_nat(x_179);
lean_inc_ref(x_171);
x_188 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_178, x_186, x_187, x_181, x_171);
lean_dec(x_178);
if (lean_obj_tag(x_188) == 0)
{
lean_dec_ref(x_188);
x_132 = x_170;
x_133 = x_173;
x_134 = x_172;
x_135 = x_171;
goto block_163;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_188;
goto block_169;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = lean_ctor_get(x_177, 1);
lean_inc(x_189);
lean_dec_ref(x_177);
x_190 = lean_array_get_size(x_189);
x_191 = lean_nat_dec_lt(x_175, x_190);
if (x_191 == 0)
{
lean_dec(x_189);
x_119 = x_170;
x_120 = x_173;
x_121 = x_172;
x_122 = x_171;
goto block_125;
}
else
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_box(0);
x_193 = lean_nat_dec_le(x_190, x_190);
if (x_193 == 0)
{
if (x_191 == 0)
{
lean_dec(x_189);
x_119 = x_170;
x_120 = x_173;
x_121 = x_172;
x_122 = x_171;
goto block_125;
}
else
{
size_t x_194; size_t x_195; lean_object* x_196; 
x_194 = 0;
x_195 = lean_usize_of_nat(x_190);
lean_inc_ref(x_171);
x_196 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_189, x_194, x_195, x_192, x_171);
lean_dec(x_189);
if (lean_obj_tag(x_196) == 0)
{
lean_dec_ref(x_196);
x_119 = x_170;
x_120 = x_173;
x_121 = x_172;
x_122 = x_171;
goto block_125;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_196;
goto block_169;
}
}
}
else
{
size_t x_197; size_t x_198; lean_object* x_199; 
x_197 = 0;
x_198 = lean_usize_of_nat(x_190);
lean_inc_ref(x_171);
x_199 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_189, x_197, x_198, x_192, x_171);
lean_dec(x_189);
if (lean_obj_tag(x_199) == 0)
{
lean_dec_ref(x_199);
x_119 = x_170;
x_120 = x_173;
x_121 = x_172;
x_122 = x_171;
goto block_125;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_199;
goto block_169;
}
}
}
}
}
else
{
x_46 = x_170;
x_47 = x_172;
x_48 = x_173;
x_49 = x_171;
goto block_118;
}
}
block_216:
{
uint8_t x_205; lean_object* x_206; uint8_t x_207; 
lean_inc_ref(x_1);
x_205 = l_Lake_GitRepo_insideWorkTree(x_1);
x_206 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_207 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_207 == 0)
{
x_170 = x_201;
x_171 = x_204;
x_172 = x_202;
x_173 = x_203;
x_174 = x_205;
goto block_200;
}
else
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_box(0);
x_209 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_209 == 0)
{
if (x_207 == 0)
{
x_170 = x_201;
x_171 = x_204;
x_172 = x_202;
x_173 = x_203;
x_174 = x_205;
goto block_200;
}
else
{
size_t x_210; size_t x_211; lean_object* x_212; 
x_210 = 0;
x_211 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_204);
x_212 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_206, x_210, x_211, x_208, x_204);
if (lean_obj_tag(x_212) == 0)
{
lean_dec_ref(x_212);
x_170 = x_201;
x_171 = x_204;
x_172 = x_202;
x_173 = x_203;
x_174 = x_205;
goto block_200;
}
else
{
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_212;
}
}
}
else
{
size_t x_213; size_t x_214; lean_object* x_215; 
x_213 = 0;
x_214 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_204);
x_215 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_206, x_213, x_214, x_208, x_204);
if (lean_obj_tag(x_215) == 0)
{
lean_dec_ref(x_215);
x_170 = x_201;
x_171 = x_204;
x_172 = x_202;
x_173 = x_203;
x_174 = x_205;
goto block_200;
}
else
{
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_215;
}
}
}
}
block_237:
{
lean_object* x_223; 
x_223 = l_IO_FS_writeFile(x_219, x_222);
lean_dec_ref(x_222);
lean_dec_ref(x_219);
if (lean_obj_tag(x_223) == 0)
{
lean_dec_ref(x_223);
x_201 = x_217;
x_202 = x_221;
x_203 = x_220;
x_204 = x_218;
goto block_216;
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_236; 
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_217);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_224 = lean_ctor_get(x_223, 0);
x_236 = !lean_is_exclusive(x_223);
if (x_236 == 0)
{
x_225 = x_223;
x_226 = x_236;
goto block_235;
}
else
{
lean_inc(x_224);
lean_dec(x_223);
x_225 = lean_box(0);
x_226 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_io_error_to_string(x_224);
x_228 = 3;
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_228);
x_230 = lean_apply_2(x_218, x_229, lean_box(0));
x_231 = lean_box(0);
if (x_226 == 0)
{
lean_ctor_set(x_225, 0, x_231);
x_232 = x_225;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_231);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
}
}
}
}
block_250:
{
if (x_243 == 0)
{
uint8_t x_244; uint8_t x_245; 
x_244 = 4;
x_245 = l_Lake_instDecidableEqInitTemplate(x_3, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_247 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_246);
lean_dec_ref(x_246);
x_217 = x_238;
x_218 = x_240;
x_219 = x_239;
x_220 = x_242;
x_221 = x_241;
x_222 = x_247;
goto block_237;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_249 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_248);
lean_dec_ref(x_248);
x_217 = x_238;
x_218 = x_240;
x_219 = x_239;
x_220 = x_242;
x_221 = x_241;
x_222 = x_249;
goto block_237;
}
}
else
{
lean_dec_ref(x_239);
lean_dec(x_2);
x_201 = x_238;
x_202 = x_241;
x_203 = x_242;
x_204 = x_240;
goto block_216;
}
}
block_268:
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(x_1);
x_256 = l_Lake_joinRelative(x_1, x_255);
x_257 = l_System_FilePath_pathExists(x_256);
x_258 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_259 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_259 == 0)
{
x_238 = x_251;
x_239 = x_256;
x_240 = x_254;
x_241 = x_253;
x_242 = x_252;
x_243 = x_257;
goto block_250;
}
else
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_box(0);
x_261 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_261 == 0)
{
if (x_259 == 0)
{
x_238 = x_251;
x_239 = x_256;
x_240 = x_254;
x_241 = x_253;
x_242 = x_252;
x_243 = x_257;
goto block_250;
}
else
{
size_t x_262; size_t x_263; lean_object* x_264; 
x_262 = 0;
x_263 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_254);
x_264 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_258, x_262, x_263, x_260, x_254);
if (lean_obj_tag(x_264) == 0)
{
lean_dec_ref(x_264);
x_238 = x_251;
x_239 = x_256;
x_240 = x_254;
x_241 = x_253;
x_242 = x_252;
x_243 = x_257;
goto block_250;
}
else
{
lean_dec_ref(x_256);
lean_dec_ref(x_254);
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_264;
}
}
}
else
{
size_t x_265; size_t x_266; lean_object* x_267; 
x_265 = 0;
x_266 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_254);
x_267 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_258, x_265, x_266, x_260, x_254);
if (lean_obj_tag(x_267) == 0)
{
lean_dec_ref(x_267);
x_238 = x_251;
x_239 = x_256;
x_240 = x_254;
x_241 = x_253;
x_242 = x_252;
x_243 = x_257;
goto block_250;
}
else
{
lean_dec_ref(x_256);
lean_dec_ref(x_254);
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_267;
}
}
}
}
block_308:
{
if (x_275 == 0)
{
uint8_t x_276; uint8_t x_277; 
x_276 = 1;
x_277 = l_Lake_instDecidableEqInitTemplate(x_3, x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_271);
x_279 = l_IO_FS_writeFile(x_274, x_278);
lean_dec_ref(x_278);
lean_dec_ref(x_274);
if (lean_obj_tag(x_279) == 0)
{
lean_dec_ref(x_279);
x_251 = x_269;
x_252 = x_273;
x_253 = x_272;
x_254 = x_270;
goto block_268;
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_292; 
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec_ref(x_269);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_280 = lean_ctor_get(x_279, 0);
x_292 = !lean_is_exclusive(x_279);
if (x_292 == 0)
{
x_281 = x_279;
x_282 = x_292;
goto block_291;
}
else
{
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_box(0);
x_282 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_283 = lean_io_error_to_string(x_280);
x_284 = 3;
x_285 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_284);
x_286 = lean_apply_2(x_270, x_285, lean_box(0));
x_287 = lean_box(0);
if (x_282 == 0)
{
lean_ctor_set(x_281, 0, x_287);
x_288 = x_281;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_287);
x_288 = x_290;
goto block_289;
}
block_289:
{
return x_288;
}
}
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_271);
x_293 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
x_294 = l_IO_FS_writeFile(x_274, x_293);
lean_dec_ref(x_274);
if (lean_obj_tag(x_294) == 0)
{
lean_dec_ref(x_294);
x_251 = x_269;
x_252 = x_273;
x_253 = x_272;
x_254 = x_270;
goto block_268;
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_307; 
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec_ref(x_269);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_294, 0);
x_307 = !lean_is_exclusive(x_294);
if (x_307 == 0)
{
x_296 = x_294;
x_297 = x_307;
goto block_306;
}
else
{
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_box(0);
x_297 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_io_error_to_string(x_295);
x_299 = 3;
x_300 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set_uint8(x_300, sizeof(void*)*1, x_299);
x_301 = lean_apply_2(x_270, x_300, lean_box(0));
x_302 = lean_box(0);
if (x_297 == 0)
{
lean_ctor_set(x_296, 0, x_302);
x_303 = x_296;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_302);
x_303 = x_305;
goto block_304;
}
block_304:
{
return x_303;
}
}
}
}
}
else
{
lean_dec_ref(x_274);
lean_dec(x_271);
x_251 = x_269;
x_252 = x_273;
x_253 = x_272;
x_254 = x_270;
goto block_268;
}
}
block_327:
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; 
x_314 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_1);
x_315 = l_Lake_joinRelative(x_1, x_314);
x_316 = l_System_FilePath_pathExists(x_315);
x_317 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_318 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_318 == 0)
{
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_313;
x_273 = x_312;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_box(0);
x_320 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_320 == 0)
{
if (x_318 == 0)
{
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_313;
x_273 = x_312;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
size_t x_321; size_t x_322; lean_object* x_323; 
x_321 = 0;
x_322 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_310);
x_323 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_317, x_321, x_322, x_319, x_310);
if (lean_obj_tag(x_323) == 0)
{
lean_dec_ref(x_323);
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_313;
x_273 = x_312;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
lean_dec_ref(x_315);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_323;
}
}
}
else
{
size_t x_324; size_t x_325; lean_object* x_326; 
x_324 = 0;
x_325 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_310);
x_326 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_317, x_324, x_325, x_319, x_310);
if (lean_obj_tag(x_326) == 0)
{
lean_dec_ref(x_326);
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_313;
x_273 = x_312;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
lean_dec_ref(x_315);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_326;
}
}
}
}
block_333:
{
switch (x_3) {
case 0:
{
x_309 = x_328;
x_310 = x_332;
x_311 = x_329;
x_312 = x_331;
x_313 = x_330;
goto block_327;
}
case 1:
{
x_309 = x_328;
x_310 = x_332;
x_311 = x_329;
x_312 = x_331;
x_313 = x_330;
goto block_327;
}
default: 
{
lean_dec(x_329);
x_251 = x_328;
x_252 = x_331;
x_253 = x_330;
x_254 = x_332;
goto block_268;
}
}
}
block_355:
{
lean_object* x_341; 
x_341 = l_IO_FS_writeFile(x_335, x_340);
lean_dec_ref(x_340);
lean_dec_ref(x_335);
if (lean_obj_tag(x_341) == 0)
{
lean_dec_ref(x_341);
x_328 = x_334;
x_329 = x_336;
x_330 = x_339;
x_331 = x_338;
x_332 = x_337;
goto block_333;
}
else
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_354; 
lean_dec_ref(x_339);
lean_dec(x_338);
lean_dec(x_336);
lean_dec_ref(x_334);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_342 = lean_ctor_get(x_341, 0);
x_354 = !lean_is_exclusive(x_341);
if (x_354 == 0)
{
x_343 = x_341;
x_344 = x_354;
goto block_353;
}
else
{
lean_inc(x_342);
lean_dec(x_341);
x_343 = lean_box(0);
x_344 = x_354;
goto block_353;
}
block_353:
{
lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_io_error_to_string(x_342);
x_346 = 3;
x_347 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*1, x_346);
x_348 = lean_apply_2(x_337, x_347, lean_box(0));
x_349 = lean_box(0);
if (x_344 == 0)
{
lean_ctor_set(x_343, 0, x_349);
x_350 = x_343;
goto block_351;
}
else
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_349);
x_350 = x_352;
goto block_351;
}
block_351:
{
return x_350;
}
}
}
}
block_368:
{
uint8_t x_362; uint8_t x_363; 
x_362 = 4;
x_363 = l_Lake_instDecidableEqInitTemplate(x_3, x_362);
if (x_363 == 0)
{
uint8_t x_364; lean_object* x_365; lean_object* x_366; 
x_364 = 1;
lean_inc(x_358);
x_365 = l_Lean_Name_toString(x_358, x_364);
lean_inc(x_358);
x_366 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_365, x_358);
lean_dec_ref(x_365);
x_334 = x_356;
x_335 = x_357;
x_336 = x_358;
x_337 = x_361;
x_338 = x_360;
x_339 = x_359;
x_340 = x_366;
goto block_355;
}
else
{
lean_object* x_367; 
lean_inc(x_358);
x_367 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_358);
x_334 = x_356;
x_335 = x_357;
x_336 = x_358;
x_337 = x_361;
x_338 = x_360;
x_339 = x_359;
x_340 = x_367;
goto block_355;
}
}
block_406:
{
if (x_376 == 0)
{
lean_object* x_377; 
x_377 = l_IO_FS_createDirAll(x_371);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; 
lean_dec_ref(x_377);
x_378 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
x_379 = l_IO_FS_writeFile(x_375, x_378);
lean_dec_ref(x_375);
if (lean_obj_tag(x_379) == 0)
{
lean_dec_ref(x_379);
x_356 = x_369;
x_357 = x_370;
x_358 = x_372;
x_359 = x_374;
x_360 = x_373;
x_361 = x_7;
goto block_368;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_392; 
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec_ref(x_370);
lean_dec_ref(x_369);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_380 = lean_ctor_get(x_379, 0);
x_392 = !lean_is_exclusive(x_379);
if (x_392 == 0)
{
x_381 = x_379;
x_382 = x_392;
goto block_391;
}
else
{
lean_inc(x_380);
lean_dec(x_379);
x_381 = lean_box(0);
x_382 = x_392;
goto block_391;
}
block_391:
{
lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_383 = lean_io_error_to_string(x_380);
x_384 = 3;
x_385 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set_uint8(x_385, sizeof(void*)*1, x_384);
x_386 = lean_apply_2(x_7, x_385, lean_box(0));
x_387 = lean_box(0);
if (x_382 == 0)
{
lean_ctor_set(x_381, 0, x_387);
x_388 = x_381;
goto block_389;
}
else
{
lean_object* x_390; 
x_390 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_390, 0, x_387);
x_388 = x_390;
goto block_389;
}
block_389:
{
return x_388;
}
}
}
}
else
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_405; 
lean_dec_ref(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec_ref(x_370);
lean_dec_ref(x_369);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_393 = lean_ctor_get(x_377, 0);
x_405 = !lean_is_exclusive(x_377);
if (x_405 == 0)
{
x_394 = x_377;
x_395 = x_405;
goto block_404;
}
else
{
lean_inc(x_393);
lean_dec(x_377);
x_394 = lean_box(0);
x_395 = x_405;
goto block_404;
}
block_404:
{
lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_396 = lean_io_error_to_string(x_393);
x_397 = 3;
x_398 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*1, x_397);
x_399 = lean_apply_2(x_7, x_398, lean_box(0));
x_400 = lean_box(0);
if (x_395 == 0)
{
lean_ctor_set(x_394, 0, x_400);
x_401 = x_394;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_400);
x_401 = x_403;
goto block_402;
}
block_402:
{
return x_401;
}
}
}
}
else
{
lean_dec_ref(x_375);
lean_dec_ref(x_371);
x_356 = x_369;
x_357 = x_370;
x_358 = x_372;
x_359 = x_374;
x_360 = x_373;
x_361 = x_7;
goto block_368;
}
}
block_446:
{
lean_object* x_415; lean_object* x_416; 
lean_inc(x_414);
lean_inc(x_411);
lean_inc(x_2);
x_415 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_411, x_414);
x_416 = l_IO_FS_writeFile(x_409, x_415);
lean_dec_ref(x_415);
lean_dec_ref(x_409);
if (lean_obj_tag(x_416) == 0)
{
lean_dec_ref(x_416);
if (lean_obj_tag(x_413) == 1)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; uint8_t x_424; 
x_417 = lean_ctor_get(x_413, 0);
lean_inc(x_417);
lean_dec_ref(x_413);
x_418 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
lean_inc(x_417);
x_419 = l_System_FilePath_withExtension(x_417, x_418);
x_420 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(x_419);
x_421 = l_Lake_joinRelative(x_419, x_420);
x_422 = l_System_FilePath_pathExists(x_421);
x_423 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_424 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_424 == 0)
{
x_369 = x_410;
x_370 = x_417;
x_371 = x_419;
x_372 = x_411;
x_373 = x_414;
x_374 = x_412;
x_375 = x_421;
x_376 = x_422;
goto block_406;
}
else
{
lean_object* x_425; uint8_t x_426; 
x_425 = lean_box(0);
x_426 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_426 == 0)
{
if (x_424 == 0)
{
x_369 = x_410;
x_370 = x_417;
x_371 = x_419;
x_372 = x_411;
x_373 = x_414;
x_374 = x_412;
x_375 = x_421;
x_376 = x_422;
goto block_406;
}
else
{
size_t x_427; size_t x_428; lean_object* x_429; 
x_427 = 0;
x_428 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_429 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_423, x_427, x_428, x_425, x_7);
if (lean_obj_tag(x_429) == 0)
{
lean_dec_ref(x_429);
x_369 = x_410;
x_370 = x_417;
x_371 = x_419;
x_372 = x_411;
x_373 = x_414;
x_374 = x_412;
x_375 = x_421;
x_376 = x_422;
goto block_406;
}
else
{
lean_dec_ref(x_421);
lean_dec_ref(x_419);
lean_dec(x_417);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_429;
}
}
}
else
{
size_t x_430; size_t x_431; lean_object* x_432; 
x_430 = 0;
x_431 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_432 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_423, x_430, x_431, x_425, x_7);
if (lean_obj_tag(x_432) == 0)
{
lean_dec_ref(x_432);
x_369 = x_410;
x_370 = x_417;
x_371 = x_419;
x_372 = x_411;
x_373 = x_414;
x_374 = x_412;
x_375 = x_421;
x_376 = x_422;
goto block_406;
}
else
{
lean_dec_ref(x_421);
lean_dec_ref(x_419);
lean_dec(x_417);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_432;
}
}
}
}
else
{
lean_dec(x_413);
x_328 = x_410;
x_329 = x_411;
x_330 = x_412;
x_331 = x_414;
x_332 = x_7;
goto block_333;
}
}
else
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; uint8_t x_445; 
lean_dec(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_433 = lean_ctor_get(x_416, 0);
x_445 = !lean_is_exclusive(x_416);
if (x_445 == 0)
{
x_434 = x_416;
x_435 = x_445;
goto block_444;
}
else
{
lean_inc(x_433);
lean_dec(x_416);
x_434 = lean_box(0);
x_435 = x_445;
goto block_444;
}
block_444:
{
lean_object* x_436; uint8_t x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_io_error_to_string(x_433);
x_437 = 3;
x_438 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*1, x_437);
x_439 = lean_apply_2(x_7, x_438, lean_box(0));
x_440 = lean_box(0);
if (x_435 == 0)
{
lean_ctor_set(x_434, 0, x_440);
x_441 = x_434;
goto block_442;
}
else
{
lean_object* x_443; 
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_440);
x_441 = x_443;
goto block_442;
}
block_442:
{
return x_441;
}
}
}
}
block_455:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_5, 1);
x_450 = lean_ctor_get(x_5, 18);
lean_inc_ref(x_450);
x_451 = l_Lake_ToolchainVer_ofString(x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc_ref(x_452);
lean_dec_ref(x_451);
x_453 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_453, 0, x_452);
lean_inc_ref(x_450);
lean_inc_ref(x_449);
x_410 = x_449;
x_411 = x_447;
x_412 = x_450;
x_413 = x_448;
x_414 = x_453;
goto block_446;
}
else
{
lean_object* x_454; 
lean_dec_ref(x_451);
x_454 = lean_box(0);
lean_inc_ref(x_450);
lean_inc_ref(x_449);
x_410 = x_449;
x_411 = x_447;
x_412 = x_450;
x_413 = x_448;
x_414 = x_454;
goto block_446;
}
}
block_461:
{
if (x_458 == 0)
{
lean_object* x_459; 
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_457);
x_447 = x_456;
x_448 = x_459;
goto block_455;
}
else
{
lean_object* x_460; 
lean_dec_ref(x_457);
x_460 = lean_box(0);
x_447 = x_456;
x_448 = x_460;
goto block_455;
}
}
block_479:
{
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; uint8_t x_469; 
lean_dec_ref(x_463);
lean_inc(x_2);
x_465 = l_Lake_toUpperCamelCase(x_2);
lean_inc(x_465);
x_466 = l_Lean_modToFilePath(x_1, x_465, x_462);
lean_dec_ref(x_462);
x_467 = l_System_FilePath_pathExists(x_466);
x_468 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_469 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_469 == 0)
{
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
lean_object* x_470; uint8_t x_471; 
x_470 = lean_box(0);
x_471 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_471 == 0)
{
if (x_469 == 0)
{
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
size_t x_472; size_t x_473; lean_object* x_474; 
x_472 = 0;
x_473 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_474 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_468, x_472, x_473, x_470, x_7);
if (lean_obj_tag(x_474) == 0)
{
lean_dec_ref(x_474);
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_474;
}
}
}
else
{
size_t x_475; size_t x_476; lean_object* x_477; 
x_475 = 0;
x_476 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_477 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_468, x_475, x_476, x_470, x_7);
if (lean_obj_tag(x_477) == 0)
{
lean_dec_ref(x_477);
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_477;
}
}
}
}
else
{
lean_object* x_478; 
lean_dec_ref(x_462);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_463);
lean_inc(x_2);
x_447 = x_2;
x_448 = x_478;
goto block_455;
}
}
block_485:
{
uint8_t x_483; uint8_t x_484; 
x_483 = 1;
x_484 = l_Lake_instDecidableEqInitTemplate(x_3, x_483);
if (x_484 == 0)
{
x_462 = x_480;
x_463 = x_481;
x_464 = x_482;
goto block_479;
}
else
{
x_462 = x_480;
x_463 = x_481;
x_464 = x_484;
goto block_479;
}
}
block_499:
{
lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; uint8_t x_490; 
x_486 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(x_2);
x_487 = l_Lean_modToFilePath(x_1, x_2, x_486);
x_488 = l_System_FilePath_pathExists(x_487);
x_489 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_490 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_490 == 0)
{
x_480 = x_486;
x_481 = x_487;
x_482 = x_488;
goto block_485;
}
else
{
lean_object* x_491; uint8_t x_492; 
x_491 = lean_box(0);
x_492 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_492 == 0)
{
if (x_490 == 0)
{
x_480 = x_486;
x_481 = x_487;
x_482 = x_488;
goto block_485;
}
else
{
size_t x_493; size_t x_494; lean_object* x_495; 
x_493 = 0;
x_494 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_495 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_489, x_493, x_494, x_491, x_7);
if (lean_obj_tag(x_495) == 0)
{
lean_dec_ref(x_495);
x_480 = x_486;
x_481 = x_487;
x_482 = x_488;
goto block_485;
}
else
{
lean_dec_ref(x_487);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_495;
}
}
}
else
{
size_t x_496; size_t x_497; lean_object* x_498; 
x_496 = 0;
x_497 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_7);
x_498 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_489, x_496, x_497, x_491, x_7);
if (lean_obj_tag(x_498) == 0)
{
lean_dec_ref(x_498);
x_480 = x_486;
x_481 = x_487;
x_482 = x_488;
goto block_485;
}
else
{
lean_dec_ref(x_487);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_498;
}
}
}
}
block_501:
{
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
goto block_499;
}
else
{
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_500;
}
}
block_534:
{
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_unsigned_to_nat(0u);
x_504 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_1);
x_505 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_1, x_3, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec_ref(x_505);
x_507 = lean_array_get_size(x_506);
x_508 = lean_nat_dec_lt(x_503, x_507);
if (x_508 == 0)
{
lean_dec(x_506);
goto block_499;
}
else
{
lean_object* x_509; uint8_t x_510; 
x_509 = lean_box(0);
x_510 = lean_nat_dec_le(x_507, x_507);
if (x_510 == 0)
{
if (x_508 == 0)
{
lean_dec(x_506);
goto block_499;
}
else
{
size_t x_511; size_t x_512; lean_object* x_513; 
x_511 = 0;
x_512 = lean_usize_of_nat(x_507);
lean_inc_ref(x_7);
x_513 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_506, x_511, x_512, x_509, x_7);
lean_dec(x_506);
if (lean_obj_tag(x_513) == 0)
{
lean_dec_ref(x_513);
goto block_499;
}
else
{
x_500 = x_513;
goto block_501;
}
}
}
else
{
size_t x_514; size_t x_515; lean_object* x_516; 
x_514 = 0;
x_515 = lean_usize_of_nat(x_507);
lean_inc_ref(x_7);
x_516 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_506, x_514, x_515, x_509, x_7);
lean_dec(x_506);
if (lean_obj_tag(x_516) == 0)
{
lean_dec_ref(x_516);
goto block_499;
}
else
{
x_500 = x_516;
goto block_501;
}
}
}
}
else
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_505, 1);
lean_inc(x_517);
lean_dec_ref(x_505);
x_518 = lean_array_get_size(x_517);
x_519 = lean_nat_dec_lt(x_503, x_518);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_517);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_520 = lean_box(0);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
else
{
lean_object* x_522; uint8_t x_523; 
x_522 = lean_box(0);
x_523 = lean_nat_dec_le(x_518, x_518);
if (x_523 == 0)
{
if (x_519 == 0)
{
lean_dec(x_517);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_11;
}
else
{
size_t x_524; size_t x_525; lean_object* x_526; 
x_524 = 0;
x_525 = lean_usize_of_nat(x_518);
lean_inc_ref(x_7);
x_526 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_517, x_524, x_525, x_522, x_7);
lean_dec(x_517);
if (lean_obj_tag(x_526) == 0)
{
lean_dec_ref(x_526);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_11;
}
else
{
x_500 = x_526;
goto block_501;
}
}
}
else
{
size_t x_527; size_t x_528; lean_object* x_529; 
x_527 = 0;
x_528 = lean_usize_of_nat(x_518);
lean_inc_ref(x_7);
x_529 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_517, x_527, x_528, x_522, x_7);
lean_dec(x_517);
if (lean_obj_tag(x_529) == 0)
{
lean_dec_ref(x_529);
lean_dec_ref(x_409);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_11;
}
else
{
x_500 = x_529;
goto block_501;
}
}
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec_ref(x_409);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_530 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
x_531 = lean_apply_2(x_7, x_530, lean_box(0));
x_532 = lean_box(0);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
return x_533;
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
lean_object* x_12; lean_object* x_13; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_447; lean_object* x_448; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_500; uint8_t x_502; lean_object* x_535; uint8_t x_536; 
x_12 = l_Lake_defaultConfigFile;
x_407 = l_Lake_ConfigLang_fileExtension(x_5);
x_408 = l_System_FilePath_addExtension(x_12, x_407);
lean_dec_ref(x_407);
lean_inc_ref(x_2);
x_409 = l_Lake_joinRelative(x_2, x_408);
x_502 = l_System_FilePath_pathExists(x_409);
x_535 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_536 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_536 == 0)
{
goto block_534;
}
else
{
lean_object* x_537; uint8_t x_538; 
x_537 = lean_box(0);
x_538 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_538 == 0)
{
if (x_536 == 0)
{
goto block_534;
}
else
{
size_t x_539; size_t x_540; lean_object* x_541; 
x_539 = 0;
x_540 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_541 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_535, x_539, x_540, x_537, x_1);
if (lean_obj_tag(x_541) == 0)
{
lean_dec_ref(x_541);
goto block_534;
}
else
{
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_541;
}
}
}
else
{
size_t x_542; size_t x_543; lean_object* x_544; 
x_542 = 0;
x_543 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_544 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_535, x_542, x_543, x_537, x_1);
if (lean_obj_tag(x_544) == 0)
{
lean_dec_ref(x_544);
goto block_534;
}
else
{
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_544;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_29:
{
if (x_7 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(x_2);
x_18 = l_Lake_joinRelative(x_2, x_17);
lean_inc_ref(x_18);
x_19 = l_Lake_joinRelative(x_18, x_12);
x_20 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
x_21 = lean_box(1);
x_22 = l_Lean_Options_empty;
x_23 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
x_24 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set(x_24, 4, x_16);
lean_ctor_set(x_24, 5, x_17);
lean_ctor_set(x_24, 6, x_18);
lean_ctor_set(x_24, 7, x_12);
lean_ctor_set(x_24, 8, x_19);
lean_ctor_set(x_24, 9, x_20);
lean_ctor_set(x_24, 10, x_21);
lean_ctor_set(x_24, 11, x_22);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set(x_24, 13, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*14, x_7);
lean_ctor_set_uint8(x_24, sizeof(void*)*14 + 1, x_7);
lean_ctor_set_uint8(x_24, sizeof(void*)*14 + 2, x_7);
x_25 = l_Lean_NameSet_empty;
x_26 = l_Lake_updateManifest(x_24, x_25, x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
block_34:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(x_31);
x_33 = lean_apply_2(x_31, x_32, lean_box(0));
x_13 = x_31;
goto block_29;
}
else
{
lean_dec_ref(x_30);
x_13 = x_31;
goto block_29;
}
}
block_39:
{
switch (x_4) {
case 3:
{
x_30 = x_35;
x_31 = x_36;
goto block_34;
}
case 4:
{
x_30 = x_35;
x_31 = x_36;
goto block_34;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
block_45:
{
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(x_40);
x_44 = lean_apply_2(x_40, x_43, lean_box(0));
x_35 = x_41;
x_36 = x_40;
goto block_39;
}
else
{
x_35 = x_41;
x_36 = x_40;
goto block_39;
}
}
block_118:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(x_2);
x_51 = l_Lake_joinRelative(x_2, x_50);
x_52 = 4;
x_53 = lean_io_prim_handle_mk(x_51, x_52);
lean_dec_ref(x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_56 = lean_io_prim_handle_put_str(x_54, x_55);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec_ref(x_56);
x_57 = l_Lake_toolchainFileName;
lean_inc_ref(x_2);
x_58 = l_Lake_joinRelative(x_2, x_57);
x_59 = lean_string_utf8_byte_size(x_46);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_48);
x_62 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
x_63 = lean_string_append(x_46, x_62);
x_64 = l_IO_FS_writeFile(x_58, x_63);
lean_dec_ref(x_63);
lean_dec_ref(x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_35 = x_47;
x_36 = x_49;
goto block_39;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_77; 
lean_dec(x_47);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_65 = lean_ctor_get(x_64, 0);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
x_66 = x_64;
x_67 = x_77;
goto block_76;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_io_error_to_string(x_65);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_apply_2(x_49, x_70, lean_box(0));
x_72 = lean_box(0);
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_72);
x_73 = x_66;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec_ref(x_46);
x_78 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_78);
lean_dec_ref(x_48);
x_79 = lean_string_utf8_byte_size(x_78);
lean_dec_ref(x_78);
x_80 = lean_nat_dec_eq(x_79, x_60);
if (x_80 == 0)
{
uint8_t x_81; lean_object* x_82; uint8_t x_83; 
x_81 = l_System_FilePath_pathExists(x_58);
lean_dec_ref(x_58);
x_82 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_83 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_83 == 0)
{
x_40 = x_49;
x_41 = x_47;
x_42 = x_81;
goto block_45;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_box(0);
x_85 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_85 == 0)
{
if (x_83 == 0)
{
x_40 = x_49;
x_41 = x_47;
x_42 = x_81;
goto block_45;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; 
x_86 = 0;
x_87 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_49);
x_88 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_82, x_86, x_87, x_84, x_49);
if (lean_obj_tag(x_88) == 0)
{
lean_dec_ref(x_88);
x_40 = x_49;
x_41 = x_47;
x_42 = x_81;
goto block_45;
}
else
{
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_88;
}
}
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_49);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_82, x_89, x_90, x_84, x_49);
if (lean_obj_tag(x_91) == 0)
{
lean_dec_ref(x_91);
x_40 = x_49;
x_41 = x_47;
x_42 = x_81;
goto block_45;
}
else
{
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_91;
}
}
}
}
else
{
lean_dec_ref(x_58);
x_35 = x_47;
x_36 = x_49;
goto block_39;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_104; 
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_92 = lean_ctor_get(x_56, 0);
x_104 = !lean_is_exclusive(x_56);
if (x_104 == 0)
{
x_93 = x_56;
x_94 = x_104;
goto block_103;
}
else
{
lean_inc(x_92);
lean_dec(x_56);
x_93 = lean_box(0);
x_94 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_io_error_to_string(x_92);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_apply_2(x_49, x_97, lean_box(0));
x_99 = lean_box(0);
if (x_94 == 0)
{
lean_ctor_set(x_93, 0, x_99);
x_100 = x_93;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_99);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_117; 
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_105 = lean_ctor_get(x_53, 0);
x_117 = !lean_is_exclusive(x_53);
if (x_117 == 0)
{
x_106 = x_53;
x_107 = x_117;
goto block_116;
}
else
{
lean_inc(x_105);
lean_dec(x_53);
x_106 = lean_box(0);
x_107 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_io_error_to_string(x_105);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_apply_2(x_49, x_110, lean_box(0));
x_112 = lean_box(0);
if (x_107 == 0)
{
lean_ctor_set(x_106, 0, x_112);
x_113 = x_106;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
block_125:
{
lean_object* x_123; lean_object* x_124; 
x_123 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(x_122);
x_124 = lean_apply_2(x_122, x_123, lean_box(0));
x_46 = x_119;
x_47 = x_120;
x_48 = x_121;
x_49 = x_122;
goto block_118;
}
block_131:
{
if (lean_obj_tag(x_130) == 0)
{
lean_dec_ref(x_130);
x_46 = x_126;
x_47 = x_127;
x_48 = x_128;
x_49 = x_129;
goto block_118;
}
else
{
lean_dec_ref(x_130);
x_119 = x_126;
x_120 = x_127;
x_121 = x_128;
x_122 = x_129;
goto block_125;
}
}
block_163:
{
lean_object* x_136; uint8_t x_137; 
x_136 = l_Lake_Git_upstreamBranch;
x_137 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_unsigned_to_nat(0u);
x_139 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_2);
x_140 = l_Lake_GitRepo_checkoutBranch(x_136, x_2, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_array_get_size(x_141);
x_143 = lean_nat_dec_lt(x_138, x_142);
if (x_143 == 0)
{
lean_dec(x_141);
x_46 = x_132;
x_47 = x_133;
x_48 = x_134;
x_49 = x_135;
goto block_118;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_box(0);
x_145 = lean_nat_dec_le(x_142, x_142);
if (x_145 == 0)
{
if (x_143 == 0)
{
lean_dec(x_141);
x_46 = x_132;
x_47 = x_133;
x_48 = x_134;
x_49 = x_135;
goto block_118;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; 
x_146 = 0;
x_147 = lean_usize_of_nat(x_142);
lean_inc_ref(x_135);
x_148 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_141, x_146, x_147, x_144, x_135);
lean_dec(x_141);
if (lean_obj_tag(x_148) == 0)
{
lean_dec_ref(x_148);
x_46 = x_132;
x_47 = x_133;
x_48 = x_134;
x_49 = x_135;
goto block_118;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_148;
goto block_131;
}
}
}
else
{
size_t x_149; size_t x_150; lean_object* x_151; 
x_149 = 0;
x_150 = lean_usize_of_nat(x_142);
lean_inc_ref(x_135);
x_151 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_141, x_149, x_150, x_144, x_135);
lean_dec(x_141);
if (lean_obj_tag(x_151) == 0)
{
lean_dec_ref(x_151);
x_46 = x_132;
x_47 = x_133;
x_48 = x_134;
x_49 = x_135;
goto block_118;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_151;
goto block_131;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_140, 1);
lean_inc(x_152);
lean_dec_ref(x_140);
x_153 = lean_array_get_size(x_152);
x_154 = lean_nat_dec_lt(x_138, x_153);
if (x_154 == 0)
{
lean_dec(x_152);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_box(0);
x_156 = lean_nat_dec_le(x_153, x_153);
if (x_156 == 0)
{
if (x_154 == 0)
{
lean_dec(x_152);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_153);
lean_inc_ref(x_135);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_152, x_157, x_158, x_155, x_135);
lean_dec(x_152);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_159;
goto block_131;
}
}
}
else
{
size_t x_160; size_t x_161; lean_object* x_162; 
x_160 = 0;
x_161 = lean_usize_of_nat(x_153);
lean_inc_ref(x_135);
x_162 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_152, x_160, x_161, x_155, x_135);
lean_dec(x_152);
if (lean_obj_tag(x_162) == 0)
{
lean_dec_ref(x_162);
x_119 = x_132;
x_120 = x_133;
x_121 = x_134;
x_122 = x_135;
goto block_125;
}
else
{
x_126 = x_132;
x_127 = x_133;
x_128 = x_134;
x_129 = x_135;
x_130 = x_162;
goto block_131;
}
}
}
}
}
else
{
x_46 = x_132;
x_47 = x_133;
x_48 = x_134;
x_49 = x_135;
goto block_118;
}
}
block_169:
{
if (lean_obj_tag(x_168) == 0)
{
lean_dec_ref(x_168);
x_132 = x_164;
x_133 = x_165;
x_134 = x_166;
x_135 = x_167;
goto block_163;
}
else
{
lean_dec_ref(x_168);
x_119 = x_164;
x_120 = x_165;
x_121 = x_166;
x_122 = x_167;
goto block_125;
}
}
block_200:
{
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_unsigned_to_nat(0u);
x_176 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_2);
x_177 = l_Lake_GitRepo_quietInit(x_2, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = lean_array_get_size(x_178);
x_180 = lean_nat_dec_lt(x_175, x_179);
if (x_180 == 0)
{
lean_dec(x_178);
x_132 = x_170;
x_133 = x_171;
x_134 = x_172;
x_135 = x_173;
goto block_163;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_box(0);
x_182 = lean_nat_dec_le(x_179, x_179);
if (x_182 == 0)
{
if (x_180 == 0)
{
lean_dec(x_178);
x_132 = x_170;
x_133 = x_171;
x_134 = x_172;
x_135 = x_173;
goto block_163;
}
else
{
size_t x_183; size_t x_184; lean_object* x_185; 
x_183 = 0;
x_184 = lean_usize_of_nat(x_179);
lean_inc_ref(x_173);
x_185 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_178, x_183, x_184, x_181, x_173);
lean_dec(x_178);
if (lean_obj_tag(x_185) == 0)
{
lean_dec_ref(x_185);
x_132 = x_170;
x_133 = x_171;
x_134 = x_172;
x_135 = x_173;
goto block_163;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_185;
goto block_169;
}
}
}
else
{
size_t x_186; size_t x_187; lean_object* x_188; 
x_186 = 0;
x_187 = lean_usize_of_nat(x_179);
lean_inc_ref(x_173);
x_188 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_178, x_186, x_187, x_181, x_173);
lean_dec(x_178);
if (lean_obj_tag(x_188) == 0)
{
lean_dec_ref(x_188);
x_132 = x_170;
x_133 = x_171;
x_134 = x_172;
x_135 = x_173;
goto block_163;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_188;
goto block_169;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = lean_ctor_get(x_177, 1);
lean_inc(x_189);
lean_dec_ref(x_177);
x_190 = lean_array_get_size(x_189);
x_191 = lean_nat_dec_lt(x_175, x_190);
if (x_191 == 0)
{
lean_dec(x_189);
x_119 = x_170;
x_120 = x_171;
x_121 = x_172;
x_122 = x_173;
goto block_125;
}
else
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_box(0);
x_193 = lean_nat_dec_le(x_190, x_190);
if (x_193 == 0)
{
if (x_191 == 0)
{
lean_dec(x_189);
x_119 = x_170;
x_120 = x_171;
x_121 = x_172;
x_122 = x_173;
goto block_125;
}
else
{
size_t x_194; size_t x_195; lean_object* x_196; 
x_194 = 0;
x_195 = lean_usize_of_nat(x_190);
lean_inc_ref(x_173);
x_196 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_189, x_194, x_195, x_192, x_173);
lean_dec(x_189);
if (lean_obj_tag(x_196) == 0)
{
lean_dec_ref(x_196);
x_119 = x_170;
x_120 = x_171;
x_121 = x_172;
x_122 = x_173;
goto block_125;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_196;
goto block_169;
}
}
}
else
{
size_t x_197; size_t x_198; lean_object* x_199; 
x_197 = 0;
x_198 = lean_usize_of_nat(x_190);
lean_inc_ref(x_173);
x_199 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_189, x_197, x_198, x_192, x_173);
lean_dec(x_189);
if (lean_obj_tag(x_199) == 0)
{
lean_dec_ref(x_199);
x_119 = x_170;
x_120 = x_171;
x_121 = x_172;
x_122 = x_173;
goto block_125;
}
else
{
x_164 = x_170;
x_165 = x_171;
x_166 = x_172;
x_167 = x_173;
x_168 = x_199;
goto block_169;
}
}
}
}
}
else
{
x_46 = x_170;
x_47 = x_171;
x_48 = x_172;
x_49 = x_173;
goto block_118;
}
}
block_216:
{
uint8_t x_205; lean_object* x_206; uint8_t x_207; 
lean_inc_ref(x_2);
x_205 = l_Lake_GitRepo_insideWorkTree(x_2);
x_206 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_207 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_207 == 0)
{
x_170 = x_201;
x_171 = x_202;
x_172 = x_203;
x_173 = x_204;
x_174 = x_205;
goto block_200;
}
else
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_box(0);
x_209 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_209 == 0)
{
if (x_207 == 0)
{
x_170 = x_201;
x_171 = x_202;
x_172 = x_203;
x_173 = x_204;
x_174 = x_205;
goto block_200;
}
else
{
size_t x_210; size_t x_211; lean_object* x_212; 
x_210 = 0;
x_211 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_204);
x_212 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_206, x_210, x_211, x_208, x_204);
if (lean_obj_tag(x_212) == 0)
{
lean_dec_ref(x_212);
x_170 = x_201;
x_171 = x_202;
x_172 = x_203;
x_173 = x_204;
x_174 = x_205;
goto block_200;
}
else
{
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_212;
}
}
}
else
{
size_t x_213; size_t x_214; lean_object* x_215; 
x_213 = 0;
x_214 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_204);
x_215 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_206, x_213, x_214, x_208, x_204);
if (lean_obj_tag(x_215) == 0)
{
lean_dec_ref(x_215);
x_170 = x_201;
x_171 = x_202;
x_172 = x_203;
x_173 = x_204;
x_174 = x_205;
goto block_200;
}
else
{
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_215;
}
}
}
}
block_237:
{
lean_object* x_223; 
x_223 = l_IO_FS_writeFile(x_218, x_222);
lean_dec_ref(x_222);
lean_dec_ref(x_218);
if (lean_obj_tag(x_223) == 0)
{
lean_dec_ref(x_223);
x_201 = x_219;
x_202 = x_220;
x_203 = x_221;
x_204 = x_217;
goto block_216;
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_236; 
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_224 = lean_ctor_get(x_223, 0);
x_236 = !lean_is_exclusive(x_223);
if (x_236 == 0)
{
x_225 = x_223;
x_226 = x_236;
goto block_235;
}
else
{
lean_inc(x_224);
lean_dec(x_223);
x_225 = lean_box(0);
x_226 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_io_error_to_string(x_224);
x_228 = 3;
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_228);
x_230 = lean_apply_2(x_217, x_229, lean_box(0));
x_231 = lean_box(0);
if (x_226 == 0)
{
lean_ctor_set(x_225, 0, x_231);
x_232 = x_225;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_231);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
}
}
}
}
block_250:
{
if (x_243 == 0)
{
uint8_t x_244; uint8_t x_245; 
x_244 = 4;
x_245 = l_Lake_instDecidableEqInitTemplate(x_4, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_247 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_246);
lean_dec_ref(x_246);
x_217 = x_238;
x_218 = x_239;
x_219 = x_240;
x_220 = x_241;
x_221 = x_242;
x_222 = x_247;
goto block_237;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_249 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_248);
lean_dec_ref(x_248);
x_217 = x_238;
x_218 = x_239;
x_219 = x_240;
x_220 = x_241;
x_221 = x_242;
x_222 = x_249;
goto block_237;
}
}
else
{
lean_dec_ref(x_239);
lean_dec(x_3);
x_201 = x_240;
x_202 = x_241;
x_203 = x_242;
x_204 = x_238;
goto block_216;
}
}
block_268:
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(x_2);
x_256 = l_Lake_joinRelative(x_2, x_255);
x_257 = l_System_FilePath_pathExists(x_256);
x_258 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_259 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_259 == 0)
{
x_238 = x_254;
x_239 = x_256;
x_240 = x_251;
x_241 = x_252;
x_242 = x_253;
x_243 = x_257;
goto block_250;
}
else
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_box(0);
x_261 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_261 == 0)
{
if (x_259 == 0)
{
x_238 = x_254;
x_239 = x_256;
x_240 = x_251;
x_241 = x_252;
x_242 = x_253;
x_243 = x_257;
goto block_250;
}
else
{
size_t x_262; size_t x_263; lean_object* x_264; 
x_262 = 0;
x_263 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_254);
x_264 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_258, x_262, x_263, x_260, x_254);
if (lean_obj_tag(x_264) == 0)
{
lean_dec_ref(x_264);
x_238 = x_254;
x_239 = x_256;
x_240 = x_251;
x_241 = x_252;
x_242 = x_253;
x_243 = x_257;
goto block_250;
}
else
{
lean_dec_ref(x_256);
lean_dec_ref(x_254);
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_264;
}
}
}
else
{
size_t x_265; size_t x_266; lean_object* x_267; 
x_265 = 0;
x_266 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_254);
x_267 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_258, x_265, x_266, x_260, x_254);
if (lean_obj_tag(x_267) == 0)
{
lean_dec_ref(x_267);
x_238 = x_254;
x_239 = x_256;
x_240 = x_251;
x_241 = x_252;
x_242 = x_253;
x_243 = x_257;
goto block_250;
}
else
{
lean_dec_ref(x_256);
lean_dec_ref(x_254);
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_267;
}
}
}
}
block_308:
{
if (x_275 == 0)
{
uint8_t x_276; uint8_t x_277; 
x_276 = 1;
x_277 = l_Lake_instDecidableEqInitTemplate(x_4, x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_272);
x_279 = l_IO_FS_writeFile(x_274, x_278);
lean_dec_ref(x_278);
lean_dec_ref(x_274);
if (lean_obj_tag(x_279) == 0)
{
lean_dec_ref(x_279);
x_251 = x_270;
x_252 = x_271;
x_253 = x_273;
x_254 = x_269;
goto block_268;
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_292; 
lean_dec_ref(x_273);
lean_dec(x_271);
lean_dec_ref(x_270);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_280 = lean_ctor_get(x_279, 0);
x_292 = !lean_is_exclusive(x_279);
if (x_292 == 0)
{
x_281 = x_279;
x_282 = x_292;
goto block_291;
}
else
{
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_box(0);
x_282 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_283 = lean_io_error_to_string(x_280);
x_284 = 3;
x_285 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_284);
x_286 = lean_apply_2(x_269, x_285, lean_box(0));
x_287 = lean_box(0);
if (x_282 == 0)
{
lean_ctor_set(x_281, 0, x_287);
x_288 = x_281;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_287);
x_288 = x_290;
goto block_289;
}
block_289:
{
return x_288;
}
}
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_272);
x_293 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
x_294 = l_IO_FS_writeFile(x_274, x_293);
lean_dec_ref(x_274);
if (lean_obj_tag(x_294) == 0)
{
lean_dec_ref(x_294);
x_251 = x_270;
x_252 = x_271;
x_253 = x_273;
x_254 = x_269;
goto block_268;
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_307; 
lean_dec_ref(x_273);
lean_dec(x_271);
lean_dec_ref(x_270);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_295 = lean_ctor_get(x_294, 0);
x_307 = !lean_is_exclusive(x_294);
if (x_307 == 0)
{
x_296 = x_294;
x_297 = x_307;
goto block_306;
}
else
{
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_box(0);
x_297 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_io_error_to_string(x_295);
x_299 = 3;
x_300 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set_uint8(x_300, sizeof(void*)*1, x_299);
x_301 = lean_apply_2(x_269, x_300, lean_box(0));
x_302 = lean_box(0);
if (x_297 == 0)
{
lean_ctor_set(x_296, 0, x_302);
x_303 = x_296;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_302);
x_303 = x_305;
goto block_304;
}
block_304:
{
return x_303;
}
}
}
}
}
else
{
lean_dec_ref(x_274);
lean_dec(x_272);
x_251 = x_270;
x_252 = x_271;
x_253 = x_273;
x_254 = x_269;
goto block_268;
}
}
block_327:
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; 
x_314 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_2);
x_315 = l_Lake_joinRelative(x_2, x_314);
x_316 = l_System_FilePath_pathExists(x_315);
x_317 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_318 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_318 == 0)
{
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_312;
x_273 = x_313;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_box(0);
x_320 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_320 == 0)
{
if (x_318 == 0)
{
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_312;
x_273 = x_313;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
size_t x_321; size_t x_322; lean_object* x_323; 
x_321 = 0;
x_322 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_309);
x_323 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_317, x_321, x_322, x_319, x_309);
if (lean_obj_tag(x_323) == 0)
{
lean_dec_ref(x_323);
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_312;
x_273 = x_313;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
lean_dec_ref(x_315);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_323;
}
}
}
else
{
size_t x_324; size_t x_325; lean_object* x_326; 
x_324 = 0;
x_325 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_309);
x_326 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_317, x_324, x_325, x_319, x_309);
if (lean_obj_tag(x_326) == 0)
{
lean_dec_ref(x_326);
x_269 = x_309;
x_270 = x_310;
x_271 = x_311;
x_272 = x_312;
x_273 = x_313;
x_274 = x_315;
x_275 = x_316;
goto block_308;
}
else
{
lean_dec_ref(x_315);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_326;
}
}
}
}
block_333:
{
switch (x_4) {
case 0:
{
x_309 = x_332;
x_310 = x_328;
x_311 = x_329;
x_312 = x_330;
x_313 = x_331;
goto block_327;
}
case 1:
{
x_309 = x_332;
x_310 = x_328;
x_311 = x_329;
x_312 = x_330;
x_313 = x_331;
goto block_327;
}
default: 
{
lean_dec(x_330);
x_251 = x_328;
x_252 = x_329;
x_253 = x_331;
x_254 = x_332;
goto block_268;
}
}
}
block_355:
{
lean_object* x_341; 
x_341 = l_IO_FS_writeFile(x_339, x_340);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
if (lean_obj_tag(x_341) == 0)
{
lean_dec_ref(x_341);
x_328 = x_335;
x_329 = x_336;
x_330 = x_337;
x_331 = x_338;
x_332 = x_334;
goto block_333;
}
else
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_354; 
lean_dec_ref(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_342 = lean_ctor_get(x_341, 0);
x_354 = !lean_is_exclusive(x_341);
if (x_354 == 0)
{
x_343 = x_341;
x_344 = x_354;
goto block_353;
}
else
{
lean_inc(x_342);
lean_dec(x_341);
x_343 = lean_box(0);
x_344 = x_354;
goto block_353;
}
block_353:
{
lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_io_error_to_string(x_342);
x_346 = 3;
x_347 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*1, x_346);
x_348 = lean_apply_2(x_334, x_347, lean_box(0));
x_349 = lean_box(0);
if (x_344 == 0)
{
lean_ctor_set(x_343, 0, x_349);
x_350 = x_343;
goto block_351;
}
else
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_349);
x_350 = x_352;
goto block_351;
}
block_351:
{
return x_350;
}
}
}
}
block_368:
{
uint8_t x_362; uint8_t x_363; 
x_362 = 4;
x_363 = l_Lake_instDecidableEqInitTemplate(x_4, x_362);
if (x_363 == 0)
{
uint8_t x_364; lean_object* x_365; lean_object* x_366; 
x_364 = 1;
lean_inc(x_358);
x_365 = l_Lean_Name_toString(x_358, x_364);
lean_inc(x_358);
x_366 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_365, x_358);
lean_dec_ref(x_365);
x_334 = x_361;
x_335 = x_356;
x_336 = x_357;
x_337 = x_358;
x_338 = x_359;
x_339 = x_360;
x_340 = x_366;
goto block_355;
}
else
{
lean_object* x_367; 
lean_inc(x_358);
x_367 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_358);
x_334 = x_361;
x_335 = x_356;
x_336 = x_357;
x_337 = x_358;
x_338 = x_359;
x_339 = x_360;
x_340 = x_367;
goto block_355;
}
}
block_406:
{
if (x_376 == 0)
{
lean_object* x_377; 
x_377 = l_IO_FS_createDirAll(x_370);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; 
lean_dec_ref(x_377);
x_378 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
x_379 = l_IO_FS_writeFile(x_369, x_378);
lean_dec_ref(x_369);
if (lean_obj_tag(x_379) == 0)
{
lean_dec_ref(x_379);
x_356 = x_371;
x_357 = x_372;
x_358 = x_373;
x_359 = x_374;
x_360 = x_375;
x_361 = x_1;
goto block_368;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_392; 
lean_dec_ref(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_380 = lean_ctor_get(x_379, 0);
x_392 = !lean_is_exclusive(x_379);
if (x_392 == 0)
{
x_381 = x_379;
x_382 = x_392;
goto block_391;
}
else
{
lean_inc(x_380);
lean_dec(x_379);
x_381 = lean_box(0);
x_382 = x_392;
goto block_391;
}
block_391:
{
lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_383 = lean_io_error_to_string(x_380);
x_384 = 3;
x_385 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set_uint8(x_385, sizeof(void*)*1, x_384);
x_386 = lean_apply_2(x_1, x_385, lean_box(0));
x_387 = lean_box(0);
if (x_382 == 0)
{
lean_ctor_set(x_381, 0, x_387);
x_388 = x_381;
goto block_389;
}
else
{
lean_object* x_390; 
x_390 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_390, 0, x_387);
x_388 = x_390;
goto block_389;
}
block_389:
{
return x_388;
}
}
}
}
else
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_405; 
lean_dec_ref(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec_ref(x_369);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_393 = lean_ctor_get(x_377, 0);
x_405 = !lean_is_exclusive(x_377);
if (x_405 == 0)
{
x_394 = x_377;
x_395 = x_405;
goto block_404;
}
else
{
lean_inc(x_393);
lean_dec(x_377);
x_394 = lean_box(0);
x_395 = x_405;
goto block_404;
}
block_404:
{
lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_396 = lean_io_error_to_string(x_393);
x_397 = 3;
x_398 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*1, x_397);
x_399 = lean_apply_2(x_1, x_398, lean_box(0));
x_400 = lean_box(0);
if (x_395 == 0)
{
lean_ctor_set(x_394, 0, x_400);
x_401 = x_394;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_400);
x_401 = x_403;
goto block_402;
}
block_402:
{
return x_401;
}
}
}
}
else
{
lean_dec_ref(x_370);
lean_dec_ref(x_369);
x_356 = x_371;
x_357 = x_372;
x_358 = x_373;
x_359 = x_374;
x_360 = x_375;
x_361 = x_1;
goto block_368;
}
}
block_446:
{
lean_object* x_415; lean_object* x_416; 
lean_inc(x_414);
lean_inc(x_411);
lean_inc(x_3);
x_415 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_4, x_5, x_3, x_411, x_414);
x_416 = l_IO_FS_writeFile(x_409, x_415);
lean_dec_ref(x_415);
lean_dec_ref(x_409);
if (lean_obj_tag(x_416) == 0)
{
lean_dec_ref(x_416);
if (lean_obj_tag(x_413) == 1)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; uint8_t x_424; 
x_417 = lean_ctor_get(x_413, 0);
lean_inc(x_417);
lean_dec_ref(x_413);
x_418 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
lean_inc(x_417);
x_419 = l_System_FilePath_withExtension(x_417, x_418);
x_420 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(x_419);
x_421 = l_Lake_joinRelative(x_419, x_420);
x_422 = l_System_FilePath_pathExists(x_421);
x_423 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_424 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_424 == 0)
{
x_369 = x_421;
x_370 = x_419;
x_371 = x_410;
x_372 = x_414;
x_373 = x_411;
x_374 = x_412;
x_375 = x_417;
x_376 = x_422;
goto block_406;
}
else
{
lean_object* x_425; uint8_t x_426; 
x_425 = lean_box(0);
x_426 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_426 == 0)
{
if (x_424 == 0)
{
x_369 = x_421;
x_370 = x_419;
x_371 = x_410;
x_372 = x_414;
x_373 = x_411;
x_374 = x_412;
x_375 = x_417;
x_376 = x_422;
goto block_406;
}
else
{
size_t x_427; size_t x_428; lean_object* x_429; 
x_427 = 0;
x_428 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_429 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_423, x_427, x_428, x_425, x_1);
if (lean_obj_tag(x_429) == 0)
{
lean_dec_ref(x_429);
x_369 = x_421;
x_370 = x_419;
x_371 = x_410;
x_372 = x_414;
x_373 = x_411;
x_374 = x_412;
x_375 = x_417;
x_376 = x_422;
goto block_406;
}
else
{
lean_dec_ref(x_421);
lean_dec_ref(x_419);
lean_dec(x_417);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_429;
}
}
}
else
{
size_t x_430; size_t x_431; lean_object* x_432; 
x_430 = 0;
x_431 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_432 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_423, x_430, x_431, x_425, x_1);
if (lean_obj_tag(x_432) == 0)
{
lean_dec_ref(x_432);
x_369 = x_421;
x_370 = x_419;
x_371 = x_410;
x_372 = x_414;
x_373 = x_411;
x_374 = x_412;
x_375 = x_417;
x_376 = x_422;
goto block_406;
}
else
{
lean_dec_ref(x_421);
lean_dec_ref(x_419);
lean_dec(x_417);
lean_dec(x_414);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_432;
}
}
}
}
else
{
lean_dec(x_413);
x_328 = x_410;
x_329 = x_414;
x_330 = x_411;
x_331 = x_412;
x_332 = x_1;
goto block_333;
}
}
else
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; uint8_t x_445; 
lean_dec(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_433 = lean_ctor_get(x_416, 0);
x_445 = !lean_is_exclusive(x_416);
if (x_445 == 0)
{
x_434 = x_416;
x_435 = x_445;
goto block_444;
}
else
{
lean_inc(x_433);
lean_dec(x_416);
x_434 = lean_box(0);
x_435 = x_445;
goto block_444;
}
block_444:
{
lean_object* x_436; uint8_t x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_io_error_to_string(x_433);
x_437 = 3;
x_438 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*1, x_437);
x_439 = lean_apply_2(x_1, x_438, lean_box(0));
x_440 = lean_box(0);
if (x_435 == 0)
{
lean_ctor_set(x_434, 0, x_440);
x_441 = x_434;
goto block_442;
}
else
{
lean_object* x_443; 
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_440);
x_441 = x_443;
goto block_442;
}
block_442:
{
return x_441;
}
}
}
}
block_455:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_6, 1);
x_450 = lean_ctor_get(x_6, 18);
lean_inc_ref(x_450);
x_451 = l_Lake_ToolchainVer_ofString(x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc_ref(x_452);
lean_dec_ref(x_451);
x_453 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_453, 0, x_452);
lean_inc_ref(x_449);
lean_inc_ref(x_450);
x_410 = x_450;
x_411 = x_447;
x_412 = x_449;
x_413 = x_448;
x_414 = x_453;
goto block_446;
}
else
{
lean_object* x_454; 
lean_dec_ref(x_451);
x_454 = lean_box(0);
lean_inc_ref(x_449);
lean_inc_ref(x_450);
x_410 = x_450;
x_411 = x_447;
x_412 = x_449;
x_413 = x_448;
x_414 = x_454;
goto block_446;
}
}
block_461:
{
if (x_458 == 0)
{
lean_object* x_459; 
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_457);
x_447 = x_456;
x_448 = x_459;
goto block_455;
}
else
{
lean_object* x_460; 
lean_dec_ref(x_457);
x_460 = lean_box(0);
x_447 = x_456;
x_448 = x_460;
goto block_455;
}
}
block_479:
{
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; uint8_t x_469; 
lean_dec_ref(x_462);
lean_inc(x_3);
x_465 = l_Lake_toUpperCamelCase(x_3);
lean_inc(x_465);
x_466 = l_Lean_modToFilePath(x_2, x_465, x_463);
lean_dec_ref(x_463);
x_467 = l_System_FilePath_pathExists(x_466);
x_468 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_469 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_469 == 0)
{
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
lean_object* x_470; uint8_t x_471; 
x_470 = lean_box(0);
x_471 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_471 == 0)
{
if (x_469 == 0)
{
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
size_t x_472; size_t x_473; lean_object* x_474; 
x_472 = 0;
x_473 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_474 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_468, x_472, x_473, x_470, x_1);
if (lean_obj_tag(x_474) == 0)
{
lean_dec_ref(x_474);
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_474;
}
}
}
else
{
size_t x_475; size_t x_476; lean_object* x_477; 
x_475 = 0;
x_476 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_477 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_468, x_475, x_476, x_470, x_1);
if (lean_obj_tag(x_477) == 0)
{
lean_dec_ref(x_477);
x_456 = x_465;
x_457 = x_466;
x_458 = x_467;
goto block_461;
}
else
{
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_477;
}
}
}
}
else
{
lean_object* x_478; 
lean_dec_ref(x_463);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_462);
lean_inc(x_3);
x_447 = x_3;
x_448 = x_478;
goto block_455;
}
}
block_485:
{
uint8_t x_483; uint8_t x_484; 
x_483 = 1;
x_484 = l_Lake_instDecidableEqInitTemplate(x_4, x_483);
if (x_484 == 0)
{
x_462 = x_480;
x_463 = x_481;
x_464 = x_482;
goto block_479;
}
else
{
x_462 = x_480;
x_463 = x_481;
x_464 = x_484;
goto block_479;
}
}
block_499:
{
lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; uint8_t x_490; 
x_486 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(x_3);
x_487 = l_Lean_modToFilePath(x_2, x_3, x_486);
x_488 = l_System_FilePath_pathExists(x_487);
x_489 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
x_490 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (x_490 == 0)
{
x_480 = x_487;
x_481 = x_486;
x_482 = x_488;
goto block_485;
}
else
{
lean_object* x_491; uint8_t x_492; 
x_491 = lean_box(0);
x_492 = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (x_492 == 0)
{
if (x_490 == 0)
{
x_480 = x_487;
x_481 = x_486;
x_482 = x_488;
goto block_485;
}
else
{
size_t x_493; size_t x_494; lean_object* x_495; 
x_493 = 0;
x_494 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_495 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_489, x_493, x_494, x_491, x_1);
if (lean_obj_tag(x_495) == 0)
{
lean_dec_ref(x_495);
x_480 = x_487;
x_481 = x_486;
x_482 = x_488;
goto block_485;
}
else
{
lean_dec_ref(x_487);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_495;
}
}
}
else
{
size_t x_496; size_t x_497; lean_object* x_498; 
x_496 = 0;
x_497 = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(x_1);
x_498 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_489, x_496, x_497, x_491, x_1);
if (lean_obj_tag(x_498) == 0)
{
lean_dec_ref(x_498);
x_480 = x_487;
x_481 = x_486;
x_482 = x_488;
goto block_485;
}
else
{
lean_dec_ref(x_487);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_498;
}
}
}
}
block_501:
{
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
goto block_499;
}
else
{
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_500;
}
}
block_534:
{
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_unsigned_to_nat(0u);
x_504 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_2);
x_505 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_2, x_4, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec_ref(x_505);
x_507 = lean_array_get_size(x_506);
x_508 = lean_nat_dec_lt(x_503, x_507);
if (x_508 == 0)
{
lean_dec(x_506);
goto block_499;
}
else
{
lean_object* x_509; uint8_t x_510; 
x_509 = lean_box(0);
x_510 = lean_nat_dec_le(x_507, x_507);
if (x_510 == 0)
{
if (x_508 == 0)
{
lean_dec(x_506);
goto block_499;
}
else
{
size_t x_511; size_t x_512; lean_object* x_513; 
x_511 = 0;
x_512 = lean_usize_of_nat(x_507);
lean_inc_ref(x_1);
x_513 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_506, x_511, x_512, x_509, x_1);
lean_dec(x_506);
if (lean_obj_tag(x_513) == 0)
{
lean_dec_ref(x_513);
goto block_499;
}
else
{
x_500 = x_513;
goto block_501;
}
}
}
else
{
size_t x_514; size_t x_515; lean_object* x_516; 
x_514 = 0;
x_515 = lean_usize_of_nat(x_507);
lean_inc_ref(x_1);
x_516 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_506, x_514, x_515, x_509, x_1);
lean_dec(x_506);
if (lean_obj_tag(x_516) == 0)
{
lean_dec_ref(x_516);
goto block_499;
}
else
{
x_500 = x_516;
goto block_501;
}
}
}
}
else
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_505, 1);
lean_inc(x_517);
lean_dec_ref(x_505);
x_518 = lean_array_get_size(x_517);
x_519 = lean_nat_dec_lt(x_503, x_518);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_517);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_520 = lean_box(0);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
else
{
lean_object* x_522; uint8_t x_523; 
x_522 = lean_box(0);
x_523 = lean_nat_dec_le(x_518, x_518);
if (x_523 == 0)
{
if (x_519 == 0)
{
lean_dec(x_517);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_11;
}
else
{
size_t x_524; size_t x_525; lean_object* x_526; 
x_524 = 0;
x_525 = lean_usize_of_nat(x_518);
lean_inc_ref(x_1);
x_526 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_517, x_524, x_525, x_522, x_1);
lean_dec(x_517);
if (lean_obj_tag(x_526) == 0)
{
lean_dec_ref(x_526);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_11;
}
else
{
x_500 = x_526;
goto block_501;
}
}
}
else
{
size_t x_527; size_t x_528; lean_object* x_529; 
x_527 = 0;
x_528 = lean_usize_of_nat(x_518);
lean_inc_ref(x_1);
x_529 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_517, x_527, x_528, x_522, x_1);
lean_dec(x_517);
if (lean_obj_tag(x_529) == 0)
{
lean_dec_ref(x_529);
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_11;
}
else
{
x_500 = x_529;
goto block_501;
}
}
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec_ref(x_409);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_530 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
x_531 = lean_apply_2(x_1, x_530, lean_box(0));
x_532 = lean_box(0);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
return x_533;
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
lean_object* x_12; lean_object* x_30; lean_object* x_31; lean_object* x_33; lean_object* x_69; uint8_t x_70; 
x_69 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
x_70 = lean_string_dec_eq(x_1, x_69);
if (x_70 == 0)
{
x_33 = x_1;
goto block_68;
}
else
{
lean_object* x_71; 
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_71 = lean_io_realpath(x_5);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_89; 
x_72 = lean_ctor_get(x_71, 0);
x_89 = !lean_is_exclusive(x_71);
if (x_89 == 0)
{
x_73 = x_71;
x_74 = x_89;
goto block_88;
}
else
{
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_75; 
lean_inc(x_72);
x_75 = l_System_FilePath_fileName(x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_76 = ((lean_object*)(l_Lake_init___closed__0));
x_77 = lean_string_append(x_76, x_72);
lean_dec(x_72);
x_78 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
x_79 = lean_string_append(x_77, x_78);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_apply_2(x_7, x_81, lean_box(0));
x_83 = lean_box(0);
if (x_74 == 0)
{
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_83);
x_84 = x_73;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_83);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
else
{
lean_object* x_87; 
lean_del_object(x_73);
lean_dec(x_72);
x_87 = lean_ctor_get(x_75, 0);
lean_inc(x_87);
lean_dec_ref(x_75);
x_33 = x_87;
goto block_68;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_102; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_90 = lean_ctor_get(x_71, 0);
x_102 = !lean_is_exclusive(x_71);
if (x_102 == 0)
{
x_91 = x_71;
x_92 = x_102;
goto block_101;
}
else
{
lean_inc(x_90);
lean_dec(x_71);
x_91 = lean_box(0);
x_92 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_io_error_to_string(x_90);
x_94 = 3;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_apply_2(x_7, x_95, lean_box(0));
x_97 = lean_box(0);
if (x_92 == 0)
{
lean_ctor_set(x_91, 0, x_97);
x_98 = x_91;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_97);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_29:
{
lean_object* x_13; 
lean_inc_ref(x_5);
x_13 = l_IO_FS_createDirAll(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = l_Lake_stringToLegalOrSimpleName(x_12);
x_15 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_7, x_5, x_14, x_2, x_3, x_4, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_28; 
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_16 = lean_ctor_get(x_13, 0);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
x_17 = x_13;
x_18 = x_28;
goto block_27;
}
else
{
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_io_error_to_string(x_16);
x_20 = 3;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_apply_2(x_7, x_21, lean_box(0));
x_23 = lean_box(0);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_23);
x_24 = x_17;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
block_32:
{
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_31);
x_12 = x_30;
goto block_29;
}
else
{
lean_dec_ref(x_30);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_31;
}
}
block_68:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_string_utf8_byte_size(x_33);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_String_Slice_trimAscii(x_36);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 2);
lean_inc(x_40);
lean_dec_ref(x_37);
x_41 = lean_string_utf8_extract(x_38, x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
x_42 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_41);
x_43 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_41, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_34, x_45);
if (x_46 == 0)
{
lean_dec(x_44);
x_12 = x_41;
goto block_29;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(0);
x_48 = lean_nat_dec_le(x_45, x_45);
if (x_48 == 0)
{
if (x_46 == 0)
{
lean_dec(x_44);
x_12 = x_41;
goto block_29;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_inc_ref(x_7);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_44, x_49, x_50, x_47, x_7);
lean_dec(x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_51);
x_12 = x_41;
goto block_29;
}
else
{
x_30 = x_41;
x_31 = x_51;
goto block_32;
}
}
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_45);
lean_inc_ref(x_7);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_44, x_52, x_53, x_47, x_7);
lean_dec(x_44);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_12 = x_41;
goto block_29;
}
else
{
x_30 = x_41;
x_31 = x_54;
goto block_32;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_dec_ref(x_43);
x_56 = lean_array_get_size(x_55);
x_57 = lean_nat_dec_lt(x_34, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec_ref(x_41);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_box(0);
x_61 = lean_nat_dec_le(x_56, x_56);
if (x_61 == 0)
{
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec_ref(x_41);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_11;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_56);
lean_inc_ref(x_7);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_55, x_62, x_63, x_60, x_7);
lean_dec(x_55);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
lean_dec_ref(x_41);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_11;
}
else
{
x_30 = x_41;
x_31 = x_64;
goto block_32;
}
}
}
else
{
size_t x_65; size_t x_66; lean_object* x_67; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_56);
lean_inc_ref(x_7);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_55, x_65, x_66, x_60, x_7);
lean_dec(x_55);
if (lean_obj_tag(x_67) == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_41);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_11;
}
else
{
x_30 = x_41;
x_31 = x_67;
goto block_32;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_39; lean_object* x_41; lean_object* x_42; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_String_Slice_trimAscii(x_14);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_string_utf8_extract(x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
x_41 = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(x_19);
x_42 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_19, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_12, x_44);
if (x_45 == 0)
{
lean_dec(x_43);
goto block_38;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_box(0);
x_47 = lean_nat_dec_le(x_44, x_44);
if (x_47 == 0)
{
if (x_45 == 0)
{
lean_dec(x_43);
goto block_38;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_44);
lean_inc_ref(x_7);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_43, x_48, x_49, x_46, x_7);
lean_dec(x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
goto block_38;
}
else
{
x_39 = x_50;
goto block_40;
}
}
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_44);
lean_inc_ref(x_7);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_43, x_51, x_52, x_46, x_7);
lean_dec(x_43);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
goto block_38;
}
else
{
x_39 = x_53;
goto block_40;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec_ref(x_42);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_12, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec_ref(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_box(0);
x_60 = lean_nat_dec_le(x_55, x_55);
if (x_60 == 0)
{
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_11;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_inc_ref(x_7);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_54, x_61, x_62, x_59, x_7);
lean_dec(x_54);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
lean_dec_ref(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_11;
}
else
{
x_39 = x_63;
goto block_40;
}
}
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_55);
lean_inc_ref(x_7);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(x_54, x_64, x_65, x_59, x_7);
lean_dec(x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_dec_ref(x_66);
lean_dec_ref(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_11;
}
else
{
x_39 = x_66;
goto block_40;
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_38:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lake_stringToLegalOrSimpleName(x_19);
lean_inc(x_20);
x_21 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_20);
x_22 = l_Lake_joinRelative(x_5, x_21);
lean_inc_ref(x_22);
x_23 = l_IO_FS_createDirAll(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
x_24 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_7, x_22, x_20, x_2, x_3, x_4, x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_37; 
lean_dec_ref(x_22);
lean_dec(x_20);
lean_dec_ref(x_4);
x_25 = lean_ctor_get(x_23, 0);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
x_26 = x_23;
x_27 = x_37;
goto block_36;
}
else
{
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_io_error_to_string(x_25);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_apply_2(x_7, x_30, lean_box(0));
x_32 = lean_box(0);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_32);
x_33 = x_26;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
block_40:
{
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_39);
goto block_38;
}
else
{
lean_dec_ref(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_39;
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
