// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: public import Lake.Config.Env public import Lake.Load.Manifest public import Lake.Config.Package import Lake.Util.Git import Lake.Reservoir
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": repository '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' has local changes"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": checking out revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": cloning "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value;
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": URL has changed; deleting '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' and cloning again"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = ": URL has changed; you might need to delete '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "' manually"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
extern uint8_t l_System_Platform_isWindows;
lean_object* l_IO_FS_removeDirAll(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedMaterializedDep_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value;
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
extern lean_object* l_System_instInhabitedFilePath_default;
static lean_once_cell_t l_Lake_instInhabitedMaterializedDep_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = ": package not found on Reservoir.\n\n  If the package is on GitHub, you can add a Git source. For example:\n\n    require ...\n      from git \"https://github.com/"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "\n\n  or, if using TOML:\n\n    [[require]]\n    git = \"https://github.com/"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n    ...\n"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\n    rev = "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n    version = "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value;
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "git#"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1;
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Dependency_materialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": Git source not found on Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__0 = (const lean_object*)&l_Lake_Dependency_materialize___closed__0_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": version `"};
static const lean_object* l_Lake_Dependency_materialize___closed__1 = (const lean_object*)&l_Lake_Dependency_materialize___closed__1_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "` not found on Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__2 = (const lean_object*)&l_Lake_Dependency_materialize___closed__2_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = ": could not fetch package versions: this may be a transient error or a bug in Lake or Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__3 = (const lean_object*)&l_Lake_Dependency_materialize___closed__3_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ": using version `"};
static const lean_object* l_Lake_Dependency_materialize___closed__4 = (const lean_object*)&l_Lake_Dependency_materialize___closed__4_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` at revision `"};
static const lean_object* l_Lake_Dependency_materialize___closed__5 = (const lean_object*)&l_Lake_Dependency_materialize___closed__5_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lake_Dependency_materialize___closed__6 = (const lean_object*)&l_Lake_Dependency_materialize___closed__6_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": could not materialize package: this may be a transient error or a bug in Lake or Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__7 = (const lean_object*)&l_Lake_Dependency_materialize___closed__7_value;
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Dependency_materialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerRange_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Dependency_materialize___closed__8 = (const lean_object*)&l_Lake_Dependency_materialize___closed__8_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ": invalid dependency version range: "};
static const lean_object* l_Lake_Dependency_materialize___closed__9 = (const lean_object*)&l_Lake_Dependency_materialize___closed__9_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__10 = (const lean_object*)&l_Lake_Dependency_materialize___closed__10_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageEntry_materialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_PackageEntry_materialize___closed__0 = (const lean_object*)&l_Lake_PackageEntry_materialize___closed__0_value;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(x_5, x_8);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_36; lean_object* x_37; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = l_Lake_Git_defaultRemote;
x_105 = lean_unsigned_to_nat(0u);
x_106 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_2);
x_107 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_104, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_137; uint8_t x_138; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_137 = lean_array_get_size(x_109);
x_138 = lean_nat_dec_lt(x_105, x_137);
if (x_138 == 0)
{
lean_dec(x_109);
goto block_136;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_box(0);
x_140 = lean_nat_dec_le(x_137, x_137);
if (x_140 == 0)
{
if (x_138 == 0)
{
lean_dec(x_109);
goto block_136;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
x_141 = 0;
x_142 = lean_usize_of_nat(x_137);
lean_inc_ref(x_4);
x_143 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_141, x_142, x_139, x_4);
lean_dec(x_109);
if (lean_obj_tag(x_143) == 0)
{
lean_dec_ref(x_143);
goto block_136;
}
else
{
lean_dec(x_108);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_143;
}
}
}
else
{
size_t x_144; size_t x_145; lean_object* x_146; 
x_144 = 0;
x_145 = lean_usize_of_nat(x_137);
lean_inc_ref(x_4);
x_146 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_144, x_145, x_139, x_4);
lean_dec(x_109);
if (lean_obj_tag(x_146) == 0)
{
lean_dec_ref(x_146);
goto block_136;
}
else
{
lean_dec(x_108);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_146;
}
}
}
block_136:
{
lean_object* x_110; 
lean_inc_ref(x_2);
x_110 = l_Lake_GitRepo_getHeadRevision(x_2, x_106);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = lean_array_get_size(x_112);
x_114 = lean_nat_dec_lt(x_105, x_113);
if (x_114 == 0)
{
lean_dec(x_112);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_box(0);
x_116 = lean_nat_dec_le(x_113, x_113);
if (x_116 == 0)
{
if (x_114 == 0)
{
lean_dec(x_112);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_113);
lean_inc_ref(x_4);
x_119 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_112, x_117, x_118, x_115, x_4);
lean_dec(x_112);
if (lean_obj_tag(x_119) == 0)
{
lean_dec_ref(x_119);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
lean_dec(x_111);
lean_dec(x_108);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_119;
}
}
}
else
{
size_t x_120; size_t x_121; lean_object* x_122; 
x_120 = 0;
x_121 = lean_usize_of_nat(x_113);
lean_inc_ref(x_4);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_112, x_120, x_121, x_115, x_4);
lean_dec(x_112);
if (lean_obj_tag(x_122) == 0)
{
lean_dec_ref(x_122);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
lean_dec(x_111);
lean_dec(x_108);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_108);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_110, 1);
lean_inc(x_123);
lean_dec_ref(x_110);
x_124 = lean_array_get_size(x_123);
x_125 = lean_nat_dec_lt(x_105, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_123);
lean_dec_ref(x_4);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_box(0);
x_129 = lean_nat_dec_le(x_124, x_124);
if (x_129 == 0)
{
if (x_125 == 0)
{
lean_dec(x_123);
lean_dec_ref(x_4);
goto block_100;
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; 
x_130 = 0;
x_131 = lean_usize_of_nat(x_124);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_123, x_130, x_131, x_128, x_4);
lean_dec(x_123);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
goto block_100;
}
else
{
return x_132;
}
}
}
else
{
size_t x_133; size_t x_134; lean_object* x_135; 
x_133 = 0;
x_134 = lean_usize_of_nat(x_124);
x_135 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_123, x_133, x_134, x_128, x_4);
lean_dec(x_123);
if (lean_obj_tag(x_135) == 0)
{
lean_dec_ref(x_135);
goto block_100;
}
else
{
return x_135;
}
}
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_147 = lean_ctor_get(x_107, 1);
lean_inc(x_147);
lean_dec_ref(x_107);
x_148 = lean_array_get_size(x_147);
x_149 = lean_nat_dec_lt(x_105, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec_ref(x_4);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_box(0);
x_153 = lean_nat_dec_le(x_148, x_148);
if (x_153 == 0)
{
if (x_149 == 0)
{
lean_dec(x_147);
lean_dec_ref(x_4);
goto block_103;
}
else
{
size_t x_154; size_t x_155; lean_object* x_156; 
x_154 = 0;
x_155 = lean_usize_of_nat(x_148);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_147, x_154, x_155, x_152, x_4);
lean_dec(x_147);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
goto block_103;
}
else
{
return x_156;
}
}
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_148);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_147, x_157, x_158, x_152, x_4);
lean_dec(x_147);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
goto block_103;
}
else
{
return x_159;
}
}
}
}
block_18:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
x_10 = lean_string_append(x_1, x_9);
x_11 = lean_string_append(x_10, x_2);
lean_dec_ref(x_2);
x_12 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = 2;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_apply_2(x_4, x_15, lean_box(0));
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
block_32:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get_size(x_19);
x_23 = lean_nat_dec_lt(x_20, x_22);
if (x_23 == 0)
{
lean_dec_ref(x_19);
x_6 = x_21;
goto block_18;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
if (x_23 == 0)
{
lean_dec_ref(x_19);
x_6 = x_21;
goto block_18;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_22);
lean_inc_ref(x_4);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_19, x_26, x_27, x_24, x_4);
lean_dec_ref(x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_28);
x_6 = x_21;
goto block_18;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_22);
lean_inc_ref(x_4);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_19, x_29, x_30, x_24, x_4);
lean_dec_ref(x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_31);
x_6 = x_21;
goto block_18;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_31;
}
}
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
block_97:
{
uint8_t x_38; 
x_38 = lean_string_dec_eq(x_37, x_36);
lean_dec_ref(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_40 = lean_string_append(x_1, x_39);
x_41 = lean_string_append(x_40, x_36);
x_42 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_43 = lean_string_append(x_41, x_42);
x_44 = 1;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
lean_inc_ref(x_4);
x_46 = lean_apply_2(x_4, x_45, lean_box(0));
x_47 = lean_unsigned_to_nat(0u);
x_48 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_49 = l_Lake_GitRepo_checkoutDetach(x_36, x_2, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_array_get_size(x_51);
x_53 = lean_nat_dec_lt(x_47, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec_ref(x_4);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_50);
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_box(0);
x_56 = lean_nat_dec_le(x_52, x_52);
if (x_56 == 0)
{
if (x_53 == 0)
{
lean_object* x_57; 
lean_dec(x_51);
lean_dec_ref(x_4);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_50);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_52);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_51, x_58, x_59, x_55, x_4);
lean_dec(x_51);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_67; 
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_60, 0);
lean_dec(x_68);
x_61 = x_60;
x_62 = x_67;
goto block_66;
}
else
{
lean_dec(x_60);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_50);
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_50);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
else
{
lean_dec(x_50);
return x_60;
}
}
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_52);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_51, x_69, x_70, x_55, x_4);
lean_dec(x_51);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_71, 0);
lean_dec(x_79);
x_72 = x_71;
x_73 = x_78;
goto block_77;
}
else
{
lean_dec(x_71);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_50);
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_50);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
else
{
lean_dec(x_50);
return x_71;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_49, 1);
lean_inc(x_80);
lean_dec_ref(x_49);
x_81 = lean_array_get_size(x_80);
x_82 = lean_nat_dec_lt(x_47, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec_ref(x_4);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_box(0);
x_86 = lean_nat_dec_le(x_81, x_81);
if (x_86 == 0)
{
if (x_82 == 0)
{
lean_dec(x_80);
lean_dec_ref(x_4);
goto block_35;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_81);
x_89 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_80, x_87, x_88, x_85, x_4);
lean_dec(x_80);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
goto block_35;
}
else
{
return x_89;
}
}
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_81);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_80, x_90, x_91, x_85, x_4);
lean_dec(x_80);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
goto block_35;
}
else
{
return x_92;
}
}
}
}
}
else
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_36);
lean_inc_ref(x_2);
x_93 = l_Lake_GitRepo_hasNoDiff(x_2);
x_94 = lean_unsigned_to_nat(0u);
x_95 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (x_93 == 0)
{
x_19 = x_95;
x_20 = x_94;
x_21 = x_38;
goto block_32;
}
else
{
uint8_t x_96; 
x_96 = 0;
x_19 = x_95;
x_20 = x_94;
x_21 = x_96;
goto block_32;
}
}
}
block_100:
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
block_103:
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1_spec__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_10; lean_object* x_108; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(x_1);
x_114 = lean_string_append(x_1, x_113);
x_115 = lean_string_append(x_114, x_3);
x_116 = 1;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
lean_inc_ref(x_5);
x_118 = lean_apply_2(x_5, x_117, lean_box(0));
x_119 = lean_unsigned_to_nat(0u);
x_120 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_2);
x_121 = l_Lake_GitRepo_clone(x_3, x_2, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_array_get_size(x_122);
x_124 = lean_nat_dec_lt(x_119, x_123);
if (x_124 == 0)
{
lean_dec(x_122);
goto block_107;
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_box(0);
x_126 = lean_nat_dec_le(x_123, x_123);
if (x_126 == 0)
{
if (x_124 == 0)
{
lean_dec(x_122);
goto block_107;
}
else
{
size_t x_127; size_t x_128; lean_object* x_129; 
x_127 = 0;
x_128 = lean_usize_of_nat(x_123);
lean_inc_ref(x_5);
x_129 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_122, x_127, x_128, x_125, x_5);
lean_dec(x_122);
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
goto block_107;
}
else
{
x_108 = x_129;
goto block_109;
}
}
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; 
x_130 = 0;
x_131 = lean_usize_of_nat(x_123);
lean_inc_ref(x_5);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_122, x_130, x_131, x_125, x_5);
lean_dec(x_122);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
goto block_107;
}
else
{
x_108 = x_132;
goto block_109;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
lean_dec_ref(x_121);
x_134 = lean_array_get_size(x_133);
x_135 = lean_nat_dec_lt(x_119, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_133);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_box(0);
x_139 = lean_nat_dec_le(x_134, x_134);
if (x_139 == 0)
{
if (x_135 == 0)
{
lean_dec(x_133);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_112;
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_134);
lean_inc_ref(x_5);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_133, x_140, x_141, x_138, x_5);
lean_dec(x_133);
if (lean_obj_tag(x_142) == 0)
{
lean_dec_ref(x_142);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_112;
}
else
{
x_108 = x_142;
goto block_109;
}
}
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; 
x_143 = 0;
x_144 = lean_usize_of_nat(x_134);
lean_inc_ref(x_5);
x_145 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_133, x_143, x_144, x_138, x_5);
lean_dec(x_133);
if (lean_obj_tag(x_145) == 0)
{
lean_dec_ref(x_145);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_112;
}
else
{
x_108 = x_145;
goto block_109;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_65:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_12 = lean_string_append(x_1, x_11);
x_13 = lean_string_append(x_12, x_10);
x_14 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_15 = lean_string_append(x_13, x_14);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
lean_inc_ref(x_5);
x_18 = lean_apply_2(x_5, x_17, lean_box(0));
x_19 = lean_unsigned_to_nat(0u);
x_20 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_21 = l_Lake_GitRepo_checkoutDetach(x_10, x_2, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_19, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec_ref(x_5);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_box(0);
x_28 = lean_nat_dec_le(x_24, x_24);
if (x_28 == 0)
{
if (x_25 == 0)
{
lean_object* x_29; 
lean_dec(x_23);
lean_dec_ref(x_5);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_22);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_24);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_23, x_30, x_31, x_27, x_5);
lean_dec(x_23);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; uint8_t x_39; 
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_33 = x_32;
x_34 = x_39;
goto block_38;
}
else
{
lean_dec(x_32);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_22);
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_22);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_dec(x_22);
return x_32;
}
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_24);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_23, x_41, x_42, x_27, x_5);
lean_dec(x_23);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_44 = x_43;
x_45 = x_50;
goto block_49;
}
else
{
lean_dec(x_43);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_22);
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_22);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
else
{
lean_dec(x_22);
return x_43;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_dec_ref(x_21);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_19, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
lean_dec_ref(x_5);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_box(0);
x_58 = lean_nat_dec_le(x_53, x_53);
if (x_58 == 0)
{
if (x_54 == 0)
{
lean_dec(x_52);
lean_dec_ref(x_5);
goto block_9;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_53);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_52, x_59, x_60, x_57, x_5);
lean_dec(x_52);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
goto block_9;
}
else
{
return x_61;
}
}
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_53);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_52, x_62, x_63, x_57, x_5);
lean_dec(x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
goto block_9;
}
else
{
return x_64;
}
}
}
}
}
block_68:
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
block_107:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_104; 
x_69 = lean_ctor_get(x_4, 0);
x_104 = !lean_is_exclusive(x_4);
if (x_104 == 0)
{
x_70 = x_4;
x_71 = x_104;
goto block_103;
}
else
{
lean_inc(x_69);
lean_dec(x_4);
x_70 = lean_box(0);
x_71 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lake_Git_defaultRemote;
x_73 = lean_unsigned_to_nat(0u);
x_74 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_2);
x_75 = l_Lake_GitRepo_resolveRemoteRevision(x_69, x_72, x_2, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_del_object(x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_array_get_size(x_77);
x_79 = lean_nat_dec_lt(x_73, x_78);
if (x_79 == 0)
{
lean_dec(x_77);
x_10 = x_76;
goto block_65;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_box(0);
x_81 = lean_nat_dec_le(x_78, x_78);
if (x_81 == 0)
{
if (x_79 == 0)
{
lean_dec(x_77);
x_10 = x_76;
goto block_65;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_78);
lean_inc_ref(x_5);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_77, x_82, x_83, x_80, x_5);
lean_dec(x_77);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
x_10 = x_76;
goto block_65;
}
else
{
lean_dec(x_76);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_84;
}
}
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_78);
lean_inc_ref(x_5);
x_87 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_77, x_85, x_86, x_80, x_5);
lean_dec(x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_dec_ref(x_87);
x_10 = x_76;
goto block_65;
}
else
{
lean_dec(x_76);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_75, 1);
lean_inc(x_88);
lean_dec_ref(x_75);
x_89 = lean_array_get_size(x_88);
x_90 = lean_nat_dec_lt(x_73, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_88);
lean_dec_ref(x_5);
x_91 = lean_box(0);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_91);
x_92 = x_70;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
else
{
lean_object* x_95; uint8_t x_96; 
lean_del_object(x_70);
x_95 = lean_box(0);
x_96 = lean_nat_dec_le(x_89, x_89);
if (x_96 == 0)
{
if (x_90 == 0)
{
lean_dec(x_88);
lean_dec_ref(x_5);
goto block_68;
}
else
{
size_t x_97; size_t x_98; lean_object* x_99; 
x_97 = 0;
x_98 = lean_usize_of_nat(x_89);
x_99 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_88, x_97, x_98, x_95, x_5);
lean_dec(x_88);
if (lean_obj_tag(x_99) == 0)
{
lean_dec_ref(x_99);
goto block_68;
}
else
{
return x_99;
}
}
}
else
{
size_t x_100; size_t x_101; lean_object* x_102; 
x_100 = 0;
x_101 = lean_usize_of_nat(x_89);
x_102 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_88, x_100, x_101, x_95, x_5);
lean_dec(x_88);
if (lean_obj_tag(x_102) == 0)
{
lean_dec_ref(x_102);
goto block_68;
}
else
{
return x_102;
}
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
block_109:
{
if (lean_obj_tag(x_108) == 0)
{
lean_dec_ref(x_108);
goto block_107;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_108;
}
}
block_112:
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_10; lean_object* x_108; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(x_2);
x_114 = lean_string_append(x_2, x_113);
x_115 = lean_string_append(x_114, x_4);
x_116 = 1;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
lean_inc_ref(x_1);
x_118 = lean_apply_2(x_1, x_117, lean_box(0));
x_119 = lean_unsigned_to_nat(0u);
x_120 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_3);
x_121 = l_Lake_GitRepo_clone(x_4, x_3, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_array_get_size(x_122);
x_124 = lean_nat_dec_lt(x_119, x_123);
if (x_124 == 0)
{
lean_dec(x_122);
goto block_107;
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_box(0);
x_126 = lean_nat_dec_le(x_123, x_123);
if (x_126 == 0)
{
if (x_124 == 0)
{
lean_dec(x_122);
goto block_107;
}
else
{
size_t x_127; size_t x_128; lean_object* x_129; 
x_127 = 0;
x_128 = lean_usize_of_nat(x_123);
lean_inc_ref(x_1);
x_129 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_122, x_127, x_128, x_125, x_1);
lean_dec(x_122);
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
goto block_107;
}
else
{
x_108 = x_129;
goto block_109;
}
}
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; 
x_130 = 0;
x_131 = lean_usize_of_nat(x_123);
lean_inc_ref(x_1);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_122, x_130, x_131, x_125, x_1);
lean_dec(x_122);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
goto block_107;
}
else
{
x_108 = x_132;
goto block_109;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
lean_dec_ref(x_121);
x_134 = lean_array_get_size(x_133);
x_135 = lean_nat_dec_lt(x_119, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_133);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_box(0);
x_139 = lean_nat_dec_le(x_134, x_134);
if (x_139 == 0)
{
if (x_135 == 0)
{
lean_dec(x_133);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_112;
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_134);
lean_inc_ref(x_1);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_133, x_140, x_141, x_138, x_1);
lean_dec(x_133);
if (lean_obj_tag(x_142) == 0)
{
lean_dec_ref(x_142);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_112;
}
else
{
x_108 = x_142;
goto block_109;
}
}
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; 
x_143 = 0;
x_144 = lean_usize_of_nat(x_134);
lean_inc_ref(x_1);
x_145 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_133, x_143, x_144, x_138, x_1);
lean_dec(x_133);
if (lean_obj_tag(x_145) == 0)
{
lean_dec_ref(x_145);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_112;
}
else
{
x_108 = x_145;
goto block_109;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_65:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_12 = lean_string_append(x_2, x_11);
x_13 = lean_string_append(x_12, x_10);
x_14 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_15 = lean_string_append(x_13, x_14);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
lean_inc_ref(x_1);
x_18 = lean_apply_2(x_1, x_17, lean_box(0));
x_19 = lean_unsigned_to_nat(0u);
x_20 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_21 = l_Lake_GitRepo_checkoutDetach(x_10, x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_19, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec_ref(x_1);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_box(0);
x_28 = lean_nat_dec_le(x_24, x_24);
if (x_28 == 0)
{
if (x_25 == 0)
{
lean_object* x_29; 
lean_dec(x_23);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_22);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_24);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_23, x_30, x_31, x_27, x_1);
lean_dec(x_23);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; uint8_t x_39; 
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_33 = x_32;
x_34 = x_39;
goto block_38;
}
else
{
lean_dec(x_32);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_22);
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_22);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_dec(x_22);
return x_32;
}
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_24);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_23, x_41, x_42, x_27, x_1);
lean_dec(x_23);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_44 = x_43;
x_45 = x_50;
goto block_49;
}
else
{
lean_dec(x_43);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_22);
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_22);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
else
{
lean_dec(x_22);
return x_43;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_dec_ref(x_21);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_19, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
lean_dec_ref(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_box(0);
x_58 = lean_nat_dec_le(x_53, x_53);
if (x_58 == 0)
{
if (x_54 == 0)
{
lean_dec(x_52);
lean_dec_ref(x_1);
goto block_9;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_53);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_52, x_59, x_60, x_57, x_1);
lean_dec(x_52);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
goto block_9;
}
else
{
return x_61;
}
}
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_53);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_52, x_62, x_63, x_57, x_1);
lean_dec(x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
goto block_9;
}
else
{
return x_64;
}
}
}
}
}
block_68:
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
block_107:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_104; 
x_69 = lean_ctor_get(x_5, 0);
x_104 = !lean_is_exclusive(x_5);
if (x_104 == 0)
{
x_70 = x_5;
x_71 = x_104;
goto block_103;
}
else
{
lean_inc(x_69);
lean_dec(x_5);
x_70 = lean_box(0);
x_71 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lake_Git_defaultRemote;
x_73 = lean_unsigned_to_nat(0u);
x_74 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_3);
x_75 = l_Lake_GitRepo_resolveRemoteRevision(x_69, x_72, x_3, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_del_object(x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_array_get_size(x_77);
x_79 = lean_nat_dec_lt(x_73, x_78);
if (x_79 == 0)
{
lean_dec(x_77);
x_10 = x_76;
goto block_65;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_box(0);
x_81 = lean_nat_dec_le(x_78, x_78);
if (x_81 == 0)
{
if (x_79 == 0)
{
lean_dec(x_77);
x_10 = x_76;
goto block_65;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_78);
lean_inc_ref(x_1);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_77, x_82, x_83, x_80, x_1);
lean_dec(x_77);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
x_10 = x_76;
goto block_65;
}
else
{
lean_dec(x_76);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_84;
}
}
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_78);
lean_inc_ref(x_1);
x_87 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_77, x_85, x_86, x_80, x_1);
lean_dec(x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_dec_ref(x_87);
x_10 = x_76;
goto block_65;
}
else
{
lean_dec(x_76);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_75, 1);
lean_inc(x_88);
lean_dec_ref(x_75);
x_89 = lean_array_get_size(x_88);
x_90 = lean_nat_dec_lt(x_73, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_88);
lean_dec_ref(x_1);
x_91 = lean_box(0);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_91);
x_92 = x_70;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
else
{
lean_object* x_95; uint8_t x_96; 
lean_del_object(x_70);
x_95 = lean_box(0);
x_96 = lean_nat_dec_le(x_89, x_89);
if (x_96 == 0)
{
if (x_90 == 0)
{
lean_dec(x_88);
lean_dec_ref(x_1);
goto block_68;
}
else
{
size_t x_97; size_t x_98; lean_object* x_99; 
x_97 = 0;
x_98 = lean_usize_of_nat(x_89);
x_99 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_88, x_97, x_98, x_95, x_1);
lean_dec(x_88);
if (lean_obj_tag(x_99) == 0)
{
lean_dec_ref(x_99);
goto block_68;
}
else
{
return x_99;
}
}
}
else
{
size_t x_100; size_t x_101; lean_object* x_102; 
x_100 = 0;
x_101 = lean_usize_of_nat(x_89);
x_102 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_88, x_100, x_101, x_95, x_1);
lean_dec(x_88);
if (lean_obj_tag(x_102) == 0)
{
lean_dec_ref(x_102);
goto block_68;
}
else
{
return x_102;
}
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
block_109:
{
if (lean_obj_tag(x_108) == 0)
{
lean_dec_ref(x_108);
goto block_107;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_108;
}
}
block_112:
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_36; lean_object* x_37; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = l_Lake_Git_defaultRemote;
x_105 = lean_unsigned_to_nat(0u);
x_106 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_3);
x_107 = l_Lake_GitRepo_findRemoteRevision(x_3, x_4, x_104, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_137; uint8_t x_138; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_137 = lean_array_get_size(x_109);
x_138 = lean_nat_dec_lt(x_105, x_137);
if (x_138 == 0)
{
lean_dec(x_109);
goto block_136;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_box(0);
x_140 = lean_nat_dec_le(x_137, x_137);
if (x_140 == 0)
{
if (x_138 == 0)
{
lean_dec(x_109);
goto block_136;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
x_141 = 0;
x_142 = lean_usize_of_nat(x_137);
lean_inc_ref(x_1);
x_143 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_141, x_142, x_139, x_1);
lean_dec(x_109);
if (lean_obj_tag(x_143) == 0)
{
lean_dec_ref(x_143);
goto block_136;
}
else
{
lean_dec(x_108);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_143;
}
}
}
else
{
size_t x_144; size_t x_145; lean_object* x_146; 
x_144 = 0;
x_145 = lean_usize_of_nat(x_137);
lean_inc_ref(x_1);
x_146 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_109, x_144, x_145, x_139, x_1);
lean_dec(x_109);
if (lean_obj_tag(x_146) == 0)
{
lean_dec_ref(x_146);
goto block_136;
}
else
{
lean_dec(x_108);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_146;
}
}
}
block_136:
{
lean_object* x_110; 
lean_inc_ref(x_3);
x_110 = l_Lake_GitRepo_getHeadRevision(x_3, x_106);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = lean_array_get_size(x_112);
x_114 = lean_nat_dec_lt(x_105, x_113);
if (x_114 == 0)
{
lean_dec(x_112);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_box(0);
x_116 = lean_nat_dec_le(x_113, x_113);
if (x_116 == 0)
{
if (x_114 == 0)
{
lean_dec(x_112);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_113);
lean_inc_ref(x_1);
x_119 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_112, x_117, x_118, x_115, x_1);
lean_dec(x_112);
if (lean_obj_tag(x_119) == 0)
{
lean_dec_ref(x_119);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
lean_dec(x_111);
lean_dec(x_108);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_119;
}
}
}
else
{
size_t x_120; size_t x_121; lean_object* x_122; 
x_120 = 0;
x_121 = lean_usize_of_nat(x_113);
lean_inc_ref(x_1);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_112, x_120, x_121, x_115, x_1);
lean_dec(x_112);
if (lean_obj_tag(x_122) == 0)
{
lean_dec_ref(x_122);
x_36 = x_108;
x_37 = x_111;
goto block_97;
}
else
{
lean_dec(x_111);
lean_dec(x_108);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_108);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_123 = lean_ctor_get(x_110, 1);
lean_inc(x_123);
lean_dec_ref(x_110);
x_124 = lean_array_get_size(x_123);
x_125 = lean_nat_dec_lt(x_105, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_123);
lean_dec_ref(x_1);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_box(0);
x_129 = lean_nat_dec_le(x_124, x_124);
if (x_129 == 0)
{
if (x_125 == 0)
{
lean_dec(x_123);
lean_dec_ref(x_1);
goto block_100;
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; 
x_130 = 0;
x_131 = lean_usize_of_nat(x_124);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_123, x_130, x_131, x_128, x_1);
lean_dec(x_123);
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
goto block_100;
}
else
{
return x_132;
}
}
}
else
{
size_t x_133; size_t x_134; lean_object* x_135; 
x_133 = 0;
x_134 = lean_usize_of_nat(x_124);
x_135 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_123, x_133, x_134, x_128, x_1);
lean_dec(x_123);
if (lean_obj_tag(x_135) == 0)
{
lean_dec_ref(x_135);
goto block_100;
}
else
{
return x_135;
}
}
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_147 = lean_ctor_get(x_107, 1);
lean_inc(x_147);
lean_dec_ref(x_107);
x_148 = lean_array_get_size(x_147);
x_149 = lean_nat_dec_lt(x_105, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec_ref(x_1);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_box(0);
x_153 = lean_nat_dec_le(x_148, x_148);
if (x_153 == 0)
{
if (x_149 == 0)
{
lean_dec(x_147);
lean_dec_ref(x_1);
goto block_103;
}
else
{
size_t x_154; size_t x_155; lean_object* x_156; 
x_154 = 0;
x_155 = lean_usize_of_nat(x_148);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_147, x_154, x_155, x_152, x_1);
lean_dec(x_147);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
goto block_103;
}
else
{
return x_156;
}
}
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_148);
x_159 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_147, x_157, x_158, x_152, x_1);
lean_dec(x_147);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
goto block_103;
}
else
{
return x_159;
}
}
}
}
block_18:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
x_10 = lean_string_append(x_2, x_9);
x_11 = lean_string_append(x_10, x_3);
lean_dec_ref(x_3);
x_12 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = 2;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_apply_2(x_1, x_15, lean_box(0));
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
block_32:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_19, x_22);
if (x_23 == 0)
{
lean_dec_ref(x_20);
x_6 = x_21;
goto block_18;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
if (x_23 == 0)
{
lean_dec_ref(x_20);
x_6 = x_21;
goto block_18;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_22);
lean_inc_ref(x_1);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_20, x_26, x_27, x_24, x_1);
lean_dec_ref(x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_28);
x_6 = x_21;
goto block_18;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_22);
lean_inc_ref(x_1);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_20, x_29, x_30, x_24, x_1);
lean_dec_ref(x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_31);
x_6 = x_21;
goto block_18;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_31;
}
}
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
block_97:
{
uint8_t x_38; 
x_38 = lean_string_dec_eq(x_37, x_36);
lean_dec_ref(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
x_40 = lean_string_append(x_2, x_39);
x_41 = lean_string_append(x_40, x_36);
x_42 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
x_43 = lean_string_append(x_41, x_42);
x_44 = 1;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
lean_inc_ref(x_1);
x_46 = lean_apply_2(x_1, x_45, lean_box(0));
x_47 = lean_unsigned_to_nat(0u);
x_48 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_49 = l_Lake_GitRepo_checkoutDetach(x_36, x_3, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_array_get_size(x_51);
x_53 = lean_nat_dec_lt(x_47, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec_ref(x_1);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_50);
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_box(0);
x_56 = lean_nat_dec_le(x_52, x_52);
if (x_56 == 0)
{
if (x_53 == 0)
{
lean_object* x_57; 
lean_dec(x_51);
lean_dec_ref(x_1);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_50);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_52);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_51, x_58, x_59, x_55, x_1);
lean_dec(x_51);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_67; 
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_60, 0);
lean_dec(x_68);
x_61 = x_60;
x_62 = x_67;
goto block_66;
}
else
{
lean_dec(x_60);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_50);
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_50);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
else
{
lean_dec(x_50);
return x_60;
}
}
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_52);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_51, x_69, x_70, x_55, x_1);
lean_dec(x_51);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_71, 0);
lean_dec(x_79);
x_72 = x_71;
x_73 = x_78;
goto block_77;
}
else
{
lean_dec(x_71);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_50);
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_50);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
else
{
lean_dec(x_50);
return x_71;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_49, 1);
lean_inc(x_80);
lean_dec_ref(x_49);
x_81 = lean_array_get_size(x_80);
x_82 = lean_nat_dec_lt(x_47, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec_ref(x_1);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_box(0);
x_86 = lean_nat_dec_le(x_81, x_81);
if (x_86 == 0)
{
if (x_82 == 0)
{
lean_dec(x_80);
lean_dec_ref(x_1);
goto block_35;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_81);
x_89 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_80, x_87, x_88, x_85, x_1);
lean_dec(x_80);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
goto block_35;
}
else
{
return x_89;
}
}
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_81);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_80, x_90, x_91, x_85, x_1);
lean_dec(x_80);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
goto block_35;
}
else
{
return x_92;
}
}
}
}
}
else
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_36);
lean_inc_ref(x_3);
x_93 = l_Lake_GitRepo_hasNoDiff(x_3);
x_94 = lean_unsigned_to_nat(0u);
x_95 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (x_93 == 0)
{
x_19 = x_94;
x_20 = x_95;
x_21 = x_38;
goto block_32;
}
else
{
uint8_t x_96; 
x_96 = 0;
x_19 = x_94;
x_20 = x_95;
x_21 = x_96;
goto block_32;
}
}
}
block_100:
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
block_103:
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7(void) {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lake_Git_defaultRemote;
lean_inc_ref(x_2);
x_44 = l_Lake_GitRepo_getRemoteUrl_x3f(x_43, x_2);
x_45 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
lean_dec_ref(x_44);
x_58 = lean_string_dec_eq(x_57, x_3);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_io_realpath(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc_ref(x_3);
x_61 = lean_io_realpath(x_3);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_string_dec_eq(x_60, x_62);
lean_dec(x_62);
lean_dec(x_60);
x_46 = x_63;
goto block_56;
}
else
{
lean_dec_ref(x_61);
lean_dec(x_60);
x_46 = x_58;
goto block_56;
}
}
else
{
lean_dec_ref(x_59);
x_46 = x_58;
goto block_56;
}
}
else
{
lean_dec(x_57);
x_46 = x_58;
goto block_56;
}
}
else
{
uint8_t x_64; 
lean_dec(x_44);
x_64 = 0;
x_46 = x_64;
goto block_56;
}
block_42:
{
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_System_Platform_isWindows;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(x_1);
x_10 = lean_string_append(x_1, x_9);
x_11 = lean_string_append(x_10, x_2);
x_12 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
lean_inc_ref(x_5);
x_16 = lean_apply_2(x_5, x_15, lean_box(0));
x_17 = l_IO_FS_removeDirAll(x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_31; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_17, 0);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
x_20 = x_17;
x_21 = x_31;
goto block_30;
}
else
{
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_io_error_to_string(x_19);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_apply_2(x_5, x_24, lean_box(0));
x_26 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_26);
x_27 = x_20;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_3);
x_32 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(x_1);
x_33 = lean_string_append(x_1, x_32);
x_34 = lean_string_append(x_33, x_2);
x_35 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
x_36 = lean_string_append(x_34, x_35);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
lean_inc_ref(x_5);
x_39 = lean_apply_2(x_5, x_38, lean_box(0));
x_40 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec_ref(x_3);
x_41 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_41;
}
}
block_56:
{
uint8_t x_47; 
x_47 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_47 == 0)
{
x_7 = x_46;
goto block_42;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(0);
x_49 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_49 == 0)
{
if (x_47 == 0)
{
x_7 = x_46;
goto block_42;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_45, x_50, x_51, x_48, x_5);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_7 = x_46;
goto block_42;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_52;
}
}
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_45, x_53, x_54, x_48, x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_7 = x_46;
goto block_42;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lake_Git_defaultRemote;
lean_inc_ref(x_3);
x_44 = l_Lake_GitRepo_getRemoteUrl_x3f(x_43, x_3);
x_45 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
lean_dec_ref(x_44);
x_58 = lean_string_dec_eq(x_57, x_4);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_io_realpath(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc_ref(x_4);
x_61 = lean_io_realpath(x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_string_dec_eq(x_60, x_62);
lean_dec(x_62);
lean_dec(x_60);
x_46 = x_63;
goto block_56;
}
else
{
lean_dec_ref(x_61);
lean_dec(x_60);
x_46 = x_58;
goto block_56;
}
}
else
{
lean_dec_ref(x_59);
x_46 = x_58;
goto block_56;
}
}
else
{
lean_dec(x_57);
x_46 = x_58;
goto block_56;
}
}
else
{
uint8_t x_64; 
lean_dec(x_44);
x_64 = 0;
x_46 = x_64;
goto block_56;
}
block_42:
{
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_System_Platform_isWindows;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(x_2);
x_10 = lean_string_append(x_2, x_9);
x_11 = lean_string_append(x_10, x_3);
x_12 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
lean_inc_ref(x_1);
x_16 = lean_apply_2(x_1, x_15, lean_box(0));
x_17 = l_IO_FS_removeDirAll(x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_31; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_17, 0);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
x_20 = x_17;
x_21 = x_31;
goto block_30;
}
else
{
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_io_error_to_string(x_19);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_apply_2(x_1, x_24, lean_box(0));
x_26 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_26);
x_27 = x_20;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_4);
x_32 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(x_2);
x_33 = lean_string_append(x_2, x_32);
x_34 = lean_string_append(x_33, x_3);
x_35 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
x_36 = lean_string_append(x_34, x_35);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
lean_inc_ref(x_1);
x_39 = lean_apply_2(x_1, x_38, lean_box(0));
x_40 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec_ref(x_4);
x_41 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_41;
}
}
block_56:
{
uint8_t x_47; 
x_47 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_47 == 0)
{
x_7 = x_46;
goto block_42;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(0);
x_49 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_49 == 0)
{
if (x_47 == 0)
{
x_7 = x_46;
goto block_42;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_45, x_50, x_51, x_48, x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_7 = x_46;
goto block_42;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_52;
}
}
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_45, x_53, x_54, x_48, x_1);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_7 = x_46;
goto block_42;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_11; uint8_t x_12; 
x_7 = l_System_FilePath_isDir(x_2);
x_11 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_12 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_12 == 0)
{
goto block_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_14 == 0)
{
if (x_12 == 0)
{
goto block_10;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_11, x_15, x_16, x_13, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
goto block_10;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_11, x_18, x_19, x_13, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_20);
goto block_10;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
}
block_10:
{
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instInhabitedPackageEntry_default;
x_2 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_3 = l_System_instInhabitedFilePath_default;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__1, &l_Lake_instInhabitedMaterializedDep_default___closed__1_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedMaterializedDep_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_name(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_scope(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_manifestFile_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_configFile(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
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
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_27; 
x_27 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_4 = x_27;
x_5 = x_27;
goto block_26;
}
case 1:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_43; 
x_28 = lean_ctor_get(x_3, 0);
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
x_29 = x_3;
x_30 = x_43;
goto block_42;
}
else
{
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
x_32 = l_String_quote(x_28);
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 3);
lean_ctor_set(x_29, 0, x_32);
x_33 = x_29;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_33 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Std_Format_defWidth;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Std_Format_pretty(x_33, x_34, x_35, x_35);
x_37 = lean_string_append(x_31, x_36);
x_38 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
x_39 = lean_string_append(x_38, x_36);
lean_dec_ref(x_36);
x_4 = x_37;
x_5 = x_39;
goto block_26;
}
}
}
default: 
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_60; 
x_44 = lean_ctor_get(x_3, 0);
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
x_45 = x_3;
x_46 = x_60;
goto block_59;
}
else
{
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_47);
lean_dec_ref(x_44);
x_48 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
x_49 = l_String_quote(x_47);
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 3);
lean_ctor_set(x_45, 0, x_49);
x_50 = x_45;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_49);
x_50 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = l_Std_Format_defWidth;
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Std_Format_pretty(x_50, x_51, x_52, x_52);
x_54 = lean_string_append(x_48, x_53);
x_55 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
x_56 = lean_string_append(x_55, x_53);
lean_dec_ref(x_53);
x_4 = x_54;
x_5 = x_56;
goto block_26;
}
}
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(x_1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_string_append(x_7, x_2);
x_9 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_1);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_string_append(x_12, x_2);
x_14 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_4);
lean_dec_ref(x_4);
x_17 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec_ref(x_1);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_14);
x_23 = lean_string_append(x_22, x_5);
lean_dec_ref(x_5);
x_24 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
x_25 = lean_string_append(x_23, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lake_defaultConfigFile;
x_9 = lean_box(0);
lean_inc_ref(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_11; uint8_t x_12; 
x_7 = l_System_FilePath_isDir(x_3);
x_11 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_12 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_12 == 0)
{
goto block_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_14 == 0)
{
if (x_12 == 0)
{
goto block_10;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_11, x_15, x_16, x_13, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
goto block_10;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_1);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_11, x_18, x_19, x_13, x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_20);
goto block_10;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
}
block_10:
{
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; lean_object* x_113; 
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_34 = l_Lake_joinRelative(x_4, x_6);
x_113 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_16, x_17);
if (lean_obj_tag(x_113) == 0)
{
x_35 = x_7;
goto block_112;
}
else
{
lean_object* x_114; 
lean_dec_ref(x_7);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_35 = x_114;
goto block_112;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_28:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_9);
lean_ctor_set(x_22, 3, x_10);
x_23 = l_Lake_defaultConfigFile;
x_24 = lean_box(0);
lean_inc_ref(x_18);
lean_inc(x_17);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_2);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_8);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_33:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
x_32 = l_Lake_joinRelative(x_6, x_31);
x_19 = x_29;
x_20 = x_30;
x_21 = x_32;
goto block_28;
}
else
{
x_19 = x_29;
x_20 = x_30;
x_21 = x_6;
goto block_28;
}
}
block_112:
{
lean_object* x_36; 
lean_inc(x_9);
lean_inc_ref(x_35);
lean_inc_ref(x_34);
lean_inc_ref(x_11);
x_36 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_11, x_5, x_34, x_35, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_102; 
x_102 = !lean_is_exclusive(x_36);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_36, 0);
lean_dec(x_103);
x_37 = x_36;
x_38 = x_102;
goto block_101;
}
else
{
lean_dec(x_36);
x_37 = lean_box(0);
x_38 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_41 = l_Lake_GitRepo_getHeadRevision(x_34, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_del_object(x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_39, x_44);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec_ref(x_11);
x_29 = x_35;
x_30 = x_42;
goto block_33;
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
lean_dec_ref(x_11);
x_29 = x_35;
x_30 = x_42;
goto block_33;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_44);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_43, x_48, x_49, x_46, x_11);
lean_dec(x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
x_29 = x_35;
x_30 = x_42;
goto block_33;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_42);
lean_dec_ref(x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_51 = lean_ctor_get(x_50, 0);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
x_52 = x_50;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_44);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_43, x_59, x_60, x_46, x_11);
lean_dec(x_43);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_29 = x_35;
x_30 = x_42;
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_42);
lean_dec_ref(x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec_ref(x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_70 = lean_ctor_get(x_41, 1);
lean_inc(x_70);
lean_dec_ref(x_41);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_39, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
lean_dec_ref(x_11);
x_73 = lean_box(0);
if (x_38 == 0)
{
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_73);
x_74 = x_37;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_del_object(x_37);
x_77 = lean_box(0);
x_78 = lean_nat_dec_le(x_71, x_71);
if (x_78 == 0)
{
if (x_72 == 0)
{
lean_dec(x_70);
lean_dec_ref(x_11);
goto block_15;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_71);
x_81 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_79, x_80, x_77, x_11);
lean_dec(x_70);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
goto block_15;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_71);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_90, x_91, x_77, x_11);
lean_dec(x_70);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
goto block_15;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
x_93 = lean_ctor_get(x_92, 0);
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
x_94 = x_92;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_111; 
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_104 = lean_ctor_get(x_36, 0);
x_111 = !lean_is_exclusive(x_36);
if (x_111 == 0)
{
x_105 = x_36;
x_106 = x_111;
goto block_110;
}
else
{
lean_inc(x_104);
lean_dec(x_36);
x_105 = lean_box(0);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_106 == 0)
{
x_107 = x_105;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; lean_object* x_113; 
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
x_34 = l_Lake_joinRelative(x_5, x_7);
x_113 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_16, x_17);
if (lean_obj_tag(x_113) == 0)
{
x_35 = x_8;
goto block_112;
}
else
{
lean_object* x_114; 
lean_dec_ref(x_8);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_35 = x_114;
goto block_112;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_28:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_11);
x_23 = l_Lake_defaultConfigFile;
x_24 = lean_box(0);
lean_inc_ref(x_18);
lean_inc(x_17);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_3);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_9);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_33:
{
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
x_32 = l_Lake_joinRelative(x_7, x_31);
x_19 = x_30;
x_20 = x_29;
x_21 = x_32;
goto block_28;
}
else
{
x_19 = x_30;
x_20 = x_29;
x_21 = x_7;
goto block_28;
}
}
block_112:
{
lean_object* x_36; 
lean_inc(x_10);
lean_inc_ref(x_35);
lean_inc_ref(x_34);
lean_inc_ref(x_1);
x_36 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_6, x_34, x_35, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_102; 
x_102 = !lean_is_exclusive(x_36);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_36, 0);
lean_dec(x_103);
x_37 = x_36;
x_38 = x_102;
goto block_101;
}
else
{
lean_dec(x_36);
x_37 = lean_box(0);
x_38 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_41 = l_Lake_GitRepo_getHeadRevision(x_34, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_del_object(x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_39, x_44);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec_ref(x_1);
x_29 = x_35;
x_30 = x_42;
goto block_33;
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
lean_dec_ref(x_1);
x_29 = x_35;
x_30 = x_42;
goto block_33;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_44);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_43, x_48, x_49, x_46, x_1);
lean_dec(x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
x_29 = x_35;
x_30 = x_42;
goto block_33;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_42);
lean_dec_ref(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_51 = lean_ctor_get(x_50, 0);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
x_52 = x_50;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_44);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_43, x_59, x_60, x_46, x_1);
lean_dec(x_43);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_29 = x_35;
x_30 = x_42;
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_42);
lean_dec_ref(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec_ref(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_70 = lean_ctor_get(x_41, 1);
lean_inc(x_70);
lean_dec_ref(x_41);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_39, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
lean_dec_ref(x_1);
x_73 = lean_box(0);
if (x_38 == 0)
{
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_73);
x_74 = x_37;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_del_object(x_37);
x_77 = lean_box(0);
x_78 = lean_nat_dec_le(x_71, x_71);
if (x_78 == 0)
{
if (x_72 == 0)
{
lean_dec(x_70);
lean_dec_ref(x_1);
goto block_15;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_71);
x_81 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_79, x_80, x_77, x_1);
lean_dec(x_70);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
goto block_15;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_71);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_70, x_90, x_91, x_77, x_1);
lean_dec(x_70);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
goto block_15;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
x_93 = lean_ctor_get(x_92, 0);
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
x_94 = x_92;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_111; 
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_36, 0);
x_111 = !lean_is_exclusive(x_36);
if (x_111 == 0)
{
x_105 = x_36;
x_106 = x_111;
goto block_110;
}
else
{
lean_inc(x_104);
lean_dec(x_36);
x_105 = lean_box(0);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_106 == 0)
{
x_107 = x_105;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_14;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_memcmp(x_1, x_2, x_7, x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_3);
x_11 = l_String_Slice_pos_x21(x_10, x_4);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_5);
x_7 = lean_array_uget_borrowed(x_2, x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_box(0);
x_10 = l_Lake_VerRange_test(x_1, x_8);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_148; 
x_115 = lean_ctor_get(x_46, 0);
x_148 = !lean_is_exclusive(x_46);
if (x_148 == 0)
{
x_116 = x_46;
x_117 = x_148;
goto block_147;
}
else
{
lean_inc(x_115);
lean_dec(x_46);
x_116 = lean_box(0);
x_117 = x_148;
goto block_147;
}
block_147:
{
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_134; 
lean_inc_ref(x_44);
lean_inc(x_43);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_118 = lean_ctor_get(x_115, 0);
x_134 = !lean_is_exclusive(x_115);
if (x_134 == 0)
{
x_119 = x_115;
x_120 = x_134;
goto block_133;
}
else
{
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_box(0);
x_120 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = l_Lake_joinRelative(x_6, x_118);
x_122 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(x_121);
if (x_120 == 0)
{
lean_ctor_set(x_119, 0, x_121);
x_123 = x_119;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_121);
x_123 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = l_Lake_defaultConfigFile;
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_126, 0, x_43);
lean_ctor_set(x_126, 1, x_44);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_125);
lean_ctor_set(x_126, 4, x_123);
lean_ctor_set_uint8(x_126, sizeof(void*)*5, x_2);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set(x_127, 1, x_122);
lean_ctor_set(x_127, 2, x_126);
if (x_117 == 0)
{
lean_ctor_set_tag(x_116, 0);
lean_ctor_set(x_116, 0, x_127);
x_128 = x_116;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_127);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_144; 
lean_del_object(x_116);
lean_dec_ref(x_6);
x_135 = lean_ctor_get(x_115, 0);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_115, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_115, 2);
lean_inc(x_137);
lean_dec_ref(x_115);
x_138 = 0;
lean_inc(x_43);
x_139 = l_Lean_Name_toString(x_43, x_138);
lean_inc_ref(x_135);
x_144 = l_Lake_Git_filterUrl_x3f(x_135);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_140 = x_145;
goto block_143;
}
else
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec_ref(x_144);
x_140 = x_146;
goto block_143;
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
lean_inc_ref(x_139);
x_141 = l_Lake_joinRelative(x_5, x_139);
x_142 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_139, x_141, x_135, x_140, x_136, x_137);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_142;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_353; lean_object* x_354; 
lean_dec(x_46);
lean_dec_ref(x_6);
x_149 = lean_string_utf8_byte_size(x_44);
x_150 = lean_unsigned_to_nat(0u);
x_353 = lean_nat_dec_eq(x_149, x_150);
if (x_353 == 0)
{
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_45, 0);
lean_inc(x_365);
x_366 = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(x_365);
if (lean_obj_tag(x_366) == 1)
{
lean_object* x_367; lean_object* x_368; uint8_t x_369; uint8_t x_375; 
x_367 = lean_ctor_get(x_366, 0);
x_375 = !lean_is_exclusive(x_366);
if (x_375 == 0)
{
x_368 = x_366;
x_369 = x_375;
goto block_374;
}
else
{
lean_inc(x_367);
lean_dec(x_366);
x_368 = lean_box(0);
x_369 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_370; lean_object* x_371; 
x_370 = l_String_Slice_toString(x_367);
lean_dec(x_367);
if (x_369 == 0)
{
lean_ctor_set(x_368, 0, x_370);
x_371 = x_368;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_370);
x_371 = x_373;
goto block_372;
}
block_372:
{
x_354 = x_371;
goto block_364;
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_366);
x_376 = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
x_377 = lean_string_utf8_byte_size(x_365);
lean_inc(x_365);
x_378 = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), x_365, x_376, x_150, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; uint8_t x_395; 
lean_inc(x_43);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_379 = lean_ctor_get(x_378, 0);
x_395 = !lean_is_exclusive(x_378);
if (x_395 == 0)
{
x_380 = x_378;
x_381 = x_395;
goto block_394;
}
else
{
lean_inc(x_379);
lean_dec(x_378);
x_380 = lean_box(0);
x_381 = x_395;
goto block_394;
}
block_394:
{
uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_382 = 1;
x_383 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_43, x_382);
x_384 = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
x_385 = lean_string_append(x_383, x_384);
x_386 = lean_string_append(x_385, x_379);
lean_dec(x_379);
x_387 = 3;
x_388 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*1, x_387);
x_389 = lean_apply_2(x_7, x_388, lean_box(0));
x_390 = lean_box(0);
if (x_381 == 0)
{
lean_ctor_set_tag(x_380, 1);
lean_ctor_set(x_380, 0, x_390);
x_391 = x_380;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_390);
x_391 = x_393;
goto block_392;
}
block_392:
{
return x_391;
}
}
}
else
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; uint8_t x_403; 
x_396 = lean_ctor_get(x_378, 0);
x_403 = !lean_is_exclusive(x_378);
if (x_403 == 0)
{
x_397 = x_378;
x_398 = x_403;
goto block_402;
}
else
{
lean_inc(x_396);
lean_dec(x_378);
x_397 = lean_box(0);
x_398 = x_403;
goto block_402;
}
block_402:
{
lean_object* x_399; 
if (x_398 == 0)
{
lean_ctor_set_tag(x_397, 2);
x_399 = x_397;
goto block_400;
}
else
{
lean_object* x_401; 
x_401 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_401, 0, x_396);
x_399 = x_401;
goto block_400;
}
block_400:
{
x_354 = x_399;
goto block_364;
}
}
}
}
}
else
{
lean_object* x_404; 
x_404 = lean_box(0);
x_354 = x_404;
goto block_364;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_inc(x_43);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_405 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_43, x_353);
x_406 = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
x_407 = lean_string_append(x_405, x_406);
x_408 = 3;
x_409 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set_uint8(x_409, sizeof(void*)*1, x_408);
x_410 = lean_apply_2(x_7, x_409, lean_box(0));
x_411 = lean_box(0);
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_411);
return x_412;
}
block_186:
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_array_get_size(x_159);
x_161 = lean_nat_dec_lt(x_150, x_160);
if (x_161 == 0)
{
lean_dec_ref(x_159);
x_64 = x_151;
x_65 = x_152;
x_66 = x_153;
x_67 = x_155;
x_68 = x_154;
x_69 = x_156;
x_70 = x_157;
x_71 = x_158;
goto block_114;
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_box(0);
x_163 = lean_nat_dec_le(x_160, x_160);
if (x_163 == 0)
{
if (x_161 == 0)
{
lean_dec_ref(x_159);
x_64 = x_151;
x_65 = x_152;
x_66 = x_153;
x_67 = x_155;
x_68 = x_154;
x_69 = x_156;
x_70 = x_157;
x_71 = x_158;
goto block_114;
}
else
{
size_t x_164; size_t x_165; lean_object* x_166; 
x_164 = 0;
x_165 = lean_usize_of_nat(x_160);
lean_inc_ref(x_7);
x_166 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_159, x_164, x_165, x_162, x_7);
lean_dec_ref(x_159);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_166);
x_64 = x_151;
x_65 = x_152;
x_66 = x_153;
x_67 = x_155;
x_68 = x_154;
x_69 = x_156;
x_70 = x_157;
x_71 = x_158;
goto block_114;
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_174; 
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_167 = lean_ctor_get(x_166, 0);
x_174 = !lean_is_exclusive(x_166);
if (x_174 == 0)
{
x_168 = x_166;
x_169 = x_174;
goto block_173;
}
else
{
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_box(0);
x_169 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_170; 
if (x_169 == 0)
{
x_170 = x_168;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_167);
x_170 = x_172;
goto block_171;
}
block_171:
{
return x_170;
}
}
}
}
}
else
{
size_t x_175; size_t x_176; lean_object* x_177; 
x_175 = 0;
x_176 = lean_usize_of_nat(x_160);
lean_inc_ref(x_7);
x_177 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_159, x_175, x_176, x_162, x_7);
lean_dec_ref(x_159);
if (lean_obj_tag(x_177) == 0)
{
lean_dec_ref(x_177);
x_64 = x_151;
x_65 = x_152;
x_66 = x_153;
x_67 = x_155;
x_68 = x_154;
x_69 = x_156;
x_70 = x_157;
x_71 = x_158;
goto block_114;
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_177, 0);
x_185 = !lean_is_exclusive(x_177);
if (x_185 == 0)
{
x_179 = x_177;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_box(0);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_180 == 0)
{
x_181 = x_179;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
}
}
block_321:
{
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_inc_ref(x_44);
lean_dec_ref(x_189);
lean_dec(x_187);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_190 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
x_191 = lean_string_append(x_44, x_190);
x_192 = lean_string_append(x_191, x_188);
lean_dec_ref(x_188);
x_193 = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
x_194 = lean_string_append(x_192, x_193);
x_195 = 3;
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_195);
x_197 = lean_apply_2(x_7, x_196, lean_box(0));
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_320; 
x_200 = lean_ctor_get(x_189, 0);
x_320 = !lean_is_exclusive(x_189);
if (x_320 == 0)
{
x_201 = x_189;
x_202 = x_320;
goto block_319;
}
else
{
lean_inc(x_200);
lean_dec(x_189);
x_201 = lean_box(0);
x_202 = x_320;
goto block_319;
}
block_319:
{
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_inc_ref(x_44);
lean_del_object(x_201);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_203 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_44, x_188, x_187);
lean_dec_ref(x_188);
x_204 = 3;
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_204);
x_206 = lean_apply_2(x_7, x_205, lean_box(0));
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_200, 0);
lean_inc(x_209);
lean_dec_ref(x_200);
x_210 = l_Lake_RegistryPkg_gitSrc_x3f(x_209);
if (lean_obj_tag(x_210) == 1)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_318; 
x_211 = lean_ctor_get(x_210, 0);
x_318 = !lean_is_exclusive(x_210);
if (x_318 == 0)
{
x_212 = x_210;
x_213 = x_318;
goto block_317;
}
else
{
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_box(0);
x_213 = x_318;
goto block_317;
}
block_317:
{
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_211, 1);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_211, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_211, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_211, 4);
lean_inc(x_217);
lean_dec_ref(x_211);
x_218 = lean_ctor_get(x_209, 0);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_209, 1);
lean_inc_ref(x_219);
lean_dec(x_209);
x_220 = l_Lake_joinRelative(x_5, x_218);
switch (lean_obj_tag(x_187)) {
case 0:
{
lean_object* x_221; 
lean_del_object(x_201);
lean_dec_ref(x_188);
x_221 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_222; 
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_222 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_dec_ref(x_7);
x_223 = lean_box(0);
if (x_213 == 0)
{
lean_ctor_set(x_212, 0, x_223);
x_224 = x_212;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_223);
x_224 = x_226;
goto block_225;
}
block_225:
{
return x_224;
}
}
else
{
lean_object* x_227; uint8_t x_228; 
lean_del_object(x_212);
x_227 = lean_box(0);
x_228 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_228 == 0)
{
if (x_222 == 0)
{
lean_dec_ref(x_7);
goto block_11;
}
else
{
size_t x_229; size_t x_230; lean_object* x_231; 
x_229 = 0;
x_230 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
x_231 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_221, x_229, x_230, x_227, x_7);
if (lean_obj_tag(x_231) == 0)
{
lean_dec_ref(x_231);
goto block_11;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_239; 
x_232 = lean_ctor_get(x_231, 0);
x_239 = !lean_is_exclusive(x_231);
if (x_239 == 0)
{
x_233 = x_231;
x_234 = x_239;
goto block_238;
}
else
{
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_box(0);
x_234 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_235; 
if (x_234 == 0)
{
x_235 = x_233;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_232);
x_235 = x_237;
goto block_236;
}
block_236:
{
return x_235;
}
}
}
}
}
else
{
size_t x_240; size_t x_241; lean_object* x_242; 
x_240 = 0;
x_241 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
x_242 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_221, x_240, x_241, x_227, x_7);
if (lean_obj_tag(x_242) == 0)
{
lean_dec_ref(x_242);
goto block_11;
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_250; 
x_243 = lean_ctor_get(x_242, 0);
x_250 = !lean_is_exclusive(x_242);
if (x_250 == 0)
{
x_244 = x_242;
x_245 = x_250;
goto block_249;
}
else
{
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_box(0);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_245 == 0)
{
x_246 = x_244;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_243);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
}
}
else
{
lean_object* x_251; uint8_t x_252; 
lean_del_object(x_212);
x_251 = lean_ctor_get(x_216, 0);
lean_inc(x_251);
lean_dec_ref(x_216);
x_252 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_252 == 0)
{
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_251;
x_39 = x_7;
goto block_42;
}
else
{
lean_object* x_253; uint8_t x_254; 
x_253 = lean_box(0);
x_254 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_254 == 0)
{
if (x_252 == 0)
{
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_251;
x_39 = x_7;
goto block_42;
}
else
{
size_t x_255; size_t x_256; lean_object* x_257; 
x_255 = 0;
x_256 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_257 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_221, x_255, x_256, x_253, x_7);
if (lean_obj_tag(x_257) == 0)
{
lean_dec_ref(x_257);
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_251;
x_39 = x_7;
goto block_42;
}
else
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_265; 
lean_dec(x_251);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_258 = lean_ctor_get(x_257, 0);
x_265 = !lean_is_exclusive(x_257);
if (x_265 == 0)
{
x_259 = x_257;
x_260 = x_265;
goto block_264;
}
else
{
lean_inc(x_258);
lean_dec(x_257);
x_259 = lean_box(0);
x_260 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_261; 
if (x_260 == 0)
{
x_261 = x_259;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_258);
x_261 = x_263;
goto block_262;
}
block_262:
{
return x_261;
}
}
}
}
}
else
{
size_t x_266; size_t x_267; lean_object* x_268; 
x_266 = 0;
x_267 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_268 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_221, x_266, x_267, x_253, x_7);
if (lean_obj_tag(x_268) == 0)
{
lean_dec_ref(x_268);
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_251;
x_39 = x_7;
goto block_42;
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_276; 
lean_dec(x_251);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_269 = lean_ctor_get(x_268, 0);
x_276 = !lean_is_exclusive(x_268);
if (x_276 == 0)
{
x_270 = x_268;
x_271 = x_276;
goto block_275;
}
else
{
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_box(0);
x_271 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_272; 
if (x_271 == 0)
{
x_272 = x_270;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_269);
x_272 = x_274;
goto block_273;
}
block_273:
{
return x_272;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; 
lean_dec(x_216);
lean_del_object(x_212);
lean_del_object(x_201);
lean_dec_ref(x_188);
x_277 = lean_ctor_get(x_187, 0);
lean_inc_ref(x_277);
lean_dec_ref(x_187);
x_278 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_279 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_279 == 0)
{
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_277;
x_39 = x_7;
goto block_42;
}
else
{
lean_object* x_280; uint8_t x_281; 
x_280 = lean_box(0);
x_281 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_281 == 0)
{
if (x_279 == 0)
{
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_277;
x_39 = x_7;
goto block_42;
}
else
{
size_t x_282; size_t x_283; lean_object* x_284; 
x_282 = 0;
x_283 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_284 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_278, x_282, x_283, x_280, x_7);
if (lean_obj_tag(x_284) == 0)
{
lean_dec_ref(x_284);
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_277;
x_39 = x_7;
goto block_42;
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_292; 
lean_dec_ref(x_277);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_285 = lean_ctor_get(x_284, 0);
x_292 = !lean_is_exclusive(x_284);
if (x_292 == 0)
{
x_286 = x_284;
x_287 = x_292;
goto block_291;
}
else
{
lean_inc(x_285);
lean_dec(x_284);
x_286 = lean_box(0);
x_287 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_288; 
if (x_287 == 0)
{
x_288 = x_286;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_285);
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
}
else
{
size_t x_293; size_t x_294; lean_object* x_295; 
x_293 = 0;
x_294 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_7);
x_295 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_278, x_293, x_294, x_280, x_7);
if (lean_obj_tag(x_295) == 0)
{
lean_dec_ref(x_295);
x_33 = x_217;
x_34 = x_219;
x_35 = x_214;
x_36 = x_215;
x_37 = x_220;
x_38 = x_277;
x_39 = x_7;
goto block_42;
}
else
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; uint8_t x_303; 
lean_dec_ref(x_277);
lean_dec_ref(x_220);
lean_dec_ref(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_296 = lean_ctor_get(x_295, 0);
x_303 = !lean_is_exclusive(x_295);
if (x_303 == 0)
{
x_297 = x_295;
x_298 = x_303;
goto block_302;
}
else
{
lean_inc(x_296);
lean_dec(x_295);
x_297 = lean_box(0);
x_298 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_299; 
if (x_298 == 0)
{
x_299 = x_297;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_296);
x_299 = x_301;
goto block_300;
}
block_300:
{
return x_299;
}
}
}
}
}
}
default: 
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_216);
lean_del_object(x_212);
x_304 = lean_ctor_get(x_187, 0);
lean_inc_ref(x_304);
lean_dec_ref(x_187);
x_305 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_188);
lean_inc_ref(x_44);
lean_inc_ref(x_3);
x_306 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_44, x_188, x_305);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec_ref(x_306);
if (x_202 == 0)
{
lean_ctor_set(x_201, 0, x_307);
x_309 = x_201;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_307);
x_309 = x_311;
goto block_310;
}
block_310:
{
x_151 = x_217;
x_152 = x_219;
x_153 = x_214;
x_154 = x_304;
x_155 = x_215;
x_156 = x_220;
x_157 = x_188;
x_158 = x_309;
x_159 = x_308;
goto block_186;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_306, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_306, 1);
lean_inc(x_313);
lean_dec_ref(x_306);
if (x_202 == 0)
{
lean_ctor_set_tag(x_201, 0);
lean_ctor_set(x_201, 0, x_312);
x_314 = x_201;
goto block_315;
}
else
{
lean_object* x_316; 
x_316 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_316, 0, x_312);
x_314 = x_316;
goto block_315;
}
block_315:
{
x_151 = x_217;
x_152 = x_219;
x_153 = x_214;
x_154 = x_304;
x_155 = x_215;
x_156 = x_220;
x_157 = x_188;
x_158 = x_314;
x_159 = x_313;
goto block_186;
}
}
}
}
}
else
{
lean_del_object(x_212);
lean_dec(x_211);
lean_del_object(x_201);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_12 = x_209;
x_13 = x_7;
goto block_22;
}
}
}
else
{
lean_dec(x_210);
lean_del_object(x_201);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_12 = x_209;
x_13 = x_7;
goto block_22;
}
}
}
}
}
block_352:
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_array_get_size(x_325);
x_327 = lean_nat_dec_lt(x_150, x_326);
if (x_327 == 0)
{
lean_dec_ref(x_325);
x_187 = x_322;
x_188 = x_323;
x_189 = x_324;
goto block_321;
}
else
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_box(0);
x_329 = lean_nat_dec_le(x_326, x_326);
if (x_329 == 0)
{
if (x_327 == 0)
{
lean_dec_ref(x_325);
x_187 = x_322;
x_188 = x_323;
x_189 = x_324;
goto block_321;
}
else
{
size_t x_330; size_t x_331; lean_object* x_332; 
x_330 = 0;
x_331 = lean_usize_of_nat(x_326);
lean_inc_ref(x_7);
x_332 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_325, x_330, x_331, x_328, x_7);
lean_dec_ref(x_325);
if (lean_obj_tag(x_332) == 0)
{
lean_dec_ref(x_332);
x_187 = x_322;
x_188 = x_323;
x_189 = x_324;
goto block_321;
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; uint8_t x_340; 
lean_dec_ref(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_333 = lean_ctor_get(x_332, 0);
x_340 = !lean_is_exclusive(x_332);
if (x_340 == 0)
{
x_334 = x_332;
x_335 = x_340;
goto block_339;
}
else
{
lean_inc(x_333);
lean_dec(x_332);
x_334 = lean_box(0);
x_335 = x_340;
goto block_339;
}
block_339:
{
lean_object* x_336; 
if (x_335 == 0)
{
x_336 = x_334;
goto block_337;
}
else
{
lean_object* x_338; 
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_333);
x_336 = x_338;
goto block_337;
}
block_337:
{
return x_336;
}
}
}
}
}
else
{
size_t x_341; size_t x_342; lean_object* x_343; 
x_341 = 0;
x_342 = lean_usize_of_nat(x_326);
lean_inc_ref(x_7);
x_343 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_325, x_341, x_342, x_328, x_7);
lean_dec_ref(x_325);
if (lean_obj_tag(x_343) == 0)
{
lean_dec_ref(x_343);
x_187 = x_322;
x_188 = x_323;
x_189 = x_324;
goto block_321;
}
else
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_351; 
lean_dec_ref(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_344 = lean_ctor_get(x_343, 0);
x_351 = !lean_is_exclusive(x_343);
if (x_351 == 0)
{
x_345 = x_343;
x_346 = x_351;
goto block_350;
}
else
{
lean_inc(x_344);
lean_dec(x_343);
x_345 = lean_box(0);
x_346 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_347; 
if (x_346 == 0)
{
x_347 = x_345;
goto block_348;
}
else
{
lean_object* x_349; 
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_344);
x_347 = x_349;
goto block_348;
}
block_348:
{
return x_347;
}
}
}
}
}
}
block_364:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_inc(x_43);
x_355 = l_Lean_Name_toString(x_43, x_353);
x_356 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
lean_inc_ref(x_355);
lean_inc_ref(x_44);
lean_inc_ref(x_3);
x_357 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_44, x_355, x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec_ref(x_357);
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_358);
x_322 = x_354;
x_323 = x_355;
x_324 = x_360;
x_325 = x_359;
goto block_352;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_357, 1);
lean_inc(x_362);
lean_dec_ref(x_357);
x_363 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_363, 0, x_361);
x_322 = x_354;
x_323 = x_355;
x_324 = x_363;
x_325 = x_362;
goto block_352;
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
block_22:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
x_16 = lean_string_append(x_14, x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_apply_2(x_13, x_18, lean_box(0));
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_31 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_24, x_28, x_26, x_29, x_30, x_23, x_27);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_31;
}
block_42:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_40; 
x_40 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_23 = x_33;
x_24 = x_34;
x_25 = x_38;
x_26 = x_35;
x_27 = x_39;
x_28 = x_37;
x_29 = x_40;
goto block_32;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec_ref(x_36);
x_23 = x_33;
x_24 = x_34;
x_25 = x_38;
x_26 = x_35;
x_27 = x_39;
x_28 = x_37;
x_29 = x_41;
goto block_32;
}
}
block_63:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_49);
lean_dec_ref(x_47);
x_50 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
x_51 = lean_string_append(x_44, x_50);
x_52 = lean_string_append(x_51, x_48);
lean_dec_ref(x_48);
x_53 = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_string_append(x_54, x_49);
lean_dec_ref(x_49);
x_56 = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
x_57 = lean_string_append(x_55, x_56);
x_58 = 3;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_apply_2(x_7, x_59, lean_box(0));
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
block_114:
{
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; uint8_t x_87; 
lean_inc_ref(x_44);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_71);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_71, 0);
lean_dec(x_88);
x_72 = x_71;
x_73 = x_87;
goto block_86;
}
else
{
lean_dec(x_71);
x_72 = lean_box(0);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
x_75 = lean_string_append(x_44, x_74);
x_76 = lean_string_append(x_75, x_70);
lean_dec_ref(x_70);
x_77 = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
x_78 = lean_string_append(x_76, x_77);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_apply_2(x_7, x_80, lean_box(0));
x_82 = lean_box(0);
if (x_73 == 0)
{
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 0, x_82);
x_83 = x_72;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_82);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_71, 0);
lean_inc(x_89);
lean_dec_ref(x_71);
x_90 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
x_91 = lean_array_size(x_89);
x_92 = 0;
x_93 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_68, x_89, x_91, x_92, x_90);
lean_dec(x_89);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_inc_ref(x_44);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_47 = x_68;
x_48 = x_70;
goto block_63;
}
else
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_68);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc_ref(x_98);
lean_dec(x_96);
x_99 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(x_44);
x_100 = lean_string_append(x_44, x_99);
x_101 = lean_string_append(x_100, x_70);
lean_dec_ref(x_70);
x_102 = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
x_103 = lean_string_append(x_101, x_102);
x_104 = l_Lake_StdVer_toString(x_97);
x_105 = lean_string_append(x_103, x_104);
lean_dec_ref(x_104);
x_106 = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_98);
x_109 = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
x_110 = lean_string_append(x_108, x_109);
x_111 = 1;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
lean_inc_ref(x_7);
x_113 = lean_apply_2(x_7, x_112, lean_box(0));
x_33 = x_64;
x_34 = x_65;
x_35 = x_66;
x_36 = x_67;
x_37 = x_69;
x_38 = x_98;
x_39 = x_7;
goto block_42;
}
else
{
lean_inc_ref(x_44);
lean_dec(x_95);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_47 = x_68;
x_48 = x_70;
goto block_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lake_Dependency_materialize(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_14 = x_12;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_1);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_51; uint8_t x_63; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_103; lean_object* x_104; uint8_t x_115; lean_object* x_148; uint8_t x_149; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_12, 3);
lean_inc(x_26);
lean_dec_ref(x_12);
x_32 = 0;
lean_inc(x_23);
x_33 = l_Lean_Name_toString(x_23, x_32);
lean_inc_ref(x_33);
x_34 = l_Lake_joinRelative(x_4, x_33);
lean_inc_ref(x_34);
x_38 = l_Lake_joinRelative(x_3, x_34);
x_115 = l_System_FilePath_isDir(x_38);
x_148 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_149 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_149 == 0)
{
goto block_147;
}
else
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_box(0);
x_151 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_151 == 0)
{
if (x_149 == 0)
{
goto block_147;
}
else
{
size_t x_152; size_t x_153; lean_object* x_154; 
x_152 = 0;
x_153 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_154 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_148, x_152, x_153, x_150, x_5);
if (lean_obj_tag(x_154) == 0)
{
lean_dec_ref(x_154);
goto block_147;
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_154, 0);
x_162 = !lean_is_exclusive(x_154);
if (x_162 == 0)
{
x_156 = x_154;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
}
else
{
size_t x_163; size_t x_164; lean_object* x_165; 
x_163 = 0;
x_164 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_165 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_148, x_163, x_164, x_150, x_5);
if (lean_obj_tag(x_165) == 0)
{
lean_dec_ref(x_165);
goto block_147;
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_173; 
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_166 = lean_ctor_get(x_165, 0);
x_173 = !lean_is_exclusive(x_165);
if (x_173 == 0)
{
x_167 = x_165;
x_168 = x_173;
goto block_172;
}
else
{
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_box(0);
x_168 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_169; 
if (x_168 == 0)
{
x_169 = x_167;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_166);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
}
}
block_31:
{
lean_object* x_28; 
x_28 = l_Lake_Git_filterUrl_x3f(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
x_7 = x_27;
x_8 = x_29;
goto block_11;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_7 = x_27;
x_8 = x_30;
goto block_11;
}
}
block_37:
{
if (lean_obj_tag(x_26) == 0)
{
x_27 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec_ref(x_26);
x_36 = l_Lake_joinRelative(x_34, x_35);
x_27 = x_36;
goto block_31;
}
}
block_50:
{
lean_object* x_41; 
x_41 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_33, x_38, x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec_ref(x_34);
lean_dec(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_41, 0);
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
x_43 = x_41;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
block_62:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_25);
x_53 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_33, x_38, x_51, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
goto block_37;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec_ref(x_34);
lean_dec(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_53, 0);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
x_55 = x_53;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
block_72:
{
if (x_63 == 0)
{
lean_dec_ref(x_38);
lean_dec_ref(x_33);
lean_dec_ref(x_5);
goto block_37;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_64 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
x_65 = lean_string_append(x_33, x_64);
x_66 = lean_string_append(x_65, x_38);
lean_dec_ref(x_38);
x_67 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
x_68 = lean_string_append(x_66, x_67);
x_69 = 2;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_apply_2(x_5, x_70, lean_box(0));
goto block_37;
}
}
block_102:
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_array_get_size(x_73);
x_77 = lean_nat_dec_lt(x_74, x_76);
if (x_77 == 0)
{
lean_dec_ref(x_73);
x_63 = x_75;
goto block_72;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_box(0);
x_79 = lean_nat_dec_le(x_76, x_76);
if (x_79 == 0)
{
if (x_77 == 0)
{
lean_dec_ref(x_73);
x_63 = x_75;
goto block_72;
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_76);
lean_inc_ref(x_5);
x_82 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_73, x_80, x_81, x_78, x_5);
lean_dec_ref(x_73);
if (lean_obj_tag(x_82) == 0)
{
lean_dec_ref(x_82);
x_63 = x_75;
goto block_72;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_82, 0);
x_90 = !lean_is_exclusive(x_82);
if (x_90 == 0)
{
x_84 = x_82;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
}
else
{
size_t x_91; size_t x_92; lean_object* x_93; 
x_91 = 0;
x_92 = lean_usize_of_nat(x_76);
lean_inc_ref(x_5);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_73, x_91, x_92, x_78, x_5);
lean_dec_ref(x_73);
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_93);
x_63 = x_75;
goto block_72;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_93, 0);
x_101 = !lean_is_exclusive(x_93);
if (x_101 == 0)
{
x_95 = x_93;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
}
}
block_114:
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_25);
lean_inc_ref(x_106);
x_107 = l_Option_instDecidableEq___redArg(x_105, x_104, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_2, 5);
x_109 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_108, x_23);
if (lean_obj_tag(x_109) == 0)
{
lean_inc_ref(x_24);
x_39 = x_106;
x_40 = x_24;
goto block_50;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_39 = x_106;
x_40 = x_110;
goto block_50;
}
}
else
{
uint8_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_106);
lean_inc_ref(x_38);
x_111 = l_Lake_GitRepo_hasNoDiff(x_38);
x_112 = lean_unsigned_to_nat(0u);
x_113 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
if (x_111 == 0)
{
x_73 = x_113;
x_74 = x_112;
x_75 = x_103;
goto block_102;
}
else
{
x_73 = x_113;
x_74 = x_112;
x_75 = x_32;
goto block_102;
}
}
}
block_147:
{
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_2, 5);
x_117 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_116, x_23);
if (lean_obj_tag(x_117) == 0)
{
lean_inc_ref(x_24);
x_51 = x_24;
goto block_62;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_51 = x_118;
goto block_62;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(x_38);
x_120 = l_Lake_GitRepo_resolveRevision_x3f(x_119, x_38);
x_121 = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
x_122 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (x_122 == 0)
{
x_103 = x_115;
x_104 = x_120;
goto block_114;
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_box(0);
x_124 = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (x_124 == 0)
{
if (x_122 == 0)
{
x_103 = x_115;
x_104 = x_120;
goto block_114;
}
else
{
size_t x_125; size_t x_126; lean_object* x_127; 
x_125 = 0;
x_126 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_127 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_121, x_125, x_126, x_123, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_dec_ref(x_127);
x_103 = x_115;
x_104 = x_120;
goto block_114;
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_dec(x_120);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_127, 0);
x_135 = !lean_is_exclusive(x_127);
if (x_135 == 0)
{
x_129 = x_127;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_128);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
else
{
size_t x_136; size_t x_137; lean_object* x_138; 
x_136 = 0;
x_137 = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
lean_inc_ref(x_5);
x_138 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__1(x_121, x_136, x_137, x_123, x_5);
if (lean_obj_tag(x_138) == 0)
{
lean_dec_ref(x_138);
x_103 = x_115;
x_104 = x_120;
goto block_114;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_146; 
lean_dec(x_120);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_139 = lean_ctor_get(x_138, 0);
x_146 = !lean_is_exclusive(x_138);
if (x_146 == 0)
{
x_140 = x_138;
x_141 = x_146;
goto block_145;
}
else
{
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_box(0);
x_141 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_142; 
if (x_141 == 0)
{
x_142 = x_140;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_PackageEntry_materialize(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Reservoir(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Reservoir(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedMaterializedDep_default = _init_l_Lake_instInhabitedMaterializedDep_default();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Reservoir(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Materialize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Materialize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Materialize(builtin);
}
#ifdef __cplusplus
}
#endif
