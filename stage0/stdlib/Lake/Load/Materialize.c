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
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lake_Manifest_load(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
extern lean_object* l_System_instInhabitedFilePath_default;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": repository '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' has local changes"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value;
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": checking out revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": cloning "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedMaterializedDep_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedMaterializedDep_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__1_value;
static const lean_ctor_object l_Lake_instInhabitedMaterializedDep_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__1_value)}};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__2_value;
static const lean_ctor_object l_Lake_instInhabitedMaterializedDep_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__2_value)}};
static const lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedMaterializedDep_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__4;
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
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "git#"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value;
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
static const lean_closure_object l_Lake_Dependency_materialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerRange_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Dependency_materialize___closed__8 = (const lean_object*)&l_Lake_Dependency_materialize___closed__8_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ": invalid dependency version range: "};
static const lean_object* l_Lake_Dependency_materialize___closed__9 = (const lean_object*)&l_Lake_Dependency_materialize___closed__9_value;
static const lean_string_object l_Lake_Dependency_materialize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__10 = (const lean_object*)&l_Lake_Dependency_materialize___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value)}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageEntry_materialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_PackageEntry_materialize___closed__0 = (const lean_object*)&l_Lake_PackageEntry_materialize___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_, lean_object* v___y_5_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; 
v___x_8_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
lean_inc_ref(v___y_5_);
lean_inc(v___x_8_);
v___x_9_ = lean_apply_2(v___y_5_, v___x_8_, lean_box(0));
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_2_, v___x_10_);
v_i_2_ = v___x_11_;
v_b_4_ = v___x_9_;
goto _start;
}
else
{
lean_object* v___x_13_; 
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v_b_4_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_, lean_object* v_b_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
size_t v_i_boxed_20_; size_t v_stop_boxed_21_; lean_object* v_res_22_; 
v_i_boxed_20_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_21_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_22_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_as_14_, v_i_boxed_20_, v_stop_boxed_21_, v_b_17_, v___y_18_);
lean_dec_ref(v___y_18_);
lean_dec_ref(v_as_14_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* v_name_29_, lean_object* v_repo_30_, lean_object* v_rev_x3f_31_, lean_object* v_a_32_){
_start:
{
uint8_t v_a_35_; lean_object* v___y_48_; lean_object* v___y_49_; uint8_t v_val_50_; lean_object* v___y_115_; lean_object* v___y_117_; lean_object* v_a_118_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = l_Lake_Git_defaultRemote;
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_30_);
v___x_168_ = l_Lake_GitRepo_findRemoteRevision(v_repo_30_, v_rev_x3f_31_, v___x_165_, v___x_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_a_170_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
v_a_170_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_170_);
lean_dec_ref(v___x_168_);
v___x_198_ = lean_array_get_size(v_a_170_);
v___x_199_ = lean_nat_dec_lt(v___x_166_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec(v_a_170_);
goto v___jp_171_;
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_box(0);
v___x_201_ = lean_nat_dec_le(v___x_198_, v___x_198_);
if (v___x_201_ == 0)
{
if (v___x_199_ == 0)
{
lean_dec(v_a_170_);
goto v___jp_171_;
}
else
{
size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_198_);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_170_, v___x_202_, v___x_203_, v___x_200_, v_a_32_);
lean_dec(v_a_170_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_dec_ref(v___x_204_);
goto v___jp_171_;
}
else
{
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_204_;
}
}
}
else
{
size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((size_t)0ULL);
v___x_206_ = lean_usize_of_nat(v___x_198_);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_170_, v___x_205_, v___x_206_, v___x_200_, v_a_32_);
lean_dec(v_a_170_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_dec_ref(v___x_207_);
goto v___jp_171_;
}
else
{
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_207_;
}
}
}
v___jp_171_:
{
lean_object* v___x_172_; 
lean_inc_ref(v_repo_30_);
v___x_172_ = l_Lake_GitRepo_getHeadRevision(v_repo_30_, v___x_167_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
v_a_174_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_a_174_);
lean_dec_ref(v___x_172_);
v___x_175_ = lean_array_get_size(v_a_174_);
v___x_176_ = lean_nat_dec_lt(v___x_166_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec(v_a_174_);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_box(0);
v___x_178_ = lean_nat_dec_le(v___x_175_, v___x_175_);
if (v___x_178_ == 0)
{
if (v___x_176_ == 0)
{
lean_dec(v_a_174_);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
size_t v___x_179_; size_t v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((size_t)0ULL);
v___x_180_ = lean_usize_of_nat(v___x_175_);
v___x_181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_174_, v___x_179_, v___x_180_, v___x_177_, v_a_32_);
lean_dec(v_a_174_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_dec_ref(v___x_181_);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
lean_dec(v_a_173_);
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_181_;
}
}
}
else
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)0ULL);
v___x_183_ = lean_usize_of_nat(v___x_175_);
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_174_, v___x_182_, v___x_183_, v___x_177_, v_a_32_);
lean_dec(v_a_174_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_dec_ref(v___x_184_);
v___y_117_ = v_a_169_;
v_a_118_ = v_a_173_;
goto v___jp_116_;
}
else
{
lean_dec(v_a_173_);
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_184_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
lean_dec(v_a_169_);
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v_a_185_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_a_185_);
lean_dec_ref(v___x_172_);
v___x_186_ = lean_array_get_size(v_a_185_);
v___x_187_ = lean_nat_dec_lt(v___x_166_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_a_185_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_box(0);
v___x_191_ = lean_nat_dec_le(v___x_186_, v___x_186_);
if (v___x_191_ == 0)
{
if (v___x_187_ == 0)
{
lean_dec(v_a_185_);
goto v___jp_159_;
}
else
{
size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((size_t)0ULL);
v___x_193_ = lean_usize_of_nat(v___x_186_);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_185_, v___x_192_, v___x_193_, v___x_190_, v_a_32_);
lean_dec(v_a_185_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_dec_ref(v___x_194_);
goto v___jp_159_;
}
else
{
return v___x_194_;
}
}
}
else
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = ((size_t)0ULL);
v___x_196_ = lean_usize_of_nat(v___x_186_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_185_, v___x_195_, v___x_196_, v___x_190_, v_a_32_);
lean_dec(v_a_185_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_dec_ref(v___x_197_);
goto v___jp_159_;
}
else
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v_a_208_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_208_);
lean_dec_ref(v___x_168_);
v___x_209_ = lean_array_get_size(v_a_208_);
v___x_210_ = lean_nat_dec_lt(v___x_166_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_a_208_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_box(0);
v___x_214_ = lean_nat_dec_le(v___x_209_, v___x_209_);
if (v___x_214_ == 0)
{
if (v___x_210_ == 0)
{
lean_dec(v_a_208_);
goto v___jp_162_;
}
else
{
size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((size_t)0ULL);
v___x_216_ = lean_usize_of_nat(v___x_209_);
v___x_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_208_, v___x_215_, v___x_216_, v___x_213_, v_a_32_);
lean_dec(v_a_208_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_dec_ref(v___x_217_);
goto v___jp_162_;
}
else
{
return v___x_217_;
}
}
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_209_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_208_, v___x_218_, v___x_219_, v___x_213_, v_a_32_);
lean_dec(v_a_208_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_dec_ref(v___x_220_);
goto v___jp_162_;
}
else
{
return v___x_220_;
}
}
}
}
v___jp_34_:
{
if (v_a_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_38_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_39_ = lean_string_append(v_name_29_, v___x_38_);
v___x_40_ = lean_string_append(v___x_39_, v_repo_30_);
lean_dec_ref(v_repo_30_);
v___x_41_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_42_ = lean_string_append(v___x_40_, v___x_41_);
v___x_43_ = 2;
v___x_44_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_43_);
lean_inc_ref(v_a_32_);
v___x_45_ = lean_apply_2(v_a_32_, v___x_44_, lean_box(0));
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
v___jp_47_:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = lean_array_get_size(v___y_49_);
v___x_52_ = lean_nat_dec_lt(v___y_48_, v___x_51_);
if (v___x_52_ == 0)
{
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_box(0);
v___x_54_ = lean_nat_dec_le(v___x_51_, v___x_51_);
if (v___x_54_ == 0)
{
if (v___x_52_ == 0)
{
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((size_t)0ULL);
v___x_56_ = lean_usize_of_nat(v___x_51_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_49_, v___x_55_, v___x_56_, v___x_53_, v_a_32_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_dec_ref(v___x_57_);
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_57_;
}
}
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_51_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_49_, v___x_58_, v___x_59_, v___x_53_, v_a_32_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_dec_ref(v___x_60_);
v_a_35_ = v_val_50_;
goto v___jp_34_;
}
else
{
lean_dec_ref(v_repo_30_);
lean_dec_ref(v_name_29_);
return v___x_60_;
}
}
}
}
v___jp_61_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
v___jp_64_:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_70_ = l_Lake_GitRepo_clean(v_repo_30_, v___x_69_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v_a_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
v_a_72_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_a_72_);
lean_dec_ref(v___x_70_);
v___x_73_ = lean_array_get_size(v_a_72_);
v___x_74_ = lean_nat_dec_lt(v___x_68_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec(v_a_72_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_a_71_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = lean_box(0);
v___x_77_ = lean_nat_dec_le(v___x_73_, v___x_73_);
if (v___x_77_ == 0)
{
if (v___x_74_ == 0)
{
lean_object* v___x_78_; 
lean_dec(v_a_72_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v_a_71_);
return v___x_78_;
}
else
{
size_t v___x_79_; size_t v___x_80_; lean_object* v___x_81_; 
v___x_79_ = ((size_t)0ULL);
v___x_80_ = lean_usize_of_nat(v___x_73_);
v___x_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_72_, v___x_79_, v___x_80_, v___x_76_, v_a_32_);
lean_dec(v_a_72_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_81_, 0);
lean_dec(v_unused_89_);
v___x_83_ = v___x_81_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_dec(v___x_81_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v_a_71_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_71_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
else
{
lean_dec(v_a_71_);
return v___x_81_;
}
}
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_73_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_72_, v___x_90_, v___x_91_, v___x_76_, v_a_32_);
lean_dec(v_a_72_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v___x_92_, 0);
lean_dec(v_unused_100_);
v___x_94_ = v___x_92_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_dec(v___x_92_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v_a_71_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_71_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
else
{
lean_dec(v_a_71_);
return v___x_92_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_a_101_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_a_101_);
lean_dec_ref(v___x_70_);
v___x_102_ = lean_array_get_size(v_a_101_);
v___x_103_ = lean_nat_dec_lt(v___x_68_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_a_101_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_box(0);
v___x_107_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_107_ == 0)
{
if (v___x_103_ == 0)
{
lean_dec(v_a_101_);
goto v___jp_64_;
}
else
{
size_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((size_t)0ULL);
v___x_109_ = lean_usize_of_nat(v___x_102_);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_101_, v___x_108_, v___x_109_, v___x_106_, v_a_32_);
lean_dec(v_a_101_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_dec_ref(v___x_110_);
goto v___jp_64_;
}
else
{
return v___x_110_;
}
}
}
else
{
size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((size_t)0ULL);
v___x_112_ = lean_usize_of_nat(v___x_102_);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_101_, v___x_111_, v___x_112_, v___x_106_, v_a_32_);
lean_dec(v_a_101_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_dec_ref(v___x_113_);
goto v___jp_64_;
}
else
{
return v___x_113_;
}
}
}
}
}
v___jp_114_:
{
if (lean_obj_tag(v___y_115_) == 0)
{
lean_dec_ref(v___y_115_);
goto v___jp_67_;
}
else
{
lean_dec_ref(v_repo_30_);
return v___y_115_;
}
}
v___jp_116_:
{
uint8_t v___x_119_; 
v___x_119_ = lean_string_dec_eq(v_a_118_, v___y_117_);
lean_dec_ref(v_a_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_120_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_121_ = lean_string_append(v_name_29_, v___x_120_);
v___x_122_ = lean_string_append(v___x_121_, v___y_117_);
v___x_123_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = 1;
v___x_126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_125_);
lean_inc_ref(v_a_32_);
v___x_127_ = lean_apply_2(v_a_32_, v___x_126_, lean_box(0));
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_30_);
v___x_130_ = l_Lake_GitRepo_checkoutDetach(v___y_117_, v_repo_30_, v___x_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_a_131_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_a_131_);
lean_dec_ref(v___x_130_);
v___x_132_ = lean_array_get_size(v_a_131_);
v___x_133_ = lean_nat_dec_lt(v___x_128_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec(v_a_131_);
goto v___jp_67_;
}
else
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_box(0);
v___x_135_ = lean_nat_dec_le(v___x_132_, v___x_132_);
if (v___x_135_ == 0)
{
if (v___x_133_ == 0)
{
lean_dec(v_a_131_);
goto v___jp_67_;
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_132_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_131_, v___x_136_, v___x_137_, v___x_134_, v_a_32_);
lean_dec(v_a_131_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_dec_ref(v___x_138_);
goto v___jp_67_;
}
else
{
v___y_115_ = v___x_138_;
goto v___jp_114_;
}
}
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_132_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_131_, v___x_139_, v___x_140_, v___x_134_, v_a_32_);
lean_dec(v_a_131_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_dec_ref(v___x_141_);
goto v___jp_67_;
}
else
{
v___y_115_ = v___x_141_;
goto v___jp_114_;
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_a_142_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_a_142_);
lean_dec_ref(v___x_130_);
v___x_143_ = lean_array_get_size(v_a_142_);
v___x_144_ = lean_nat_dec_lt(v___x_128_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_a_142_);
lean_dec_ref(v_repo_30_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_nat_dec_le(v___x_143_, v___x_143_);
if (v___x_148_ == 0)
{
if (v___x_144_ == 0)
{
lean_dec(v_a_142_);
lean_dec_ref(v_repo_30_);
goto v___jp_61_;
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_143_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_142_, v___x_149_, v___x_150_, v___x_147_, v_a_32_);
lean_dec(v_a_142_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_dec_ref(v___x_151_);
lean_dec_ref(v_repo_30_);
goto v___jp_61_;
}
else
{
v___y_115_ = v___x_151_;
goto v___jp_114_;
}
}
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_143_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_142_, v___x_152_, v___x_153_, v___x_147_, v_a_32_);
lean_dec(v_a_142_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_dec_ref(v___x_154_);
lean_dec_ref(v_repo_30_);
goto v___jp_61_;
}
else
{
v___y_115_ = v___x_154_;
goto v___jp_114_;
}
}
}
}
}
else
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec_ref(v___y_117_);
lean_inc_ref(v_repo_30_);
v___x_155_ = l_Lake_GitRepo_hasNoDiff(v_repo_30_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_155_ == 0)
{
v___y_48_ = v___x_156_;
v___y_49_ = v___x_157_;
v_val_50_ = v___x_119_;
goto v___jp_47_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
v___y_48_ = v___x_156_;
v___y_49_ = v___x_157_;
v_val_50_ = v___x_158_;
goto v___jp_47_;
}
}
}
v___jp_159_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
v___jp_162_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object* v_name_221_, lean_object* v_repo_222_, lean_object* v_rev_x3f_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(v_name_221_, v_repo_222_, v_rev_x3f_223_, v_a_224_);
lean_dec_ref(v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* v_name_228_, lean_object* v_repo_229_, lean_object* v_url_230_, lean_object* v_rev_x3f_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_a_238_; lean_object* v___y_336_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_340_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_228_);
v___x_341_ = lean_string_append(v_name_228_, v___x_340_);
v___x_342_ = lean_string_append(v___x_341_, v_url_230_);
v___x_343_ = 1;
v___x_344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v___x_343_);
lean_inc_ref(v_a_232_);
v___x_345_ = lean_apply_2(v_a_232_, v___x_344_, lean_box(0));
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_229_);
v___x_348_ = l_Lake_GitRepo_clone(v_url_230_, v_repo_229_, v___x_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_a_349_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_a_349_);
lean_dec_ref(v___x_348_);
v___x_350_ = lean_array_get_size(v_a_349_);
v___x_351_ = lean_nat_dec_lt(v___x_346_, v___x_350_);
if (v___x_351_ == 0)
{
lean_dec(v_a_349_);
goto v___jp_296_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_box(0);
v___x_353_ = lean_nat_dec_le(v___x_350_, v___x_350_);
if (v___x_353_ == 0)
{
if (v___x_351_ == 0)
{
lean_dec(v_a_349_);
goto v___jp_296_;
}
else
{
size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_354_ = ((size_t)0ULL);
v___x_355_ = lean_usize_of_nat(v___x_350_);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_349_, v___x_354_, v___x_355_, v___x_352_, v_a_232_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_dec_ref(v___x_356_);
goto v___jp_296_;
}
else
{
v___y_336_ = v___x_356_;
goto v___jp_335_;
}
}
}
else
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((size_t)0ULL);
v___x_358_ = lean_usize_of_nat(v___x_350_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_349_, v___x_357_, v___x_358_, v___x_352_, v_a_232_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_dec_ref(v___x_359_);
goto v___jp_296_;
}
else
{
v___y_336_ = v___x_359_;
goto v___jp_335_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_a_360_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_a_360_);
lean_dec_ref(v___x_348_);
v___x_361_ = lean_array_get_size(v_a_360_);
v___x_362_ = lean_nat_dec_lt(v___x_346_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_a_360_);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_box(0);
v___x_366_ = lean_nat_dec_le(v___x_361_, v___x_361_);
if (v___x_366_ == 0)
{
if (v___x_362_ == 0)
{
lean_dec(v_a_360_);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
goto v___jp_337_;
}
else
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v___x_367_ = ((size_t)0ULL);
v___x_368_ = lean_usize_of_nat(v___x_361_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_360_, v___x_367_, v___x_368_, v___x_365_, v_a_232_);
lean_dec(v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_dec_ref(v___x_369_);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
goto v___jp_337_;
}
else
{
v___y_336_ = v___x_369_;
goto v___jp_335_;
}
}
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_361_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_360_, v___x_370_, v___x_371_, v___x_365_, v_a_232_);
lean_dec(v_a_360_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_dec_ref(v___x_372_);
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
goto v___jp_337_;
}
else
{
v___y_336_ = v___x_372_;
goto v___jp_335_;
}
}
}
}
v___jp_234_:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_239_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_240_ = lean_string_append(v_name_228_, v___x_239_);
v___x_241_ = lean_string_append(v___x_240_, v_a_238_);
v___x_242_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_243_ = lean_string_append(v___x_241_, v___x_242_);
v___x_244_ = 1;
v___x_245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_244_);
lean_inc_ref(v_a_232_);
v___x_246_ = lean_apply_2(v_a_232_, v___x_245_, lean_box(0));
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_249_ = l_Lake_GitRepo_checkoutDetach(v_a_238_, v_repo_229_, v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v_a_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
v_a_251_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_a_251_);
lean_dec_ref(v___x_249_);
v___x_252_ = lean_array_get_size(v_a_251_);
v___x_253_ = lean_nat_dec_lt(v___x_247_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_a_251_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_a_250_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_nat_dec_le(v___x_252_, v___x_252_);
if (v___x_256_ == 0)
{
if (v___x_253_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_a_251_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_a_250_);
return v___x_257_;
}
else
{
size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v___x_258_ = ((size_t)0ULL);
v___x_259_ = lean_usize_of_nat(v___x_252_);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_251_, v___x_258_, v___x_259_, v___x_255_, v_a_232_);
lean_dec(v_a_251_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_260_, 0);
lean_dec(v_unused_268_);
v___x_262_ = v___x_260_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_dec(v___x_260_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v_a_250_);
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_250_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_dec(v_a_250_);
return v___x_260_;
}
}
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_252_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_251_, v___x_269_, v___x_270_, v___x_255_, v_a_232_);
lean_dec(v_a_251_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_271_, 0);
lean_dec(v_unused_279_);
v___x_273_ = v___x_271_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_dec(v___x_271_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_a_250_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_250_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_dec(v_a_250_);
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_a_280_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_a_280_);
lean_dec_ref(v___x_249_);
v___x_281_ = lean_array_get_size(v_a_280_);
v___x_282_ = lean_nat_dec_lt(v___x_247_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_a_280_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_box(0);
v___x_286_ = lean_nat_dec_le(v___x_281_, v___x_281_);
if (v___x_286_ == 0)
{
if (v___x_282_ == 0)
{
lean_dec(v_a_280_);
goto v___jp_234_;
}
else
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_287_ = ((size_t)0ULL);
v___x_288_ = lean_usize_of_nat(v___x_281_);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_280_, v___x_287_, v___x_288_, v___x_285_, v_a_232_);
lean_dec(v_a_280_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_dec_ref(v___x_289_);
goto v___jp_234_;
}
else
{
return v___x_289_;
}
}
}
else
{
size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((size_t)0ULL);
v___x_291_ = lean_usize_of_nat(v___x_281_);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_280_, v___x_290_, v___x_291_, v___x_285_, v_a_232_);
lean_dec(v_a_280_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_dec_ref(v___x_292_);
goto v___jp_234_;
}
else
{
return v___x_292_;
}
}
}
}
}
v___jp_293_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
v___jp_296_:
{
if (lean_obj_tag(v_rev_x3f_231_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_332_; 
v_val_297_ = lean_ctor_get(v_rev_x3f_231_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_rev_x3f_231_);
if (v_isSharedCheck_332_ == 0)
{
v___x_299_ = v_rev_x3f_231_;
v_isShared_300_ = v_isSharedCheck_332_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v_rev_x3f_231_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_332_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = l_Lake_Git_defaultRemote;
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_229_);
v___x_304_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_297_, v___x_301_, v_repo_229_, v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v_a_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
lean_del_object(v___x_299_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
v_a_306_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_a_306_);
lean_dec_ref(v___x_304_);
v___x_307_ = lean_array_get_size(v_a_306_);
v___x_308_ = lean_nat_dec_lt(v___x_302_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec(v_a_306_);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_box(0);
v___x_310_ = lean_nat_dec_le(v___x_307_, v___x_307_);
if (v___x_310_ == 0)
{
if (v___x_308_ == 0)
{
lean_dec(v_a_306_);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v___x_311_ = ((size_t)0ULL);
v___x_312_ = lean_usize_of_nat(v___x_307_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_306_, v___x_311_, v___x_312_, v___x_309_, v_a_232_);
lean_dec(v_a_306_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_dec_ref(v___x_313_);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
lean_dec(v_a_305_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
return v___x_313_;
}
}
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_307_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_306_, v___x_314_, v___x_315_, v___x_309_, v_a_232_);
lean_dec(v_a_306_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_dec_ref(v___x_316_);
v_a_238_ = v_a_305_;
goto v___jp_237_;
}
else
{
lean_dec(v_a_305_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
v_a_317_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_a_317_);
lean_dec_ref(v___x_304_);
v___x_318_ = lean_array_get_size(v_a_317_);
v___x_319_ = lean_nat_dec_lt(v___x_302_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec(v_a_317_);
v___x_320_ = lean_box(0);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_320_);
v___x_322_ = v___x_299_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; 
lean_del_object(v___x_299_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_nat_dec_le(v___x_318_, v___x_318_);
if (v___x_325_ == 0)
{
if (v___x_319_ == 0)
{
lean_dec(v_a_317_);
goto v___jp_293_;
}
else
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_318_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_317_, v___x_326_, v___x_327_, v___x_324_, v_a_232_);
lean_dec(v_a_317_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_dec_ref(v___x_328_);
goto v___jp_293_;
}
else
{
return v___x_328_;
}
}
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_318_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_317_, v___x_329_, v___x_330_, v___x_324_, v_a_232_);
lean_dec(v_a_317_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_dec_ref(v___x_331_);
goto v___jp_293_;
}
else
{
return v___x_331_;
}
}
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
v___jp_335_:
{
if (lean_obj_tag(v___y_336_) == 0)
{
lean_dec_ref(v___y_336_);
goto v___jp_296_;
}
else
{
lean_dec(v_rev_x3f_231_);
lean_dec_ref(v_repo_229_);
lean_dec_ref(v_name_228_);
return v___y_336_;
}
}
v___jp_337_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object* v_name_373_, lean_object* v_repo_374_, lean_object* v_url_375_, lean_object* v_rev_x3f_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(v_name_373_, v_repo_374_, v_url_375_, v_rev_x3f_376_, v_a_377_);
lean_dec_ref(v_a_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object* v_a_380_, lean_object* v_name_381_, lean_object* v_repo_382_, lean_object* v_url_383_, lean_object* v_rev_x3f_384_){
_start:
{
lean_object* v_a_390_; lean_object* v___y_488_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_492_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0));
lean_inc_ref(v_name_381_);
v___x_493_ = lean_string_append(v_name_381_, v___x_492_);
v___x_494_ = lean_string_append(v___x_493_, v_url_383_);
v___x_495_ = 1;
v___x_496_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
lean_inc_ref(v_a_380_);
v___x_497_ = lean_apply_2(v_a_380_, v___x_496_, lean_box(0));
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_382_);
v___x_500_ = l_Lake_GitRepo_clone(v_url_383_, v_repo_382_, v___x_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_a_501_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = lean_array_get_size(v_a_501_);
v___x_503_ = lean_nat_dec_lt(v___x_498_, v___x_502_);
if (v___x_503_ == 0)
{
lean_dec(v_a_501_);
goto v___jp_448_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_box(0);
v___x_505_ = lean_nat_dec_le(v___x_502_, v___x_502_);
if (v___x_505_ == 0)
{
if (v___x_503_ == 0)
{
lean_dec(v_a_501_);
goto v___jp_448_;
}
else
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((size_t)0ULL);
v___x_507_ = lean_usize_of_nat(v___x_502_);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_501_, v___x_506_, v___x_507_, v___x_504_, v_a_380_);
lean_dec(v_a_501_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_dec_ref(v___x_508_);
goto v___jp_448_;
}
else
{
v___y_488_ = v___x_508_;
goto v___jp_487_;
}
}
}
else
{
size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((size_t)0ULL);
v___x_510_ = lean_usize_of_nat(v___x_502_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_501_, v___x_509_, v___x_510_, v___x_504_, v_a_380_);
lean_dec(v_a_501_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_dec_ref(v___x_511_);
goto v___jp_448_;
}
else
{
v___y_488_ = v___x_511_;
goto v___jp_487_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_a_512_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_a_512_);
lean_dec_ref(v___x_500_);
v___x_513_ = lean_array_get_size(v_a_512_);
v___x_514_ = lean_nat_dec_lt(v___x_498_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_a_512_);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_nat_dec_le(v___x_513_, v___x_513_);
if (v___x_518_ == 0)
{
if (v___x_514_ == 0)
{
lean_dec(v_a_512_);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
goto v___jp_489_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___x_513_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_512_, v___x_519_, v___x_520_, v___x_517_, v_a_380_);
lean_dec(v_a_512_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_dec_ref(v___x_521_);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
goto v___jp_489_;
}
else
{
v___y_488_ = v___x_521_;
goto v___jp_487_;
}
}
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___x_513_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_512_, v___x_522_, v___x_523_, v___x_517_, v_a_380_);
lean_dec(v_a_512_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_dec_ref(v___x_524_);
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
goto v___jp_489_;
}
else
{
v___y_488_ = v___x_524_;
goto v___jp_487_;
}
}
}
}
v___jp_386_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_box(0);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_391_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_392_ = lean_string_append(v_name_381_, v___x_391_);
v___x_393_ = lean_string_append(v___x_392_, v_a_390_);
v___x_394_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = 1;
v___x_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*1, v___x_396_);
lean_inc_ref(v_a_380_);
v___x_398_ = lean_apply_2(v_a_380_, v___x_397_, lean_box(0));
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_401_ = l_Lake_GitRepo_checkoutDetach(v_a_390_, v_repo_382_, v___x_400_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
v_a_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_a_403_);
lean_dec_ref(v___x_401_);
v___x_404_ = lean_array_get_size(v_a_403_);
v___x_405_ = lean_nat_dec_lt(v___x_399_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_a_403_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_a_402_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_box(0);
v___x_408_ = lean_nat_dec_le(v___x_404_, v___x_404_);
if (v___x_408_ == 0)
{
if (v___x_405_ == 0)
{
lean_object* v___x_409_; 
lean_dec(v_a_403_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_a_402_);
return v___x_409_;
}
else
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((size_t)0ULL);
v___x_411_ = lean_usize_of_nat(v___x_404_);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_403_, v___x_410_, v___x_411_, v___x_407_, v_a_380_);
lean_dec(v_a_403_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_412_, 0);
lean_dec(v_unused_420_);
v___x_414_ = v___x_412_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_dec(v___x_412_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_a_402_);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_402_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_dec(v_a_402_);
return v___x_412_;
}
}
}
else
{
size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v___x_421_ = ((size_t)0ULL);
v___x_422_ = lean_usize_of_nat(v___x_404_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_403_, v___x_421_, v___x_422_, v___x_407_, v_a_380_);
lean_dec(v_a_403_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_423_, 0);
lean_dec(v_unused_431_);
v___x_425_ = v___x_423_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_dec(v___x_423_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v_a_402_);
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_402_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_dec(v_a_402_);
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_a_432_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_a_432_);
lean_dec_ref(v___x_401_);
v___x_433_ = lean_array_get_size(v_a_432_);
v___x_434_ = lean_nat_dec_lt(v___x_399_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_a_432_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_nat_dec_le(v___x_433_, v___x_433_);
if (v___x_438_ == 0)
{
if (v___x_434_ == 0)
{
lean_dec(v_a_432_);
goto v___jp_386_;
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_433_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_432_, v___x_439_, v___x_440_, v___x_437_, v_a_380_);
lean_dec(v_a_432_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_dec_ref(v___x_441_);
goto v___jp_386_;
}
else
{
return v___x_441_;
}
}
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_433_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_432_, v___x_442_, v___x_443_, v___x_437_, v_a_380_);
lean_dec(v_a_432_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_dec_ref(v___x_444_);
goto v___jp_386_;
}
else
{
return v___x_444_;
}
}
}
}
}
v___jp_445_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
v___jp_448_:
{
if (lean_obj_tag(v_rev_x3f_384_) == 1)
{
lean_object* v_val_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_484_; 
v_val_449_ = lean_ctor_get(v_rev_x3f_384_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_rev_x3f_384_);
if (v_isSharedCheck_484_ == 0)
{
v___x_451_ = v_rev_x3f_384_;
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_val_449_);
lean_dec(v_rev_x3f_384_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = l_Lake_Git_defaultRemote;
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_382_);
v___x_456_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_449_, v___x_453_, v_repo_382_, v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
lean_del_object(v___x_451_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
v_a_458_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_a_458_);
lean_dec_ref(v___x_456_);
v___x_459_ = lean_array_get_size(v_a_458_);
v___x_460_ = lean_nat_dec_lt(v___x_454_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v_a_458_);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_box(0);
v___x_462_ = lean_nat_dec_le(v___x_459_, v___x_459_);
if (v___x_462_ == 0)
{
if (v___x_460_ == 0)
{
lean_dec(v_a_458_);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_459_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_458_, v___x_463_, v___x_464_, v___x_461_, v_a_380_);
lean_dec(v_a_458_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_dec_ref(v___x_465_);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
lean_dec(v_a_457_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
return v___x_465_;
}
}
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_459_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_458_, v___x_466_, v___x_467_, v___x_461_, v_a_380_);
lean_dec(v_a_458_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec_ref(v___x_468_);
v_a_390_ = v_a_457_;
goto v___jp_389_;
}
else
{
lean_dec(v_a_457_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
v_a_469_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_a_469_);
lean_dec_ref(v___x_456_);
v___x_470_ = lean_array_get_size(v_a_469_);
v___x_471_ = lean_nat_dec_lt(v___x_454_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_a_469_);
v___x_472_ = lean_box(0);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_472_);
v___x_474_ = v___x_451_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
lean_object* v___x_476_; uint8_t v___x_477_; 
lean_del_object(v___x_451_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_nat_dec_le(v___x_470_, v___x_470_);
if (v___x_477_ == 0)
{
if (v___x_471_ == 0)
{
lean_dec(v_a_469_);
goto v___jp_445_;
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_470_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_469_, v___x_478_, v___x_479_, v___x_476_, v_a_380_);
lean_dec(v_a_469_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_dec_ref(v___x_480_);
goto v___jp_445_;
}
else
{
return v___x_480_;
}
}
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_470_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_469_, v___x_481_, v___x_482_, v___x_476_, v_a_380_);
lean_dec(v_a_469_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_dec_ref(v___x_483_);
goto v___jp_445_;
}
else
{
return v___x_483_;
}
}
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
v___jp_487_:
{
if (lean_obj_tag(v___y_488_) == 0)
{
lean_dec_ref(v___y_488_);
goto v___jp_448_;
}
else
{
lean_dec(v_rev_x3f_384_);
lean_dec_ref(v_repo_382_);
lean_dec_ref(v_name_381_);
return v___y_488_;
}
}
v___jp_489_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_box(0);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object* v_a_525_, lean_object* v_name_526_, lean_object* v_repo_527_, lean_object* v_url_528_, lean_object* v_rev_x3f_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_525_, v_name_526_, v_repo_527_, v_url_528_, v_rev_x3f_529_);
lean_dec_ref(v_a_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* v_a_532_, lean_object* v_name_533_, lean_object* v_repo_534_, lean_object* v_rev_x3f_535_){
_start:
{
uint8_t v_a_538_; lean_object* v___y_551_; lean_object* v___y_552_; uint8_t v_val_553_; lean_object* v___y_618_; lean_object* v___y_620_; lean_object* v_a_621_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = l_Lake_Git_defaultRemote;
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_534_);
v___x_671_ = l_Lake_GitRepo_findRemoteRevision(v_repo_534_, v_rev_x3f_535_, v___x_668_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v_a_673_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
v_a_673_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_a_673_);
lean_dec_ref(v___x_671_);
v___x_701_ = lean_array_get_size(v_a_673_);
v___x_702_ = lean_nat_dec_lt(v___x_669_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec(v_a_673_);
goto v___jp_674_;
}
else
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_box(0);
v___x_704_ = lean_nat_dec_le(v___x_701_, v___x_701_);
if (v___x_704_ == 0)
{
if (v___x_702_ == 0)
{
lean_dec(v_a_673_);
goto v___jp_674_;
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_701_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_673_, v___x_705_, v___x_706_, v___x_703_, v_a_532_);
lean_dec(v_a_673_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_dec_ref(v___x_707_);
goto v___jp_674_;
}
else
{
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_707_;
}
}
}
else
{
size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((size_t)0ULL);
v___x_709_ = lean_usize_of_nat(v___x_701_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_673_, v___x_708_, v___x_709_, v___x_703_, v_a_532_);
lean_dec(v_a_673_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_dec_ref(v___x_710_);
goto v___jp_674_;
}
else
{
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_710_;
}
}
}
v___jp_674_:
{
lean_object* v___x_675_; 
lean_inc_ref(v_repo_534_);
v___x_675_ = l_Lake_GitRepo_getHeadRevision(v_repo_534_, v___x_670_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
v_a_677_ = lean_ctor_get(v___x_675_, 1);
lean_inc(v_a_677_);
lean_dec_ref(v___x_675_);
v___x_678_ = lean_array_get_size(v_a_677_);
v___x_679_ = lean_nat_dec_lt(v___x_669_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec(v_a_677_);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_nat_dec_le(v___x_678_, v___x_678_);
if (v___x_681_ == 0)
{
if (v___x_679_ == 0)
{
lean_dec(v_a_677_);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_678_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_677_, v___x_682_, v___x_683_, v___x_680_, v_a_532_);
lean_dec(v_a_677_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_dec_ref(v___x_684_);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
lean_dec(v_a_676_);
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_684_;
}
}
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_678_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_677_, v___x_685_, v___x_686_, v___x_680_, v_a_532_);
lean_dec(v_a_677_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec_ref(v___x_687_);
v___y_620_ = v_a_672_;
v_a_621_ = v_a_676_;
goto v___jp_619_;
}
else
{
lean_dec(v_a_676_);
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
lean_dec(v_a_672_);
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
v_a_688_ = lean_ctor_get(v___x_675_, 1);
lean_inc(v_a_688_);
lean_dec_ref(v___x_675_);
v___x_689_ = lean_array_get_size(v_a_688_);
v___x_690_ = lean_nat_dec_lt(v___x_669_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_a_688_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_nat_dec_le(v___x_689_, v___x_689_);
if (v___x_694_ == 0)
{
if (v___x_690_ == 0)
{
lean_dec(v_a_688_);
goto v___jp_662_;
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_689_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_688_, v___x_695_, v___x_696_, v___x_693_, v_a_532_);
lean_dec(v_a_688_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_dec_ref(v___x_697_);
goto v___jp_662_;
}
else
{
return v___x_697_;
}
}
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_689_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_688_, v___x_698_, v___x_699_, v___x_693_, v_a_532_);
lean_dec(v_a_688_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_dec_ref(v___x_700_);
goto v___jp_662_;
}
else
{
return v___x_700_;
}
}
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
v_a_711_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_a_711_);
lean_dec_ref(v___x_671_);
v___x_712_ = lean_array_get_size(v_a_711_);
v___x_713_ = lean_nat_dec_lt(v___x_669_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_a_711_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = lean_nat_dec_le(v___x_712_, v___x_712_);
if (v___x_717_ == 0)
{
if (v___x_713_ == 0)
{
lean_dec(v_a_711_);
goto v___jp_665_;
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_712_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_711_, v___x_718_, v___x_719_, v___x_716_, v_a_532_);
lean_dec(v_a_711_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref(v___x_720_);
goto v___jp_665_;
}
else
{
return v___x_720_;
}
}
}
else
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = ((size_t)0ULL);
v___x_722_ = lean_usize_of_nat(v___x_712_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_711_, v___x_721_, v___x_722_, v___x_716_, v_a_532_);
lean_dec(v_a_711_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_dec_ref(v___x_723_);
goto v___jp_665_;
}
else
{
return v___x_723_;
}
}
}
}
v___jp_537_:
{
if (v_a_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_541_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_542_ = lean_string_append(v_name_533_, v___x_541_);
v___x_543_ = lean_string_append(v___x_542_, v_repo_534_);
lean_dec_ref(v_repo_534_);
v___x_544_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
v___x_546_ = 2;
v___x_547_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*1, v___x_546_);
lean_inc_ref(v_a_532_);
v___x_548_ = lean_apply_2(v_a_532_, v___x_547_, lean_box(0));
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
v___jp_550_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_size(v___y_551_);
v___x_555_ = lean_nat_dec_lt(v___y_552_, v___x_554_);
if (v___x_555_ == 0)
{
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_nat_dec_le(v___x_554_, v___x_554_);
if (v___x_557_ == 0)
{
if (v___x_555_ == 0)
{
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v___x_558_ = ((size_t)0ULL);
v___x_559_ = lean_usize_of_nat(v___x_554_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_551_, v___x_558_, v___x_559_, v___x_556_, v_a_532_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_dec_ref(v___x_560_);
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_560_;
}
}
}
else
{
size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_554_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_551_, v___x_561_, v___x_562_, v___x_556_, v_a_532_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_dec_ref(v___x_563_);
v_a_538_ = v_val_553_;
goto v___jp_537_;
}
else
{
lean_dec_ref(v_repo_534_);
lean_dec_ref(v_name_533_);
return v___x_563_;
}
}
}
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_box(0);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
v___jp_567_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
v___jp_570_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_573_ = l_Lake_GitRepo_clean(v_repo_534_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
v_a_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_a_575_);
lean_dec_ref(v___x_573_);
v___x_576_ = lean_array_get_size(v_a_575_);
v___x_577_ = lean_nat_dec_lt(v___x_571_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v_a_575_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_a_574_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_box(0);
v___x_580_ = lean_nat_dec_le(v___x_576_, v___x_576_);
if (v___x_580_ == 0)
{
if (v___x_577_ == 0)
{
lean_object* v___x_581_; 
lean_dec(v_a_575_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v_a_574_);
return v___x_581_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_576_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_575_, v___x_582_, v___x_583_, v___x_579_, v_a_532_);
lean_dec(v_a_575_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_592_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_a_574_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_574_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_dec(v_a_574_);
return v___x_584_;
}
}
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_576_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_575_, v___x_593_, v___x_594_, v___x_579_, v_a_532_);
lean_dec(v_a_575_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_603_);
v___x_597_ = v___x_595_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_dec(v___x_595_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_a_574_);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_574_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_dec(v_a_574_);
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_a_604_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_a_604_);
lean_dec_ref(v___x_573_);
v___x_605_ = lean_array_get_size(v_a_604_);
v___x_606_ = lean_nat_dec_lt(v___x_571_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_a_604_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_nat_dec_le(v___x_605_, v___x_605_);
if (v___x_610_ == 0)
{
if (v___x_606_ == 0)
{
lean_dec(v_a_604_);
goto v___jp_567_;
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_605_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_604_, v___x_611_, v___x_612_, v___x_609_, v_a_532_);
lean_dec(v_a_604_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_dec_ref(v___x_613_);
goto v___jp_567_;
}
else
{
return v___x_613_;
}
}
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_605_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_604_, v___x_614_, v___x_615_, v___x_609_, v_a_532_);
lean_dec(v_a_604_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_dec_ref(v___x_616_);
goto v___jp_567_;
}
else
{
return v___x_616_;
}
}
}
}
}
v___jp_617_:
{
if (lean_obj_tag(v___y_618_) == 0)
{
lean_dec_ref(v___y_618_);
goto v___jp_570_;
}
else
{
lean_dec_ref(v_repo_534_);
return v___y_618_;
}
}
v___jp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_string_dec_eq(v_a_621_, v___y_620_);
lean_dec_ref(v_a_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_623_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3));
v___x_624_ = lean_string_append(v_name_533_, v___x_623_);
v___x_625_ = lean_string_append(v___x_624_, v___y_620_);
v___x_626_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4));
v___x_627_ = lean_string_append(v___x_625_, v___x_626_);
v___x_628_ = 1;
v___x_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
lean_inc_ref(v_a_532_);
v___x_630_ = lean_apply_2(v_a_532_, v___x_629_, lean_box(0));
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_repo_534_);
v___x_633_ = l_Lake_GitRepo_checkoutDetach(v___y_620_, v_repo_534_, v___x_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_array_get_size(v_a_634_);
v___x_636_ = lean_nat_dec_lt(v___x_631_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_a_634_);
goto v___jp_570_;
}
else
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_box(0);
v___x_638_ = lean_nat_dec_le(v___x_635_, v___x_635_);
if (v___x_638_ == 0)
{
if (v___x_636_ == 0)
{
lean_dec(v_a_634_);
goto v___jp_570_;
}
else
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_635_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_634_, v___x_639_, v___x_640_, v___x_637_, v_a_532_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref(v___x_641_);
goto v___jp_570_;
}
else
{
v___y_618_ = v___x_641_;
goto v___jp_617_;
}
}
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_635_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_634_, v___x_642_, v___x_643_, v___x_637_, v_a_532_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref(v___x_644_);
goto v___jp_570_;
}
else
{
v___y_618_ = v___x_644_;
goto v___jp_617_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_a_645_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_a_645_);
lean_dec_ref(v___x_633_);
v___x_646_ = lean_array_get_size(v_a_645_);
v___x_647_ = lean_nat_dec_lt(v___x_631_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_a_645_);
lean_dec_ref(v_repo_534_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_nat_dec_le(v___x_646_, v___x_646_);
if (v___x_651_ == 0)
{
if (v___x_647_ == 0)
{
lean_dec(v_a_645_);
lean_dec_ref(v_repo_534_);
goto v___jp_564_;
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_646_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_645_, v___x_652_, v___x_653_, v___x_650_, v_a_532_);
lean_dec(v_a_645_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec_ref(v___x_654_);
lean_dec_ref(v_repo_534_);
goto v___jp_564_;
}
else
{
v___y_618_ = v___x_654_;
goto v___jp_617_;
}
}
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_646_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_645_, v___x_655_, v___x_656_, v___x_650_, v_a_532_);
lean_dec(v_a_645_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref(v___x_657_);
lean_dec_ref(v_repo_534_);
goto v___jp_564_;
}
else
{
v___y_618_ = v___x_657_;
goto v___jp_617_;
}
}
}
}
}
else
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec_ref(v___y_620_);
lean_inc_ref(v_repo_534_);
v___x_658_ = l_Lake_GitRepo_hasNoDiff(v_repo_534_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_658_ == 0)
{
v___y_551_ = v___x_660_;
v___y_552_ = v___x_659_;
v_val_553_ = v___x_622_;
goto v___jp_550_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 0;
v___y_551_ = v___x_660_;
v___y_552_ = v___x_659_;
v_val_553_ = v___x_661_;
goto v___jp_550_;
}
}
}
v___jp_662_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
v___jp_665_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* v_a_724_, lean_object* v_name_725_, lean_object* v_repo_726_, lean_object* v_rev_x3f_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_724_, v_name_725_, v_repo_726_, v_rev_x3f_727_);
lean_dec_ref(v_a_724_);
return v_res_729_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_735_ = lean_array_get_size(v___x_734_);
return v___x_735_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_nat_dec_lt(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6(void){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_740_ = lean_nat_dec_le(v___x_739_, v___x_739_);
return v___x_740_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7(void){
_start:
{
lean_object* v___x_741_; size_t v___x_742_; 
v___x_741_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
v___x_742_ = lean_usize_of_nat(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* v_name_743_, lean_object* v_repo_744_, lean_object* v_url_745_, lean_object* v_rev_x3f_746_, lean_object* v_a_747_){
_start:
{
uint8_t v_a_750_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v_val_789_; 
v___x_785_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_744_);
v___x_786_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_785_, v_repo_744_);
v___x_787_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v___x_786_) == 1)
{
lean_object* v_val_799_; uint8_t v___x_800_; 
v_val_799_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_799_);
lean_dec_ref(v___x_786_);
v___x_800_ = lean_string_dec_eq(v_val_799_, v_url_745_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
v___x_801_ = lean_io_realpath(v_val_799_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
lean_inc_ref(v_url_745_);
v___x_803_ = lean_io_realpath(v_url_745_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; uint8_t v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v___x_805_ = lean_string_dec_eq(v_a_802_, v_a_804_);
lean_dec(v_a_804_);
lean_dec(v_a_802_);
v_val_789_ = v___x_805_;
goto v___jp_788_;
}
else
{
lean_dec_ref(v___x_803_);
lean_dec(v_a_802_);
v_val_789_ = v___x_800_;
goto v___jp_788_;
}
}
else
{
lean_dec_ref(v___x_801_);
v_val_789_ = v___x_800_;
goto v___jp_788_;
}
}
else
{
lean_dec(v_val_799_);
v_val_789_ = v___x_800_;
goto v___jp_788_;
}
}
else
{
uint8_t v___x_806_; 
lean_dec(v___x_786_);
v___x_806_ = 0;
v_val_789_ = v___x_806_;
goto v___jp_788_;
}
v___jp_749_:
{
if (v_a_750_ == 0)
{
uint8_t v___x_751_; 
v___x_751_ = l_System_Platform_isWindows;
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_752_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_743_);
v___x_753_ = lean_string_append(v_name_743_, v___x_752_);
v___x_754_ = lean_string_append(v___x_753_, v_repo_744_);
v___x_755_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
v___x_757_ = 1;
v___x_758_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*1, v___x_757_);
lean_inc_ref(v_a_747_);
v___x_759_ = lean_apply_2(v_a_747_, v___x_758_, lean_box(0));
v___x_760_ = l_IO_FS_removeDirAll(v_repo_744_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; 
lean_dec_ref(v___x_760_);
v___x_761_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_747_, v_name_743_, v_repo_744_, v_url_745_, v_rev_x3f_746_);
return v___x_761_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_rev_x3f_746_);
lean_dec_ref(v_url_745_);
lean_dec_ref(v_repo_744_);
lean_dec_ref(v_name_743_);
v_a_762_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_774_ == 0)
{
v___x_764_ = v___x_760_;
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_766_ = lean_io_error_to_string(v_a_762_);
v___x_767_ = 3;
v___x_768_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*1, v___x_767_);
lean_inc_ref(v_a_747_);
v___x_769_ = lean_apply_2(v_a_747_, v___x_768_, lean_box(0));
v___x_770_ = lean_box(0);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_770_);
v___x_772_ = v___x_764_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v_url_745_);
v___x_775_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_743_);
v___x_776_ = lean_string_append(v_name_743_, v___x_775_);
v___x_777_ = lean_string_append(v___x_776_, v_repo_744_);
v___x_778_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_779_ = lean_string_append(v___x_777_, v___x_778_);
v___x_780_ = 1;
v___x_781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*1, v___x_780_);
lean_inc_ref(v_a_747_);
v___x_782_ = lean_apply_2(v_a_747_, v___x_781_, lean_box(0));
v___x_783_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_747_, v_name_743_, v_repo_744_, v_rev_x3f_746_);
return v___x_783_;
}
}
else
{
lean_object* v___x_784_; 
lean_dec_ref(v_url_745_);
v___x_784_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_747_, v_name_743_, v_repo_744_, v_rev_x3f_746_);
return v___x_784_;
}
}
v___jp_788_:
{
uint8_t v___x_790_; 
v___x_790_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_790_ == 0)
{
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = lean_box(0);
v___x_792_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_792_ == 0)
{
if (v___x_790_ == 0)
{
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_787_, v___x_793_, v___x_794_, v___x_791_, v_a_747_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref(v___x_795_);
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
lean_dec(v_rev_x3f_746_);
lean_dec_ref(v_url_745_);
lean_dec_ref(v_repo_744_);
lean_dec_ref(v_name_743_);
return v___x_795_;
}
}
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_787_, v___x_796_, v___x_797_, v___x_791_, v_a_747_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_dec_ref(v___x_798_);
v_a_750_ = v_val_789_;
goto v___jp_749_;
}
else
{
lean_dec(v_rev_x3f_746_);
lean_dec_ref(v_url_745_);
lean_dec_ref(v_repo_744_);
lean_dec_ref(v_name_743_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object* v_name_807_, lean_object* v_repo_808_, lean_object* v_url_809_, lean_object* v_rev_x3f_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(v_name_807_, v_repo_808_, v_url_809_, v_rev_x3f_810_, v_a_811_);
lean_dec_ref(v_a_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_a_814_, lean_object* v_name_815_, lean_object* v_repo_816_, lean_object* v_url_817_, lean_object* v_rev_x3f_818_){
_start:
{
uint8_t v_a_821_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v_val_860_; 
v___x_856_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_repo_816_);
v___x_857_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_856_, v_repo_816_);
v___x_858_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v___x_857_) == 1)
{
lean_object* v_val_870_; uint8_t v___x_871_; 
v_val_870_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_870_);
lean_dec_ref(v___x_857_);
v___x_871_ = lean_string_dec_eq(v_val_870_, v_url_817_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_io_realpath(v_val_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v___x_872_);
lean_inc_ref(v_url_817_);
v___x_874_ = lean_io_realpath(v_url_817_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; uint8_t v___x_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v___x_874_);
v___x_876_ = lean_string_dec_eq(v_a_873_, v_a_875_);
lean_dec(v_a_875_);
lean_dec(v_a_873_);
v_val_860_ = v___x_876_;
goto v___jp_859_;
}
else
{
lean_dec_ref(v___x_874_);
lean_dec(v_a_873_);
v_val_860_ = v___x_871_;
goto v___jp_859_;
}
}
else
{
lean_dec_ref(v___x_872_);
v_val_860_ = v___x_871_;
goto v___jp_859_;
}
}
else
{
lean_dec(v_val_870_);
v_val_860_ = v___x_871_;
goto v___jp_859_;
}
}
else
{
uint8_t v___x_877_; 
lean_dec(v___x_857_);
v___x_877_ = 0;
v_val_860_ = v___x_877_;
goto v___jp_859_;
}
v___jp_820_:
{
if (v_a_821_ == 0)
{
uint8_t v___x_822_; 
v___x_822_ = l_System_Platform_isWindows;
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_823_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0));
lean_inc_ref(v_name_815_);
v___x_824_ = lean_string_append(v_name_815_, v___x_823_);
v___x_825_ = lean_string_append(v___x_824_, v_repo_816_);
v___x_826_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1));
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
v___x_828_ = 1;
v___x_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*1, v___x_828_);
lean_inc_ref(v_a_814_);
v___x_830_ = lean_apply_2(v_a_814_, v___x_829_, lean_box(0));
v___x_831_ = l_IO_FS_removeDirAll(v_repo_816_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v___x_831_);
v___x_832_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_814_, v_name_815_, v_repo_816_, v_url_817_, v_rev_x3f_818_);
return v___x_832_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_rev_x3f_818_);
lean_dec_ref(v_url_817_);
lean_dec_ref(v_repo_816_);
lean_dec_ref(v_name_815_);
v_a_833_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_845_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_837_ = lean_io_error_to_string(v_a_833_);
v___x_838_ = 3;
v___x_839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*1, v___x_838_);
lean_inc_ref(v_a_814_);
v___x_840_ = lean_apply_2(v_a_814_, v___x_839_, lean_box(0));
v___x_841_ = lean_box(0);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_841_);
v___x_843_ = v___x_835_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref(v_url_817_);
v___x_846_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2));
lean_inc_ref(v_name_815_);
v___x_847_ = lean_string_append(v_name_815_, v___x_846_);
v___x_848_ = lean_string_append(v___x_847_, v_repo_816_);
v___x_849_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3));
v___x_850_ = lean_string_append(v___x_848_, v___x_849_);
v___x_851_ = 1;
v___x_852_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*1, v___x_851_);
lean_inc_ref(v_a_814_);
v___x_853_ = lean_apply_2(v_a_814_, v___x_852_, lean_box(0));
v___x_854_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_814_, v_name_815_, v_repo_816_, v_rev_x3f_818_);
return v___x_854_;
}
}
else
{
lean_object* v___x_855_; 
lean_dec_ref(v_url_817_);
v___x_855_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_814_, v_name_815_, v_repo_816_, v_rev_x3f_818_);
return v___x_855_;
}
}
v___jp_859_:
{
uint8_t v___x_861_; 
v___x_861_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_861_ == 0)
{
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_863_ == 0)
{
if (v___x_861_ == 0)
{
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_858_, v___x_864_, v___x_865_, v___x_862_, v_a_814_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_dec_ref(v___x_866_);
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
lean_dec(v_rev_x3f_818_);
lean_dec_ref(v_url_817_);
lean_dec_ref(v_repo_816_);
lean_dec_ref(v_name_815_);
return v___x_866_;
}
}
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((size_t)0ULL);
v___x_868_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_858_, v___x_867_, v___x_868_, v___x_862_, v_a_814_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_dec_ref(v___x_869_);
v_a_821_ = v_val_860_;
goto v___jp_820_;
}
else
{
lean_dec(v_rev_x3f_818_);
lean_dec_ref(v_url_817_);
lean_dec_ref(v_repo_816_);
lean_dec_ref(v_name_815_);
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_a_878_, lean_object* v_name_879_, lean_object* v_repo_880_, lean_object* v_url_881_, lean_object* v_rev_x3f_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_878_, v_name_879_, v_repo_880_, v_url_881_, v_rev_x3f_882_);
lean_dec_ref(v_a_878_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_885_, lean_object* v_repo_886_, lean_object* v_url_887_, lean_object* v_rev_x3f_888_, lean_object* v_a_889_){
_start:
{
uint8_t v___x_891_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_891_ = l_System_FilePath_isDir(v_repo_886_);
v___x_895_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_896_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_896_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_box(0);
v___x_898_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_898_ == 0)
{
if (v___x_896_ == 0)
{
goto v___jp_892_;
}
else
{
size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((size_t)0ULL);
v___x_900_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_895_, v___x_899_, v___x_900_, v___x_897_, v_a_889_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_dec_ref(v___x_901_);
goto v___jp_892_;
}
else
{
lean_dec(v_rev_x3f_888_);
lean_dec_ref(v_url_887_);
lean_dec_ref(v_repo_886_);
lean_dec_ref(v_name_885_);
return v___x_901_;
}
}
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; 
v___x_902_ = ((size_t)0ULL);
v___x_903_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_895_, v___x_902_, v___x_903_, v___x_897_, v_a_889_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_dec_ref(v___x_904_);
goto v___jp_892_;
}
else
{
lean_dec(v_rev_x3f_888_);
lean_dec_ref(v_url_887_);
lean_dec_ref(v_repo_886_);
lean_dec_ref(v_name_885_);
return v___x_904_;
}
}
}
v___jp_892_:
{
if (v___x_891_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_889_, v_name_885_, v_repo_886_, v_url_887_, v_rev_x3f_888_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_889_, v_name_885_, v_repo_886_, v_url_887_, v_rev_x3f_888_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_905_, lean_object* v_repo_906_, lean_object* v_url_907_, lean_object* v_rev_x3f_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_905_, v_repo_906_, v_url_907_, v_rev_x3f_908_, v_a_909_);
lean_dec_ref(v_a_909_);
return v_res_911_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_918_ = l_Lake_instInhabitedPackageEntry_default;
v___x_919_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_920_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_921_ = l_System_instInhabitedFilePath_default;
v___x_922_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_920_);
lean_ctor_set(v___x_922_, 2, v___x_919_);
lean_ctor_set(v___x_922_, 3, v___x_918_);
return v___x_922_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_923_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_925_){
_start:
{
lean_object* v_manifestEntry_926_; lean_object* v_name_927_; 
v_manifestEntry_926_ = lean_ctor_get(v_self_925_, 3);
v_name_927_ = lean_ctor_get(v_manifestEntry_926_, 0);
lean_inc(v_name_927_);
return v_name_927_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lake_MaterializedDep_name(v_self_928_);
lean_dec_ref(v_self_928_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_930_){
_start:
{
lean_object* v_manifestEntry_931_; lean_object* v_scope_932_; 
v_manifestEntry_931_ = lean_ctor_get(v_self_930_, 3);
v_scope_932_ = lean_ctor_get(v_manifestEntry_931_, 1);
lean_inc_ref(v_scope_932_);
return v_scope_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lake_MaterializedDep_scope(v_self_933_);
lean_dec_ref(v_self_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* v_self_935_){
_start:
{
lean_object* v_manifestEntry_936_; lean_object* v_manifestFile_x3f_937_; 
v_manifestEntry_936_ = lean_ctor_get(v_self_935_, 3);
v_manifestFile_x3f_937_ = lean_ctor_get(v_manifestEntry_936_, 3);
lean_inc(v_manifestFile_x3f_937_);
return v_manifestFile_x3f_937_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object* v_self_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lake_MaterializedDep_manifestFile_x3f(v_self_938_);
lean_dec_ref(v_self_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_940_){
_start:
{
lean_object* v_manifestEntry_941_; lean_object* v_configFile_942_; 
v_manifestEntry_941_ = lean_ctor_get(v_self_940_, 3);
v_configFile_942_ = lean_ctor_get(v_manifestEntry_941_, 2);
lean_inc_ref(v_configFile_942_);
return v_configFile_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* v_self_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lake_MaterializedDep_configFile(v_self_943_);
lean_dec_ref(v_self_943_);
return v_res_944_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_945_){
_start:
{
lean_object* v_manifest_x3f_946_; 
v_manifest_x3f_946_ = lean_ctor_get(v_self_945_, 2);
if (lean_obj_tag(v_manifest_x3f_946_) == 1)
{
lean_object* v_a_947_; uint8_t v_fixedToolchain_948_; 
v_a_947_ = lean_ctor_get(v_manifest_x3f_946_, 0);
v_fixedToolchain_948_ = lean_ctor_get_uint8(v_a_947_, sizeof(void*)*4);
return v_fixedToolchain_948_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = 0;
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lake_MaterializedDep_fixedToolchain(v_self_950_);
lean_dec_ref(v_self_950_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* v_x_953_){
_start:
{
switch(lean_obj_tag(v_x_953_))
{
case 0:
{
lean_object* v___x_954_; 
v___x_954_ = lean_unsigned_to_nat(0u);
return v___x_954_;
}
case 1:
{
lean_object* v___x_955_; 
v___x_955_ = lean_unsigned_to_nat(1u);
return v___x_955_;
}
default: 
{
lean_object* v___x_956_; 
v___x_956_ = lean_unsigned_to_nat(2u);
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* v_x_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_957_);
lean_dec(v_x_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* v_t_959_, lean_object* v_k_960_){
_start:
{
if (lean_obj_tag(v_t_959_) == 0)
{
return v_k_960_;
}
else
{
lean_object* v_rev_961_; lean_object* v___x_962_; 
v_rev_961_ = lean_ctor_get(v_t_959_, 0);
lean_inc_ref(v_rev_961_);
lean_dec(v_t_959_);
v___x_962_ = lean_apply_1(v_k_960_, v_rev_961_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* v_motive_963_, lean_object* v_ctorIdx_964_, lean_object* v_t_965_, lean_object* v_h_966_, lean_object* v_k_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_965_, v_k_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* v_motive_969_, lean_object* v_ctorIdx_970_, lean_object* v_t_971_, lean_object* v_h_972_, lean_object* v_k_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(v_motive_969_, v_ctorIdx_970_, v_t_971_, v_h_972_, v_k_973_);
lean_dec(v_ctorIdx_970_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* v_t_975_, lean_object* v_none_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_975_, v_none_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* v_motive_978_, lean_object* v_t_979_, lean_object* v_h_980_, lean_object* v_none_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_979_, v_none_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* v_t_983_, lean_object* v_git_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_983_, v_git_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* v_motive_986_, lean_object* v_t_987_, lean_object* v_h_988_, lean_object* v_git_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_987_, v_git_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* v_t_991_, lean_object* v_ver_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_991_, v_ver_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* v_motive_994_, lean_object* v_t_995_, lean_object* v_h_996_, lean_object* v_ver_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_995_, v_ver_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_scope_1007_, lean_object* v_name_1008_, lean_object* v_ver_1009_){
_start:
{
lean_object* v_fst_1011_; lean_object* v_snd_1012_; 
switch(lean_obj_tag(v_ver_1009_))
{
case 0:
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1011_ = v___x_1033_;
v_snd_1012_ = v___x_1033_;
goto v___jp_1010_;
}
case 1:
{
lean_object* v_rev_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1049_; 
v_rev_1034_ = lean_ctor_get(v_ver_1009_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_ver_1009_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1036_ = v_ver_1009_;
v_isShared_1037_ = v_isSharedCheck_1049_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_rev_1034_);
lean_dec(v_ver_1009_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1049_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1039_ = l_String_quote(v_rev_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 3);
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1042_ = l_Std_Format_defWidth;
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = l_Std_Format_pretty(v___x_1041_, v___x_1042_, v___x_1043_, v___x_1043_);
v___x_1045_ = lean_string_append(v___x_1038_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1047_ = lean_string_append(v___x_1046_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v_fst_1011_ = v___x_1045_;
v_snd_1012_ = v___x_1047_;
goto v___jp_1010_;
}
}
}
default: 
{
lean_object* v_ver_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1066_; 
v_ver_1050_ = lean_ctor_get(v_ver_1009_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_ver_1009_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1052_ = v_ver_1009_;
v_isShared_1053_ = v_isSharedCheck_1066_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_ver_1050_);
lean_dec(v_ver_1009_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1066_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_toString_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v_toString_1054_ = lean_ctor_get(v_ver_1050_, 0);
lean_inc_ref(v_toString_1054_);
lean_dec_ref(v_ver_1050_);
v___x_1055_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1056_ = l_String_quote(v_toString_1054_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 3);
lean_ctor_set(v___x_1052_, 0, v___x_1056_);
v___x_1058_ = v___x_1052_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1059_ = l_Std_Format_defWidth;
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = l_Std_Format_pretty(v___x_1058_, v___x_1059_, v___x_1060_, v___x_1060_);
v___x_1062_ = lean_string_append(v___x_1055_, v___x_1061_);
v___x_1063_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1064_ = lean_string_append(v___x_1063_, v___x_1061_);
lean_dec_ref(v___x_1061_);
v_fst_1011_ = v___x_1062_;
v_snd_1012_ = v___x_1064_;
goto v___jp_1010_;
}
}
}
}
v___jp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1013_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1007_);
v___x_1014_ = lean_string_append(v_scope_1007_, v___x_1013_);
v___x_1015_ = lean_string_append(v___x_1014_, v_name_1008_);
v___x_1016_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1017_ = lean_string_append(v___x_1015_, v___x_1016_);
v___x_1018_ = lean_string_append(v___x_1017_, v_scope_1007_);
v___x_1019_ = lean_string_append(v___x_1018_, v___x_1013_);
v___x_1020_ = lean_string_append(v___x_1019_, v_name_1008_);
v___x_1021_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1022_ = lean_string_append(v___x_1020_, v___x_1021_);
v___x_1023_ = lean_string_append(v___x_1022_, v_fst_1011_);
lean_dec_ref(v_fst_1011_);
v___x_1024_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1025_ = lean_string_append(v___x_1023_, v___x_1024_);
v___x_1026_ = lean_string_append(v___x_1025_, v_scope_1007_);
lean_dec_ref(v_scope_1007_);
v___x_1027_ = lean_string_append(v___x_1026_, v___x_1013_);
v___x_1028_ = lean_string_append(v___x_1027_, v_name_1008_);
v___x_1029_ = lean_string_append(v___x_1028_, v___x_1021_);
v___x_1030_ = lean_string_append(v___x_1029_, v_snd_1012_);
lean_dec_ref(v_snd_1012_);
v___x_1031_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1032_ = lean_string_append(v___x_1030_, v___x_1031_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* v_scope_1067_, lean_object* v_name_1068_, lean_object* v_ver_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1067_, v_name_1068_, v_ver_1069_);
lean_dec_ref(v_name_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_inc_ref(v___y_1073_);
v___x_1075_ = lean_apply_2(v___y_1073_, v___y_1072_, lean_box(0));
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object* v_x_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(v_x_1077_, v___y_1078_, v___y_1079_);
lean_dec_ref(v___y_1079_);
return v_res_1081_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_instMonadEIO(lean_box(0));
return v___x_1083_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
v___x_1085_ = l_ReaderT_instMonad___redArg(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1086_, uint8_t v_inherited_1087_, lean_object* v_pkgDir_1088_, lean_object* v_relPkgDir_1089_, lean_object* v_remoteUrl_1090_, lean_object* v_src_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_a_1095_; lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_val_1109_; lean_object* v___x_1137_; 
v___f_1103_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1104_ = l_Lake_defaultManifestFile;
v___x_1105_ = l_Lake_joinRelative(v_pkgDir_1088_, v___x_1104_);
v___x_1106_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2);
v___x_1107_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1137_ = l_Lake_Manifest_load(v___x_1105_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 1);
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
v_val_1109_ = v___x_1143_;
goto v___jp_1108_;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1146_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1137_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1137_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 0);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
v_val_1109_ = v___x_1151_;
goto v___jp_1108_;
}
}
}
v___jp_1094_:
{
lean_object* v_name_1096_; lean_object* v_scope_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_name_1096_ = lean_ctor_get(v_dep_1086_, 0);
v_scope_1097_ = lean_ctor_get(v_dep_1086_, 1);
v___x_1098_ = l_Lake_defaultConfigFile;
v___x_1099_ = lean_box(0);
lean_inc_ref(v_scope_1097_);
lean_inc(v_name_1096_);
v___x_1100_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1100_, 0, v_name_1096_);
lean_ctor_set(v___x_1100_, 1, v_scope_1097_);
lean_ctor_set(v___x_1100_, 2, v___x_1098_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
lean_ctor_set(v___x_1100_, 4, v_src_1091_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*5, v_inherited_1087_);
v___x_1101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1101_, 0, v_relPkgDir_1089_);
lean_ctor_set(v___x_1101_, 1, v_remoteUrl_1090_);
lean_ctor_set(v___x_1101_, 2, v_a_1095_);
lean_ctor_set(v___x_1101_, 3, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
v___jp_1108_:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1110_ == 0)
{
v_a_1095_ = v_val_1109_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1112_ == 0)
{
if (v___x_1110_ == 0)
{
v_a_1095_ = v_val_1109_;
goto v___jp_1094_;
}
else
{
size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_808__overap_1115_; lean_object* v___x_1116_; 
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_808__overap_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1106_, v___f_1103_, v___x_1107_, v___x_1113_, v___x_1114_, v___x_1111_);
lean_inc_ref(v_a_1092_);
v___x_1116_ = lean_apply_2(v___x_808__overap_1115_, v_a_1092_, lean_box(0));
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_dec_ref(v___x_1116_);
v_a_1095_ = v_val_1109_;
goto v___jp_1094_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v_val_1109_);
lean_dec_ref(v_src_1091_);
lean_dec_ref(v_remoteUrl_1090_);
lean_dec_ref(v_relPkgDir_1089_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
else
{
size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_818__overap_1127_; lean_object* v___x_1128_; 
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_818__overap_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1106_, v___f_1103_, v___x_1107_, v___x_1125_, v___x_1126_, v___x_1111_);
lean_inc_ref(v_a_1092_);
v___x_1128_ = lean_apply_2(v___x_818__overap_1127_, v_a_1092_, lean_box(0));
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_dec_ref(v___x_1128_);
v_a_1095_ = v_val_1109_;
goto v___jp_1094_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v_val_1109_);
lean_dec_ref(v_src_1091_);
lean_dec_ref(v_remoteUrl_1090_);
lean_dec_ref(v_relPkgDir_1089_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1154_, lean_object* v_inherited_1155_, lean_object* v_pkgDir_1156_, lean_object* v_relPkgDir_1157_, lean_object* v_remoteUrl_1158_, lean_object* v_src_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
uint8_t v_inherited_boxed_1162_; lean_object* v_res_1163_; 
v_inherited_boxed_1162_ = lean_unbox(v_inherited_1155_);
v_res_1163_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1154_, v_inherited_boxed_1162_, v_pkgDir_1156_, v_relPkgDir_1157_, v_remoteUrl_1158_, v_src_1159_, v_a_1160_);
lean_dec_ref(v_a_1160_);
lean_dec_ref(v_dep_1154_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1164_, lean_object* v_name_1165_, lean_object* v_repo_1166_, lean_object* v_url_1167_, lean_object* v_rev_x3f_1168_){
_start:
{
uint8_t v___x_1170_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1170_ = l_System_FilePath_isDir(v_repo_1166_);
v___x_1174_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1175_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1175_ == 0)
{
goto v___jp_1171_;
}
else
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1177_ == 0)
{
if (v___x_1175_ == 0)
{
goto v___jp_1171_;
}
else
{
size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = ((size_t)0ULL);
v___x_1179_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1174_, v___x_1178_, v___x_1179_, v___x_1176_, v_a_1164_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_dec_ref(v___x_1180_);
goto v___jp_1171_;
}
else
{
lean_dec(v_rev_x3f_1168_);
lean_dec_ref(v_url_1167_);
lean_dec_ref(v_repo_1166_);
lean_dec_ref(v_name_1165_);
return v___x_1180_;
}
}
}
else
{
size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1174_, v___x_1181_, v___x_1182_, v___x_1176_, v_a_1164_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_dec_ref(v___x_1183_);
goto v___jp_1171_;
}
else
{
lean_dec(v_rev_x3f_1168_);
lean_dec_ref(v_url_1167_);
lean_dec_ref(v_repo_1166_);
lean_dec_ref(v_name_1165_);
return v___x_1183_;
}
}
}
v___jp_1171_:
{
if (v___x_1170_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1164_, v_name_1165_, v_repo_1166_, v_url_1167_, v_rev_x3f_1168_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1164_, v_name_1165_, v_repo_1166_, v_url_1167_, v_rev_x3f_1168_);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1184_, lean_object* v_name_1185_, lean_object* v_repo_1186_, lean_object* v_url_1187_, lean_object* v_rev_x3f_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1184_, v_name_1185_, v_repo_1186_, v_url_1187_, v_rev_x3f_1188_);
lean_dec_ref(v_a_1184_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1191_, uint8_t v_inherited_1192_, lean_object* v_lakeEnv_1193_, lean_object* v_wsDir_1194_, lean_object* v_name_1195_, lean_object* v_relPkgDir_1196_, lean_object* v_gitUrl_1197_, lean_object* v_remoteUrl_1198_, lean_object* v_inputRev_x3f_1199_, lean_object* v_subDir_x3f_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_pkgUrlMap_1206_; lean_object* v_name_1207_; lean_object* v_scope_1208_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v_a_1212_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v_val_1223_; lean_object* v_pkgDir_1250_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1278_; lean_object* v_a_1279_; lean_object* v___y_1283_; lean_object* v___x_1360_; 
v_pkgUrlMap_1206_ = lean_ctor_get(v_lakeEnv_1193_, 5);
v_name_1207_ = lean_ctor_get(v_dep_1191_, 0);
v_scope_1208_ = lean_ctor_get(v_dep_1191_, 1);
lean_inc_ref(v_relPkgDir_1196_);
v_pkgDir_1250_ = l_Lake_joinRelative(v_wsDir_1194_, v_relPkgDir_1196_);
v___x_1360_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1206_, v_name_1207_);
if (lean_obj_tag(v___x_1360_) == 0)
{
v___y_1283_ = v_gitUrl_1197_;
goto v___jp_1282_;
}
else
{
lean_object* v_val_1361_; 
lean_dec_ref(v_gitUrl_1197_);
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref(v___x_1360_);
v___y_1283_ = v_val_1361_;
goto v___jp_1282_;
}
v___jp_1203_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
v___jp_1209_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1213_ = l_Lake_defaultConfigFile;
v___x_1214_ = lean_box(0);
lean_inc_ref(v_scope_1208_);
lean_inc(v_name_1207_);
v___x_1215_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1215_, 0, v_name_1207_);
lean_ctor_set(v___x_1215_, 1, v_scope_1208_);
lean_ctor_set(v___x_1215_, 2, v___x_1213_);
lean_ctor_set(v___x_1215_, 3, v___x_1214_);
lean_ctor_set(v___x_1215_, 4, v___y_1210_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*5, v_inherited_1192_);
v___x_1216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1216_, 0, v___y_1211_);
lean_ctor_set(v___x_1216_, 1, v_remoteUrl_1198_);
lean_ctor_set(v___x_1216_, 2, v_a_1212_);
lean_ctor_set(v___x_1216_, 3, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1218_:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_array_get_size(v___y_1220_);
v___x_1225_ = lean_nat_dec_lt(v___y_1222_, v___x_1224_);
if (v___x_1225_ == 0)
{
v___y_1210_ = v___y_1219_;
v___y_1211_ = v___y_1221_;
v_a_1212_ = v_val_1223_;
goto v___jp_1209_;
}
else
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_nat_dec_le(v___x_1224_, v___x_1224_);
if (v___x_1227_ == 0)
{
if (v___x_1225_ == 0)
{
v___y_1210_ = v___y_1219_;
v___y_1211_ = v___y_1221_;
v_a_1212_ = v_val_1223_;
goto v___jp_1209_;
}
else
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = lean_usize_of_nat(v___x_1224_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1220_, v___x_1228_, v___x_1229_, v___x_1226_, v_a_1201_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_dec_ref(v___x_1230_);
v___y_1210_ = v___y_1219_;
v___y_1211_ = v___y_1221_;
v_a_1212_ = v_val_1223_;
goto v___jp_1209_;
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v_val_1223_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_remoteUrl_1198_);
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1224_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1220_, v___x_1239_, v___x_1240_, v___x_1226_, v_a_1201_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_dec_ref(v___x_1241_);
v___y_1210_ = v___y_1219_;
v___y_1211_ = v___y_1221_;
v_a_1212_ = v_val_1223_;
goto v___jp_1209_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_val_1223_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_remoteUrl_1198_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
}
v___jp_1251_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1255_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1255_, 0, v___y_1253_);
lean_ctor_set(v___x_1255_, 1, v___y_1252_);
lean_ctor_set(v___x_1255_, 2, v_inputRev_x3f_1199_);
lean_ctor_set(v___x_1255_, 3, v_subDir_x3f_1200_);
v___x_1256_ = l_Lake_defaultManifestFile;
v___x_1257_ = l_Lake_joinRelative(v_pkgDir_1250_, v___x_1256_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1260_ = l_Lake_Manifest_load(v___x_1257_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v___y_1219_ = v___x_1255_;
v___y_1220_ = v___x_1259_;
v___y_1221_ = v___y_1254_;
v___y_1222_ = v___x_1258_;
v_val_1223_ = v___x_1266_;
goto v___jp_1218_;
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_a_1269_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1260_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1260_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 0);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v___y_1219_ = v___x_1255_;
v___y_1220_ = v___x_1259_;
v___y_1221_ = v___y_1254_;
v___y_1222_ = v___x_1258_;
v_val_1223_ = v___x_1274_;
goto v___jp_1218_;
}
}
}
}
v___jp_1277_:
{
if (lean_obj_tag(v_subDir_x3f_1200_) == 1)
{
lean_object* v_val_1280_; lean_object* v___x_1281_; 
v_val_1280_ = lean_ctor_get(v_subDir_x3f_1200_, 0);
lean_inc(v_val_1280_);
v___x_1281_ = l_Lake_joinRelative(v_relPkgDir_1196_, v_val_1280_);
v___y_1252_ = v_a_1279_;
v___y_1253_ = v___y_1278_;
v___y_1254_ = v___x_1281_;
goto v___jp_1251_;
}
else
{
v___y_1252_ = v_a_1279_;
v___y_1253_ = v___y_1278_;
v___y_1254_ = v_relPkgDir_1196_;
goto v___jp_1251_;
}
}
v___jp_1282_:
{
lean_object* v___x_1284_; 
lean_inc(v_inputRev_x3f_1199_);
lean_inc_ref(v___y_1283_);
lean_inc_ref(v_pkgDir_1250_);
v___x_1284_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1201_, v_name_1195_, v_pkgDir_1250_, v___y_1283_, v_inputRev_x3f_1199_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1350_; 
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v___x_1284_, 0);
lean_dec(v_unused_1351_);
v___x_1286_ = v___x_1284_;
v_isShared_1287_ = v_isSharedCheck_1350_;
goto v_resetjp_1285_;
}
else
{
lean_dec(v___x_1284_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1350_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_pkgDir_1250_);
v___x_1290_ = l_Lake_GitRepo_getHeadRevision(v_pkgDir_1250_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v_a_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
lean_del_object(v___x_1286_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
v_a_1292_ = lean_ctor_get(v___x_1290_, 1);
lean_inc(v_a_1292_);
lean_dec_ref(v___x_1290_);
v___x_1293_ = lean_array_get_size(v_a_1292_);
v___x_1294_ = lean_nat_dec_lt(v___x_1288_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_dec(v_a_1292_);
v___y_1278_ = v___y_1283_;
v_a_1279_ = v_a_1291_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_nat_dec_le(v___x_1293_, v___x_1293_);
if (v___x_1296_ == 0)
{
if (v___x_1294_ == 0)
{
lean_dec(v_a_1292_);
v___y_1278_ = v___y_1283_;
v_a_1279_ = v_a_1291_;
goto v___jp_1277_;
}
else
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_of_nat(v___x_1293_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1292_, v___x_1297_, v___x_1298_, v___x_1295_, v_a_1201_);
lean_dec(v_a_1292_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_dec_ref(v___x_1299_);
v___y_1278_ = v___y_1283_;
v_a_1279_ = v_a_1291_;
goto v___jp_1277_;
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_a_1291_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_pkgDir_1250_);
lean_dec(v_subDir_x3f_1200_);
lean_dec(v_inputRev_x3f_1199_);
lean_dec_ref(v_remoteUrl_1198_);
lean_dec_ref(v_relPkgDir_1196_);
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1293_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1292_, v___x_1308_, v___x_1309_, v___x_1295_, v_a_1201_);
lean_dec(v_a_1292_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_dec_ref(v___x_1310_);
v___y_1278_ = v___y_1283_;
v_a_1279_ = v_a_1291_;
goto v___jp_1277_;
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1291_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_pkgDir_1250_);
lean_dec(v_subDir_x3f_1200_);
lean_dec(v_inputRev_x3f_1199_);
lean_dec_ref(v_remoteUrl_1198_);
lean_dec_ref(v_relPkgDir_1196_);
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_pkgDir_1250_);
lean_dec(v_subDir_x3f_1200_);
lean_dec(v_inputRev_x3f_1199_);
lean_dec_ref(v_remoteUrl_1198_);
lean_dec_ref(v_relPkgDir_1196_);
v_a_1319_ = lean_ctor_get(v___x_1290_, 1);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1290_);
v___x_1320_ = lean_array_get_size(v_a_1319_);
v___x_1321_ = lean_nat_dec_lt(v___x_1288_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_dec(v_a_1319_);
v___x_1322_ = lean_box(0);
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 1);
lean_ctor_set(v___x_1286_, 0, v___x_1322_);
v___x_1324_ = v___x_1286_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
lean_del_object(v___x_1286_);
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_nat_dec_le(v___x_1320_, v___x_1320_);
if (v___x_1327_ == 0)
{
if (v___x_1321_ == 0)
{
lean_dec(v_a_1319_);
goto v___jp_1203_;
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1320_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1319_, v___x_1328_, v___x_1329_, v___x_1326_, v_a_1201_);
lean_dec(v_a_1319_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_dec_ref(v___x_1330_);
goto v___jp_1203_;
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
else
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = lean_usize_of_nat(v___x_1320_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1319_, v___x_1339_, v___x_1340_, v___x_1326_, v_a_1201_);
lean_dec(v_a_1319_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref(v___x_1341_);
goto v___jp_1203_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
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
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_pkgDir_1250_);
lean_dec(v_subDir_x3f_1200_);
lean_dec(v_inputRev_x3f_1199_);
lean_dec_ref(v_remoteUrl_1198_);
lean_dec_ref(v_relPkgDir_1196_);
v_a_1352_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1284_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1284_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1362_, lean_object* v_inherited_1363_, lean_object* v_lakeEnv_1364_, lean_object* v_wsDir_1365_, lean_object* v_name_1366_, lean_object* v_relPkgDir_1367_, lean_object* v_gitUrl_1368_, lean_object* v_remoteUrl_1369_, lean_object* v_inputRev_x3f_1370_, lean_object* v_subDir_x3f_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
uint8_t v_inherited_boxed_1374_; lean_object* v_res_1375_; 
v_inherited_boxed_1374_ = lean_unbox(v_inherited_1363_);
v_res_1375_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1362_, v_inherited_boxed_1374_, v_lakeEnv_1364_, v_wsDir_1365_, v_name_1366_, v_relPkgDir_1367_, v_gitUrl_1368_, v_remoteUrl_1369_, v_inputRev_x3f_1370_, v_subDir_x3f_1371_, v_a_1372_);
lean_dec_ref(v_a_1372_);
lean_dec_ref(v_lakeEnv_1364_);
lean_dec_ref(v_dep_1362_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1376_, lean_object* v_dep_1377_, uint8_t v_inherited_1378_, lean_object* v_lakeEnv_1379_, lean_object* v_wsDir_1380_, lean_object* v_name_1381_, lean_object* v_relPkgDir_1382_, lean_object* v_gitUrl_1383_, lean_object* v_remoteUrl_1384_, lean_object* v_inputRev_x3f_1385_, lean_object* v_subDir_x3f_1386_){
_start:
{
lean_object* v_pkgUrlMap_1391_; lean_object* v_name_1392_; lean_object* v_scope_1393_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v_a_1397_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v_val_1408_; lean_object* v_pkgDir_1435_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1463_; lean_object* v_a_1464_; lean_object* v___y_1468_; lean_object* v___x_1545_; 
v_pkgUrlMap_1391_ = lean_ctor_get(v_lakeEnv_1379_, 5);
v_name_1392_ = lean_ctor_get(v_dep_1377_, 0);
v_scope_1393_ = lean_ctor_get(v_dep_1377_, 1);
lean_inc_ref(v_relPkgDir_1382_);
v_pkgDir_1435_ = l_Lake_joinRelative(v_wsDir_1380_, v_relPkgDir_1382_);
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1391_, v_name_1392_);
if (lean_obj_tag(v___x_1545_) == 0)
{
v___y_1468_ = v_gitUrl_1383_;
goto v___jp_1467_;
}
else
{
lean_object* v_val_1546_; 
lean_dec_ref(v_gitUrl_1383_);
v_val_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref(v___x_1545_);
v___y_1468_ = v_val_1546_;
goto v___jp_1467_;
}
v___jp_1388_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
v___jp_1394_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = l_Lake_defaultConfigFile;
v___x_1399_ = lean_box(0);
lean_inc_ref(v_scope_1393_);
lean_inc(v_name_1392_);
v___x_1400_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1400_, 0, v_name_1392_);
lean_ctor_set(v___x_1400_, 1, v_scope_1393_);
lean_ctor_set(v___x_1400_, 2, v___x_1398_);
lean_ctor_set(v___x_1400_, 3, v___x_1399_);
lean_ctor_set(v___x_1400_, 4, v___y_1396_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*5, v_inherited_1378_);
v___x_1401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1401_, 0, v___y_1395_);
lean_ctor_set(v___x_1401_, 1, v_remoteUrl_1384_);
lean_ctor_set(v___x_1401_, 2, v_a_1397_);
lean_ctor_set(v___x_1401_, 3, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
v___jp_1403_:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_array_get_size(v___y_1405_);
v___x_1410_ = lean_nat_dec_lt(v___y_1407_, v___x_1409_);
if (v___x_1410_ == 0)
{
v___y_1395_ = v___y_1404_;
v___y_1396_ = v___y_1406_;
v_a_1397_ = v_val_1408_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_nat_dec_le(v___x_1409_, v___x_1409_);
if (v___x_1412_ == 0)
{
if (v___x_1410_ == 0)
{
v___y_1395_ = v___y_1404_;
v___y_1396_ = v___y_1406_;
v_a_1397_ = v_val_1408_;
goto v___jp_1394_;
}
else
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1409_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1405_, v___x_1413_, v___x_1414_, v___x_1411_, v_a_1376_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref(v___x_1415_);
v___y_1395_ = v___y_1404_;
v___y_1396_ = v___y_1406_;
v_a_1397_ = v_val_1408_;
goto v___jp_1394_;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_val_1408_);
lean_dec_ref(v___y_1406_);
lean_dec_ref(v___y_1404_);
lean_dec_ref(v_remoteUrl_1384_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1409_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1405_, v___x_1424_, v___x_1425_, v___x_1411_, v_a_1376_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_dec_ref(v___x_1426_);
v___y_1395_ = v___y_1404_;
v___y_1396_ = v___y_1406_;
v_a_1397_ = v_val_1408_;
goto v___jp_1394_;
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec_ref(v_val_1408_);
lean_dec_ref(v___y_1406_);
lean_dec_ref(v___y_1404_);
lean_dec_ref(v_remoteUrl_1384_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
v___jp_1436_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1440_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1438_);
lean_ctor_set(v___x_1440_, 1, v___y_1437_);
lean_ctor_set(v___x_1440_, 2, v_inputRev_x3f_1385_);
lean_ctor_set(v___x_1440_, 3, v_subDir_x3f_1386_);
v___x_1441_ = l_Lake_defaultManifestFile;
v___x_1442_ = l_Lake_joinRelative(v_pkgDir_1435_, v___x_1441_);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1445_ = l_Lake_Manifest_load(v___x_1442_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 1);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
v___y_1404_ = v___y_1439_;
v___y_1405_ = v___x_1444_;
v___y_1406_ = v___x_1440_;
v___y_1407_ = v___x_1443_;
v_val_1408_ = v___x_1451_;
goto v___jp_1403_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_a_1454_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1445_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1445_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 0);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
v___y_1404_ = v___y_1439_;
v___y_1405_ = v___x_1444_;
v___y_1406_ = v___x_1440_;
v___y_1407_ = v___x_1443_;
v_val_1408_ = v___x_1459_;
goto v___jp_1403_;
}
}
}
}
v___jp_1462_:
{
if (lean_obj_tag(v_subDir_x3f_1386_) == 1)
{
lean_object* v_val_1465_; lean_object* v___x_1466_; 
v_val_1465_ = lean_ctor_get(v_subDir_x3f_1386_, 0);
lean_inc(v_val_1465_);
v___x_1466_ = l_Lake_joinRelative(v_relPkgDir_1382_, v_val_1465_);
v___y_1437_ = v_a_1464_;
v___y_1438_ = v___y_1463_;
v___y_1439_ = v___x_1466_;
goto v___jp_1436_;
}
else
{
v___y_1437_ = v_a_1464_;
v___y_1438_ = v___y_1463_;
v___y_1439_ = v_relPkgDir_1382_;
goto v___jp_1436_;
}
}
v___jp_1467_:
{
lean_object* v___x_1469_; 
lean_inc(v_inputRev_x3f_1385_);
lean_inc_ref(v___y_1468_);
lean_inc_ref(v_pkgDir_1435_);
v___x_1469_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1376_, v_name_1381_, v_pkgDir_1435_, v___y_1468_, v_inputRev_x3f_1385_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1535_; 
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1469_, 0);
lean_dec(v_unused_1536_);
v___x_1471_ = v___x_1469_;
v_isShared_1472_ = v_isSharedCheck_1535_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v___x_1469_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1535_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v_pkgDir_1435_);
v___x_1475_ = l_Lake_GitRepo_getHeadRevision(v_pkgDir_1435_, v___x_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_a_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
lean_del_object(v___x_1471_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v_a_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1475_);
v___x_1478_ = lean_array_get_size(v_a_1477_);
v___x_1479_ = lean_nat_dec_lt(v___x_1473_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec(v_a_1477_);
v___y_1463_ = v___y_1468_;
v_a_1464_ = v_a_1476_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_nat_dec_le(v___x_1478_, v___x_1478_);
if (v___x_1481_ == 0)
{
if (v___x_1479_ == 0)
{
lean_dec(v_a_1477_);
v___y_1463_ = v___y_1468_;
v_a_1464_ = v_a_1476_;
goto v___jp_1462_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1478_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1477_, v___x_1482_, v___x_1483_, v___x_1480_, v_a_1376_);
lean_dec(v_a_1477_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec_ref(v___x_1484_);
v___y_1463_ = v___y_1468_;
v_a_1464_ = v_a_1476_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1476_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_pkgDir_1435_);
lean_dec(v_subDir_x3f_1386_);
lean_dec(v_inputRev_x3f_1385_);
lean_dec_ref(v_remoteUrl_1384_);
lean_dec_ref(v_relPkgDir_1382_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
else
{
size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = ((size_t)0ULL);
v___x_1494_ = lean_usize_of_nat(v___x_1478_);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1477_, v___x_1493_, v___x_1494_, v___x_1480_, v_a_1376_);
lean_dec(v_a_1477_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_dec_ref(v___x_1495_);
v___y_1463_ = v___y_1468_;
v_a_1464_ = v_a_1476_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1476_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_pkgDir_1435_);
lean_dec(v_subDir_x3f_1386_);
lean_dec(v_inputRev_x3f_1385_);
lean_dec_ref(v_remoteUrl_1384_);
lean_dec_ref(v_relPkgDir_1382_);
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_pkgDir_1435_);
lean_dec(v_subDir_x3f_1386_);
lean_dec(v_inputRev_x3f_1385_);
lean_dec_ref(v_remoteUrl_1384_);
lean_dec_ref(v_relPkgDir_1382_);
v_a_1504_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1475_);
v___x_1505_ = lean_array_get_size(v_a_1504_);
v___x_1506_ = lean_nat_dec_lt(v___x_1473_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_dec(v_a_1504_);
v___x_1507_ = lean_box(0);
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 1);
lean_ctor_set(v___x_1471_, 0, v___x_1507_);
v___x_1509_ = v___x_1471_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
else
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
lean_del_object(v___x_1471_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_nat_dec_le(v___x_1505_, v___x_1505_);
if (v___x_1512_ == 0)
{
if (v___x_1506_ == 0)
{
lean_dec(v_a_1504_);
goto v___jp_1388_;
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_of_nat(v___x_1505_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1504_, v___x_1513_, v___x_1514_, v___x_1511_, v_a_1376_);
lean_dec(v_a_1504_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_dec_ref(v___x_1515_);
goto v___jp_1388_;
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
else
{
size_t v___x_1524_; size_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = ((size_t)0ULL);
v___x_1525_ = lean_usize_of_nat(v___x_1505_);
v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1504_, v___x_1524_, v___x_1525_, v___x_1511_, v_a_1376_);
lean_dec(v_a_1504_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec_ref(v___x_1526_);
goto v___jp_1388_;
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
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
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_pkgDir_1435_);
lean_dec(v_subDir_x3f_1386_);
lean_dec(v_inputRev_x3f_1385_);
lean_dec_ref(v_remoteUrl_1384_);
lean_dec_ref(v_relPkgDir_1382_);
v_a_1537_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1469_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1469_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1547_, lean_object* v_dep_1548_, lean_object* v_inherited_1549_, lean_object* v_lakeEnv_1550_, lean_object* v_wsDir_1551_, lean_object* v_name_1552_, lean_object* v_relPkgDir_1553_, lean_object* v_gitUrl_1554_, lean_object* v_remoteUrl_1555_, lean_object* v_inputRev_x3f_1556_, lean_object* v_subDir_x3f_1557_, lean_object* v_a_1558_){
_start:
{
uint8_t v_inherited_boxed_1559_; lean_object* v_res_1560_; 
v_inherited_boxed_1559_ = lean_unbox(v_inherited_1549_);
v_res_1560_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1547_, v_dep_1548_, v_inherited_boxed_1559_, v_lakeEnv_1550_, v_wsDir_1551_, v_name_1552_, v_relPkgDir_1553_, v_gitUrl_1554_, v_remoteUrl_1555_, v_inputRev_x3f_1556_, v_subDir_x3f_1557_);
lean_dec_ref(v_lakeEnv_1550_);
lean_dec_ref(v_dep_1548_);
lean_dec_ref(v_a_1547_);
return v_res_1560_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1563_ = lean_string_utf8_byte_size(v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* v_s_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1565_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1566_ = lean_string_utf8_byte_size(v_s_1564_);
v___x_1567_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
v___x_1568_ = lean_nat_dec_le(v___x_1567_, v___x_1566_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec_ref(v_s_1564_);
v___x_1569_ = lean_box(0);
return v___x_1569_;
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_string_memcmp(v_s_1564_, v___x_1565_, v___x_1570_, v___x_1570_, v___x_1567_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_dec_ref(v_s_1564_);
v___x_1572_ = lean_box(0);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_inc_ref(v_s_1564_);
v___x_1573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1573_, 0, v_s_1564_);
lean_ctor_set(v___x_1573_, 1, v___x_1570_);
lean_ctor_set(v___x_1573_, 2, v___x_1566_);
v___x_1574_ = l_String_Slice_pos_x21(v___x_1573_, v___x_1567_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1575_, 0, v_s_1564_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
lean_ctor_set(v___x_1575_, 2, v___x_1566_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* v_s_1577_, lean_object* v_pat_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* v_s_1580_, lean_object* v_pat_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(v_s_1580_, v_pat_1581_);
lean_dec_ref(v_pat_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1586_, lean_object* v_as_1587_, size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_b_1590_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1591_ == 0)
{
lean_inc_ref(v_b_1590_);
return v_b_1590_;
}
else
{
lean_object* v_a_1592_; lean_object* v_version_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_a_1592_ = lean_array_uget_borrowed(v_as_1587_, v_i_1589_);
v_version_1593_ = lean_ctor_get(v_a_1592_, 0);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lake_VerRange_test(v_ver_1586_, v_version_1593_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; size_t v___x_1597_; size_t v___x_1598_; 
v___x_1596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_add(v_i_1589_, v___x_1597_);
v_i_1589_ = v___x_1598_;
v_b_1590_ = v___x_1596_;
goto _start;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_inc(v_a_1592_);
v___x_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_a_1592_);
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1594_);
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1603_, lean_object* v_as_1604_, lean_object* v_sz_1605_, lean_object* v_i_1606_, lean_object* v_b_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1605_);
lean_dec(v_sz_1605_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1606_);
lean_dec(v_i_1606_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1603_, v_as_1604_, v_sz_boxed_1608_, v_i_boxed_1609_, v_b_1607_);
lean_dec_ref(v_b_1607_);
lean_dec_ref(v_as_1604_);
lean_dec_ref(v_ver_1603_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1622_, uint8_t v_inherited_1623_, lean_object* v_lakeEnv_1624_, lean_object* v_wsDir_1625_, lean_object* v_relPkgsDir_1626_, lean_object* v_relParentDir_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v_rev_x3f_1660_; lean_object* v___y_1661_; lean_object* v_name_1664_; lean_object* v_scope_1665_; lean_object* v_version_x3f_1666_; lean_object* v_src_x3f_1667_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v_a_1693_; 
v_name_1664_ = lean_ctor_get(v_dep_1622_, 0);
v_scope_1665_ = lean_ctor_get(v_dep_1622_, 1);
v_version_x3f_1666_ = lean_ctor_get(v_dep_1622_, 2);
v_src_x3f_1667_ = lean_ctor_get(v_dep_1622_, 3);
lean_inc(v_src_x3f_1667_);
if (lean_obj_tag(v_src_x3f_1667_) == 1)
{
lean_object* v_val_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1819_; 
v_val_1736_ = lean_ctor_get(v_src_x3f_1667_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_src_x3f_1667_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1738_ = v_src_x3f_1667_;
v_isShared_1739_ = v_isSharedCheck_1819_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_val_1736_);
lean_dec(v_src_x3f_1667_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1819_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
if (lean_obj_tag(v_val_1736_) == 0)
{
lean_object* v_dir_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1806_; 
lean_inc_ref(v_scope_1665_);
lean_inc(v_name_1664_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_dir_1740_ = lean_ctor_get(v_val_1736_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_val_1736_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1742_ = v_val_1736_;
v_isShared_1743_ = v_isSharedCheck_1806_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_dir_1740_);
lean_dec(v_val_1736_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1806_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_relPkgDir_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v_relPkgDir_1744_ = l_Lake_joinRelative(v_relParentDir_1627_, v_dir_1740_);
lean_inc_ref_n(v_relPkgDir_1744_, 2);
v___x_1745_ = l_Lake_joinRelative(v_wsDir_1625_, v_relPkgDir_1744_);
v___x_1746_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v_relPkgDir_1744_);
v___x_1748_ = v___x_1742_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_relPkgDir_1744_);
v___x_1748_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v_a_1750_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_val_1762_; lean_object* v___x_1788_; 
v___x_1758_ = l_Lake_defaultManifestFile;
v___x_1759_ = l_Lake_joinRelative(v___x_1745_, v___x_1758_);
v___x_1760_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1788_ = l_Lake_Manifest_load(v___x_1759_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 1);
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v_val_1762_ = v___x_1794_;
goto v___jp_1761_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1788_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1788_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 0);
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
v_val_1762_ = v___x_1802_;
goto v___jp_1761_;
}
}
}
v___jp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1751_ = l_Lake_defaultConfigFile;
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1753_, 0, v_name_1664_);
lean_ctor_set(v___x_1753_, 1, v_scope_1665_);
lean_ctor_set(v___x_1753_, 2, v___x_1751_);
lean_ctor_set(v___x_1753_, 3, v___x_1752_);
lean_ctor_set(v___x_1753_, 4, v___x_1748_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*5, v_inherited_1623_);
v___x_1754_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1754_, 0, v_relPkgDir_1744_);
lean_ctor_set(v___x_1754_, 1, v___x_1746_);
lean_ctor_set(v___x_1754_, 2, v_a_1750_);
lean_ctor_set(v___x_1754_, 3, v___x_1753_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set_tag(v___x_1738_, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1754_);
v___x_1756_ = v___x_1738_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
v___jp_1761_:
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1763_ == 0)
{
v_a_1750_ = v_val_1762_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1765_ == 0)
{
if (v___x_1763_ == 0)
{
v_a_1750_ = v_val_1762_;
goto v___jp_1749_;
}
else
{
size_t v___x_1766_; size_t v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = ((size_t)0ULL);
v___x_1767_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1760_, v___x_1766_, v___x_1767_, v___x_1764_, v_a_1628_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_dec_ref(v___x_1768_);
v_a_1750_ = v_val_1762_;
goto v___jp_1749_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_val_1762_);
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_relPkgDir_1744_);
lean_del_object(v___x_1738_);
lean_dec_ref(v_scope_1665_);
lean_dec(v_name_1664_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
size_t v___x_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1760_, v___x_1777_, v___x_1778_, v___x_1764_, v_a_1628_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_dec_ref(v___x_1779_);
v_a_1750_ = v_val_1762_;
goto v___jp_1749_;
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v_val_1762_);
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_relPkgDir_1744_);
lean_del_object(v___x_1738_);
lean_dec_ref(v_scope_1665_);
lean_dec(v_name_1664_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
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
lean_object* v_url_1807_; lean_object* v_rev_1808_; lean_object* v_subDir_1809_; uint8_t v___x_1810_; lean_object* v_sname_1811_; lean_object* v___y_1813_; lean_object* v___x_1816_; 
lean_del_object(v___x_1738_);
lean_dec_ref(v_relParentDir_1627_);
v_url_1807_ = lean_ctor_get(v_val_1736_, 0);
lean_inc_ref_n(v_url_1807_, 2);
v_rev_1808_ = lean_ctor_get(v_val_1736_, 1);
lean_inc(v_rev_1808_);
v_subDir_1809_ = lean_ctor_get(v_val_1736_, 2);
lean_inc(v_subDir_1809_);
lean_dec_ref(v_val_1736_);
v___x_1810_ = 0;
lean_inc(v_name_1664_);
v_sname_1811_ = l_Lean_Name_toString(v_name_1664_, v___x_1810_);
v___x_1816_ = l_Lake_Git_filterUrl_x3f(v_url_1807_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1813_ = v___x_1817_;
goto v___jp_1812_;
}
else
{
lean_object* v_val_1818_; 
v_val_1818_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_val_1818_);
lean_dec_ref(v___x_1816_);
v___y_1813_ = v_val_1818_;
goto v___jp_1812_;
}
v___jp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_inc_ref(v_sname_1811_);
v___x_1814_ = l_Lake_joinRelative(v_relPkgsDir_1626_, v_sname_1811_);
v___x_1815_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1628_, v_dep_1622_, v_inherited_1623_, v_lakeEnv_1624_, v_wsDir_1625_, v_sname_1811_, v___x_1814_, v_url_1807_, v___y_1813_, v_rev_1808_, v_subDir_1809_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
return v___x_1815_;
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_fst_1830_; lean_object* v_snd_1831_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v_a_1861_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v_fst_1996_; lean_object* v_snd_1997_; uint8_t v___x_2024_; lean_object* v_a_2026_; 
lean_dec(v_src_x3f_1667_);
lean_dec_ref(v_relParentDir_1627_);
v___x_1820_ = lean_string_utf8_byte_size(v_scope_1665_);
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_nat_dec_eq(v___x_1820_, v___x_1821_);
if (v___x_2024_ == 0)
{
if (lean_obj_tag(v_version_x3f_1666_) == 1)
{
lean_object* v_val_2036_; lean_object* v___x_2037_; 
v_val_2036_ = lean_ctor_get(v_version_x3f_1666_, 0);
lean_inc(v_val_2036_);
v___x_2037_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_2036_);
if (lean_obj_tag(v___x_2037_) == 1)
{
lean_object* v_val_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_val_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = l_String_Slice_toString(v_val_2038_);
lean_dec(v_val_2038_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
v_a_2026_ = v___x_2044_;
goto v___jp_2025_;
}
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v___x_2037_);
v___x_2047_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2048_ = lean_string_utf8_byte_size(v_val_2036_);
lean_inc(v_val_2036_);
v___x_2049_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_val_2036_, v___x_2047_, v___x_1821_, v___x_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2066_; 
lean_inc(v_name_1664_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2066_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2066_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2054_ = 1;
v___x_2055_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1664_, v___x_2054_);
v___x_2056_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
v___x_2057_ = lean_string_append(v___x_2055_, v___x_2056_);
v___x_2058_ = lean_string_append(v___x_2057_, v_a_2050_);
lean_dec(v_a_2050_);
v___x_2059_ = 3;
v___x_2060_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*1, v___x_2059_);
lean_inc_ref(v_a_1628_);
v___x_2061_ = lean_apply_2(v_a_1628_, v___x_2060_, lean_box(0));
v___x_2062_ = lean_box(0);
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 1);
lean_ctor_set(v___x_2052_, 0, v___x_2062_);
v___x_2064_ = v___x_2052_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2049_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2049_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 2);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
v_a_2026_ = v___x_2072_;
goto v___jp_2025_;
}
}
}
}
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_box(0);
v_a_2026_ = v___x_2075_;
goto v___jp_2025_;
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_inc(v_name_1664_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___x_2076_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1664_, v___x_2024_);
v___x_2077_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
v___x_2079_ = 3;
v___x_2080_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*1, v___x_2079_);
lean_inc_ref(v_a_1628_);
v___x_2081_ = lean_apply_2(v_a_1628_, v___x_2080_, lean_box(0));
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
v___jp_1822_:
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_array_get_size(v_snd_1831_);
v___x_1833_ = lean_nat_dec_lt(v___x_1821_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v_snd_1831_);
v___y_1686_ = v___y_1823_;
v___y_1687_ = v___y_1824_;
v___y_1688_ = v___y_1825_;
v___y_1689_ = v___y_1826_;
v___y_1690_ = v___y_1827_;
v___y_1691_ = v___y_1829_;
v___y_1692_ = v___y_1828_;
v_a_1693_ = v_fst_1830_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = lean_nat_dec_le(v___x_1832_, v___x_1832_);
if (v___x_1835_ == 0)
{
if (v___x_1833_ == 0)
{
lean_dec_ref(v_snd_1831_);
v___y_1686_ = v___y_1823_;
v___y_1687_ = v___y_1824_;
v___y_1688_ = v___y_1825_;
v___y_1689_ = v___y_1826_;
v___y_1690_ = v___y_1827_;
v___y_1691_ = v___y_1829_;
v___y_1692_ = v___y_1828_;
v_a_1693_ = v_fst_1830_;
goto v___jp_1685_;
}
else
{
size_t v___x_1836_; size_t v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = lean_usize_of_nat(v___x_1832_);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1831_, v___x_1836_, v___x_1837_, v___x_1834_, v_a_1628_);
lean_dec_ref(v_snd_1831_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_dec_ref(v___x_1838_);
v___y_1686_ = v___y_1823_;
v___y_1687_ = v___y_1824_;
v___y_1688_ = v___y_1825_;
v___y_1689_ = v___y_1826_;
v___y_1690_ = v___y_1827_;
v___y_1691_ = v___y_1829_;
v___y_1692_ = v___y_1828_;
v_a_1693_ = v_fst_1830_;
goto v___jp_1685_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_fst_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
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
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = lean_usize_of_nat(v___x_1832_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1831_, v___x_1847_, v___x_1848_, v___x_1834_, v_a_1628_);
lean_dec_ref(v_snd_1831_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_dec_ref(v___x_1849_);
v___y_1686_ = v___y_1823_;
v___y_1687_ = v___y_1824_;
v___y_1688_ = v___y_1825_;
v___y_1689_ = v___y_1826_;
v___y_1690_ = v___y_1827_;
v___y_1691_ = v___y_1829_;
v___y_1692_ = v___y_1828_;
v_a_1693_ = v_fst_1830_;
goto v___jp_1685_;
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v_fst_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
v___jp_1858_:
{
if (lean_obj_tag(v_a_1861_) == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_inc_ref(v_scope_1665_);
lean_dec_ref(v_a_1861_);
lean_dec(v___y_1859_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___x_1862_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1863_ = lean_string_append(v_scope_1665_, v___x_1862_);
v___x_1864_ = lean_string_append(v___x_1863_, v___y_1860_);
lean_dec_ref(v___y_1860_);
v___x_1865_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_1866_ = lean_string_append(v___x_1864_, v___x_1865_);
v___x_1867_ = 3;
v___x_1868_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set_uint8(v___x_1868_, sizeof(void*)*1, v___x_1867_);
lean_inc_ref(v_a_1628_);
v___x_1869_ = lean_apply_2(v_a_1628_, v___x_1868_, lean_box(0));
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1992_; 
v_a_1872_ = lean_ctor_get(v_a_1861_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_a_1861_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1874_ = v_a_1861_;
v_isShared_1875_ = v_isSharedCheck_1992_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v_a_1861_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1992_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
if (lean_obj_tag(v_a_1872_) == 0)
{
lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_inc_ref(v_scope_1665_);
lean_del_object(v___x_1874_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___x_1876_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1665_, v___y_1860_, v___y_1859_);
lean_dec_ref(v___y_1860_);
v___x_1877_ = 3;
v___x_1878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*1, v___x_1877_);
lean_inc_ref(v_a_1628_);
v___x_1879_ = lean_apply_2(v_a_1628_, v___x_1878_, lean_box(0));
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
else
{
lean_object* v_val_1882_; lean_object* v___x_1883_; 
v_val_1882_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_val_1882_);
lean_dec_ref(v_a_1872_);
v___x_1883_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_1882_);
if (lean_obj_tag(v___x_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1991_; 
v_val_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1991_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1991_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
if (lean_obj_tag(v_val_1884_) == 0)
{
lean_object* v_url_1888_; lean_object* v_githubUrl_x3f_1889_; lean_object* v_defaultBranch_x3f_1890_; lean_object* v_subDir_x3f_1891_; lean_object* v_name_1892_; lean_object* v_fullName_1893_; lean_object* v___x_1894_; 
v_url_1888_ = lean_ctor_get(v_val_1884_, 1);
lean_inc_ref(v_url_1888_);
v_githubUrl_x3f_1889_ = lean_ctor_get(v_val_1884_, 2);
lean_inc(v_githubUrl_x3f_1889_);
v_defaultBranch_x3f_1890_ = lean_ctor_get(v_val_1884_, 3);
lean_inc(v_defaultBranch_x3f_1890_);
v_subDir_x3f_1891_ = lean_ctor_get(v_val_1884_, 4);
lean_inc(v_subDir_x3f_1891_);
lean_dec_ref(v_val_1884_);
v_name_1892_ = lean_ctor_get(v_val_1882_, 0);
lean_inc_ref(v_name_1892_);
v_fullName_1893_ = lean_ctor_get(v_val_1882_, 1);
lean_inc_ref(v_fullName_1893_);
lean_dec(v_val_1882_);
v___x_1894_ = l_Lake_joinRelative(v_relPkgsDir_1626_, v_name_1892_);
switch(lean_obj_tag(v___y_1859_))
{
case 0:
{
lean_object* v___x_1895_; 
lean_del_object(v___x_1874_);
lean_dec_ref(v___y_1860_);
v___x_1895_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v_defaultBranch_x3f_1890_) == 0)
{
uint8_t v___x_1896_; 
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_fullName_1893_);
lean_dec(v_subDir_x3f_1891_);
lean_dec(v_githubUrl_x3f_1889_);
lean_dec_ref(v_url_1888_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___x_1896_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_box(0);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1897_);
v___x_1899_ = v___x_1886_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
else
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
lean_del_object(v___x_1886_);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1902_ == 0)
{
if (v___x_1896_ == 0)
{
goto v___jp_1630_;
}
else
{
size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1895_, v___x_1903_, v___x_1904_, v___x_1901_, v_a_1628_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_dec_ref(v___x_1905_);
goto v___jp_1630_;
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1895_, v___x_1914_, v___x_1915_, v___x_1901_, v_a_1628_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_dec_ref(v___x_1916_);
goto v___jp_1630_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
}
else
{
lean_object* v_val_1925_; uint8_t v___x_1926_; 
lean_del_object(v___x_1886_);
v_val_1925_ = lean_ctor_get(v_defaultBranch_x3f_1890_, 0);
lean_inc(v_val_1925_);
lean_dec_ref(v_defaultBranch_x3f_1890_);
v___x_1926_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1926_ == 0)
{
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_val_1925_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1928_ == 0)
{
if (v___x_1926_ == 0)
{
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_val_1925_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1895_, v___x_1929_, v___x_1930_, v___x_1927_, v_a_1628_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_dec_ref(v___x_1931_);
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_val_1925_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_val_1925_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_fullName_1893_);
lean_dec(v_subDir_x3f_1891_);
lean_dec(v_githubUrl_x3f_1889_);
lean_dec_ref(v_url_1888_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
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
}
else
{
size_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1895_, v___x_1940_, v___x_1941_, v___x_1927_, v_a_1628_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_dec_ref(v___x_1942_);
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_val_1925_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_val_1925_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_fullName_1893_);
lean_dec(v_subDir_x3f_1891_);
lean_dec(v_githubUrl_x3f_1889_);
lean_dec_ref(v_url_1888_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
lean_dec(v_defaultBranch_x3f_1890_);
lean_del_object(v___x_1886_);
lean_del_object(v___x_1874_);
lean_dec_ref(v___y_1860_);
v_rev_1951_ = lean_ctor_get(v___y_1859_, 0);
lean_inc_ref(v_rev_1951_);
lean_dec_ref(v___y_1859_);
v___x_1952_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1953_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1953_ == 0)
{
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_rev_1951_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1955_ == 0)
{
if (v___x_1953_ == 0)
{
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_rev_1951_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
size_t v___x_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = ((size_t)0ULL);
v___x_1957_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1952_, v___x_1956_, v___x_1957_, v___x_1954_, v_a_1628_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref(v___x_1958_);
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_rev_1951_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v_rev_1951_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_fullName_1893_);
lean_dec(v_subDir_x3f_1891_);
lean_dec(v_githubUrl_x3f_1889_);
lean_dec_ref(v_url_1888_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
else
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = ((size_t)0ULL);
v___x_1968_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1952_, v___x_1967_, v___x_1968_, v___x_1954_, v_a_1628_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_dec_ref(v___x_1969_);
v___y_1655_ = v_subDir_x3f_1891_;
v___y_1656_ = v_githubUrl_x3f_1889_;
v___y_1657_ = v_fullName_1893_;
v___y_1658_ = v___x_1894_;
v___y_1659_ = v_url_1888_;
v_rev_x3f_1660_ = v_rev_1951_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_rev_1951_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_fullName_1893_);
lean_dec(v_subDir_x3f_1891_);
lean_dec(v_githubUrl_x3f_1889_);
lean_dec_ref(v_url_1888_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
default: 
{
lean_object* v_ver_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_defaultBranch_x3f_1890_);
lean_del_object(v___x_1886_);
v_ver_1978_ = lean_ctor_get(v___y_1859_, 0);
lean_inc_ref(v_ver_1978_);
lean_dec_ref(v___y_1859_);
v___x_1979_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___y_1860_);
lean_inc_ref(v_scope_1665_);
lean_inc_ref(v_lakeEnv_1624_);
v___x_1980_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1624_, v_scope_1665_, v___y_1860_, v___x_1979_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v_a_1982_; lean_object* v___x_1984_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
v_a_1982_ = lean_ctor_get(v___x_1980_, 1);
lean_inc(v_a_1982_);
lean_dec_ref(v___x_1980_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v_a_1981_);
v___x_1984_ = v___x_1874_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1981_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
v___y_1823_ = v_subDir_x3f_1891_;
v___y_1824_ = v_ver_1978_;
v___y_1825_ = v_githubUrl_x3f_1889_;
v___y_1826_ = v_fullName_1893_;
v___y_1827_ = v___x_1894_;
v___y_1828_ = v___y_1860_;
v___y_1829_ = v_url_1888_;
v_fst_1830_ = v___x_1984_;
v_snd_1831_ = v_a_1982_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_1986_; lean_object* v_a_1987_; lean_object* v___x_1989_; 
v_a_1986_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1986_);
v_a_1987_ = lean_ctor_get(v___x_1980_, 1);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1980_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 0);
lean_ctor_set(v___x_1874_, 0, v_a_1986_);
v___x_1989_ = v___x_1874_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1986_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
v___y_1823_ = v_subDir_x3f_1891_;
v___y_1824_ = v_ver_1978_;
v___y_1825_ = v_githubUrl_x3f_1889_;
v___y_1826_ = v_fullName_1893_;
v___y_1827_ = v___x_1894_;
v___y_1828_ = v___y_1860_;
v___y_1829_ = v_url_1888_;
v_fst_1830_ = v___x_1989_;
v_snd_1831_ = v_a_1987_;
goto v___jp_1822_;
}
}
}
}
}
else
{
lean_del_object(v___x_1886_);
lean_dec(v_val_1884_);
lean_del_object(v___x_1874_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___y_1634_ = v_val_1882_;
v___y_1635_ = v_a_1628_;
goto v___jp_1633_;
}
}
}
else
{
lean_dec(v___x_1883_);
lean_del_object(v___x_1874_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___y_1634_ = v_val_1882_;
v___y_1635_ = v_a_1628_;
goto v___jp_1633_;
}
}
}
}
}
v___jp_1993_:
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = lean_array_get_size(v_snd_1997_);
v___x_1999_ = lean_nat_dec_lt(v___x_1821_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_dec_ref(v_snd_1997_);
v___y_1859_ = v___y_1994_;
v___y_1860_ = v___y_1995_;
v_a_1861_ = v_fst_1996_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_nat_dec_le(v___x_1998_, v___x_1998_);
if (v___x_2001_ == 0)
{
if (v___x_1999_ == 0)
{
lean_dec_ref(v_snd_1997_);
v___y_1859_ = v___y_1994_;
v___y_1860_ = v___y_1995_;
v_a_1861_ = v_fst_1996_;
goto v___jp_1858_;
}
else
{
size_t v___x_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = lean_usize_of_nat(v___x_1998_);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1997_, v___x_2002_, v___x_2003_, v___x_2000_, v_a_1628_);
lean_dec_ref(v_snd_1997_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_dec_ref(v___x_2004_);
v___y_1859_ = v___y_1994_;
v___y_1860_ = v___y_1995_;
v_a_1861_ = v_fst_1996_;
goto v___jp_1858_;
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v_fst_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
else
{
size_t v___x_2013_; size_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = lean_usize_of_nat(v___x_1998_);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_1997_, v___x_2013_, v___x_2014_, v___x_2000_, v_a_1628_);
lean_dec_ref(v_snd_1997_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_dec_ref(v___x_2015_);
v___y_1859_ = v___y_1994_;
v___y_1860_ = v___y_1995_;
v_a_1861_ = v_fst_1996_;
goto v___jp_1858_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_fst_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v_relPkgsDir_1626_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
v___jp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_inc(v_name_1664_);
v___x_2027_ = l_Lean_Name_toString(v_name_1664_, v___x_2024_);
v___x_2028_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___x_2027_);
lean_inc_ref(v_scope_1665_);
lean_inc_ref(v_lakeEnv_1624_);
v___x_2029_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1624_, v_scope_1665_, v___x_2027_, v___x_2028_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v_a_2031_; lean_object* v___x_2032_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
v_a_2031_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2029_);
v___x_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2032_, 0, v_a_2030_);
v___y_1994_ = v_a_2026_;
v___y_1995_ = v___x_2027_;
v_fst_1996_ = v___x_2032_;
v_snd_1997_ = v_a_2031_;
goto v___jp_1993_;
}
else
{
lean_object* v_a_2033_; lean_object* v_a_2034_; lean_object* v___x_2035_; 
v_a_2033_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2033_);
v_a_2034_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2029_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2033_);
v___y_1994_ = v_a_2026_;
v___y_1995_ = v___x_2027_;
v_fst_1996_ = v___x_2035_;
v_snd_1997_ = v_a_2034_;
goto v___jp_1993_;
}
}
}
v___jp_1630_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
v___jp_1633_:
{
lean_object* v_fullName_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_fullName_1636_ = lean_ctor_get(v___y_1634_, 1);
lean_inc_ref(v_fullName_1636_);
lean_dec_ref(v___y_1634_);
v___x_1637_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1638_ = lean_string_append(v_fullName_1636_, v___x_1637_);
v___x_1639_ = 3;
v___x_1640_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set_uint8(v___x_1640_, sizeof(void*)*1, v___x_1639_);
lean_inc_ref(v___y_1635_);
v___x_1641_ = lean_apply_2(v___y_1635_, v___x_1640_, lean_box(0));
v___x_1642_ = lean_box(0);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
v___jp_1644_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___y_1647_);
v___x_1653_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1622_, v_inherited_1623_, v_lakeEnv_1624_, v_wsDir_1625_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___x_1652_, v___y_1645_, v___y_1646_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
return v___x_1653_;
}
v___jp_1654_:
{
if (lean_obj_tag(v___y_1656_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1645_ = v___y_1655_;
v___y_1646_ = v___y_1661_;
v___y_1647_ = v_rev_x3f_1660_;
v___y_1648_ = v___y_1657_;
v___y_1649_ = v___y_1658_;
v___y_1650_ = v___y_1659_;
v___y_1651_ = v___x_1662_;
goto v___jp_1644_;
}
else
{
lean_object* v_val_1663_; 
v_val_1663_ = lean_ctor_get(v___y_1656_, 0);
lean_inc(v_val_1663_);
lean_dec_ref(v___y_1656_);
v___y_1645_ = v___y_1655_;
v___y_1646_ = v___y_1661_;
v___y_1647_ = v_rev_x3f_1660_;
v___y_1648_ = v___y_1657_;
v___y_1649_ = v___y_1658_;
v___y_1650_ = v___y_1659_;
v___y_1651_ = v_val_1663_;
goto v___jp_1644_;
}
}
v___jp_1668_:
{
lean_object* v_toString_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_toString_1671_ = lean_ctor_get(v___y_1669_, 0);
lean_inc_ref(v_toString_1671_);
lean_dec_ref(v___y_1669_);
v___x_1672_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1673_ = lean_string_append(v_scope_1665_, v___x_1672_);
v___x_1674_ = lean_string_append(v___x_1673_, v___y_1670_);
lean_dec_ref(v___y_1670_);
v___x_1675_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1676_ = lean_string_append(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_string_append(v___x_1676_, v_toString_1671_);
lean_dec_ref(v_toString_1671_);
v___x_1678_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1679_ = lean_string_append(v___x_1677_, v___x_1678_);
v___x_1680_ = 3;
v___x_1681_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*1, v___x_1680_);
lean_inc_ref(v_a_1628_);
v___x_1682_ = lean_apply_2(v_a_1628_, v___x_1681_, lean_box(0));
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
v___jp_1685_:
{
if (lean_obj_tag(v_a_1693_) == 0)
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1709_; 
lean_inc_ref(v_scope_1665_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_a_1693_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_a_1693_, 0);
lean_dec(v_unused_1710_);
v___x_1695_ = v_a_1693_;
v_isShared_1696_ = v_isSharedCheck_1709_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v_a_1693_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1709_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1697_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1698_ = lean_string_append(v_scope_1665_, v___x_1697_);
v___x_1699_ = lean_string_append(v___x_1698_, v___y_1692_);
lean_dec_ref(v___y_1692_);
v___x_1700_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_1701_ = lean_string_append(v___x_1699_, v___x_1700_);
v___x_1702_ = 3;
v___x_1703_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set_uint8(v___x_1703_, sizeof(void*)*1, v___x_1702_);
lean_inc_ref(v_a_1628_);
v___x_1704_ = lean_apply_2(v_a_1628_, v___x_1703_, lean_box(0));
v___x_1705_ = lean_box(0);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 0, v___x_1705_);
v___x_1707_ = v___x_1695_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1712_; size_t v_sz_1713_; size_t v___x_1714_; lean_object* v___x_1715_; lean_object* v_fst_1716_; 
v_a_1711_ = lean_ctor_get(v_a_1693_, 0);
lean_inc(v_a_1711_);
lean_dec_ref(v_a_1693_);
v___x_1712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_1713_ = lean_array_size(v_a_1711_);
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1687_, v_a_1711_, v_sz_1713_, v___x_1714_, v___x_1712_);
lean_dec(v_a_1711_);
v_fst_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_fst_1716_);
lean_dec_ref(v___x_1715_);
if (lean_obj_tag(v_fst_1716_) == 0)
{
lean_inc_ref(v_scope_1665_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v___y_1686_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___y_1669_ = v___y_1687_;
v___y_1670_ = v___y_1692_;
goto v___jp_1668_;
}
else
{
lean_object* v_val_1717_; 
v_val_1717_ = lean_ctor_get(v_fst_1716_, 0);
lean_inc(v_val_1717_);
lean_dec_ref(v_fst_1716_);
if (lean_obj_tag(v_val_1717_) == 1)
{
lean_object* v_val_1718_; lean_object* v_version_1719_; lean_object* v_revision_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref(v___y_1687_);
v_val_1718_ = lean_ctor_get(v_val_1717_, 0);
lean_inc(v_val_1718_);
lean_dec_ref(v_val_1717_);
v_version_1719_ = lean_ctor_get(v_val_1718_, 0);
lean_inc_ref(v_version_1719_);
v_revision_1720_ = lean_ctor_get(v_val_1718_, 1);
lean_inc_ref(v_revision_1720_);
lean_dec(v_val_1718_);
v___x_1721_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1665_);
v___x_1722_ = lean_string_append(v_scope_1665_, v___x_1721_);
v___x_1723_ = lean_string_append(v___x_1722_, v___y_1692_);
lean_dec_ref(v___y_1692_);
v___x_1724_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_1725_ = lean_string_append(v___x_1723_, v___x_1724_);
v___x_1726_ = l_Lake_StdVer_toString(v_version_1719_);
v___x_1727_ = lean_string_append(v___x_1725_, v___x_1726_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
v___x_1730_ = lean_string_append(v___x_1729_, v_revision_1720_);
v___x_1731_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
v___x_1733_ = 1;
v___x_1734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*1, v___x_1733_);
lean_inc_ref(v_a_1628_);
v___x_1735_ = lean_apply_2(v_a_1628_, v___x_1734_, lean_box(0));
v___y_1655_ = v___y_1686_;
v___y_1656_ = v___y_1688_;
v___y_1657_ = v___y_1689_;
v___y_1658_ = v___y_1690_;
v___y_1659_ = v___y_1691_;
v_rev_x3f_1660_ = v_revision_1720_;
v___y_1661_ = v_a_1628_;
goto v___jp_1654_;
}
else
{
lean_inc_ref(v_scope_1665_);
lean_dec(v_val_1717_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v___y_1686_);
lean_dec_ref(v_wsDir_1625_);
lean_dec_ref(v_lakeEnv_1624_);
lean_dec_ref(v_dep_1622_);
v___y_1669_ = v___y_1687_;
v___y_1670_ = v___y_1692_;
goto v___jp_1668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2084_, lean_object* v_inherited_2085_, lean_object* v_lakeEnv_2086_, lean_object* v_wsDir_2087_, lean_object* v_relPkgsDir_2088_, lean_object* v_relParentDir_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
uint8_t v_inherited_boxed_2092_; lean_object* v_res_2093_; 
v_inherited_boxed_2092_ = lean_unbox(v_inherited_2085_);
v_res_2093_ = l_Lake_Dependency_materialize(v_dep_2084_, v_inherited_boxed_2092_, v_lakeEnv_2086_, v_wsDir_2087_, v_relPkgsDir_2088_, v_relParentDir_2089_, v_a_2090_);
lean_dec_ref(v_a_2090_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2099_, lean_object* v_pkgDir_2100_, lean_object* v_relPkgDir_2101_, lean_object* v_remoteUrl_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_a_2106_; lean_object* v_manifestFile_x3f_2109_; 
v_manifestFile_x3f_2109_ = lean_ctor_get(v_manifestEntry_2099_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2109_) == 1)
{
lean_object* v_val_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v_a_2116_; lean_object* v_a_2117_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_val_2110_ = lean_ctor_get(v_manifestFile_x3f_2109_, 0);
v___f_2111_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
lean_inc(v_val_2110_);
v___x_2112_ = l_Lake_joinRelative(v_pkgDir_2100_, v_val_2110_);
v___x_2113_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2146_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2147_ = l_Lake_Manifest_load(v___x_2112_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set_tag(v___x_2150_, 1);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v_a_2116_ = v___x_2153_;
v_a_2117_ = v___x_2146_;
goto v___jp_2115_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
v_a_2156_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2147_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2147_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 0);
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
v_a_2116_ = v___x_2161_;
v_a_2117_ = v___x_2146_;
goto v___jp_2115_;
}
}
}
v___jp_2115_:
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_array_get_size(v_a_2117_);
v___x_2119_ = lean_nat_dec_lt(v___x_2114_, v___x_2118_);
if (v___x_2119_ == 0)
{
v_a_2106_ = v_a_2116_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_nat_dec_le(v___x_2118_, v___x_2118_);
if (v___x_2121_ == 0)
{
if (v___x_2119_ == 0)
{
v_a_2106_ = v_a_2116_;
goto v___jp_2105_;
}
else
{
size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_944__overap_2124_; lean_object* v___x_2125_; 
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2118_);
lean_inc_ref(v_a_2117_);
v___x_944__overap_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2113_, v___f_2111_, v_a_2117_, v___x_2122_, v___x_2123_, v___x_2120_);
lean_inc_ref(v_a_2103_);
v___x_2125_ = lean_apply_2(v___x_944__overap_2124_, v_a_2103_, lean_box(0));
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_dec_ref(v___x_2125_);
v_a_2106_ = v_a_2116_;
goto v___jp_2105_;
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_remoteUrl_2102_);
lean_dec_ref(v_relPkgDir_2101_);
lean_dec_ref(v_manifestEntry_2099_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
else
{
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_954__overap_2136_; lean_object* v___x_2137_; 
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = lean_usize_of_nat(v___x_2118_);
lean_inc_ref(v_a_2117_);
v___x_954__overap_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2113_, v___f_2111_, v_a_2117_, v___x_2134_, v___x_2135_, v___x_2120_);
lean_inc_ref(v_a_2103_);
v___x_2137_ = lean_apply_2(v___x_954__overap_2136_, v_a_2103_, lean_box(0));
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_dec_ref(v___x_2137_);
v_a_2106_ = v_a_2116_;
goto v___jp_2105_;
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_remoteUrl_2102_);
lean_dec_ref(v_relPkgDir_2101_);
lean_dec_ref(v_manifestEntry_2099_);
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2164_; 
lean_dec_ref(v_pkgDir_2100_);
v___x_2164_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v_a_2106_ = v___x_2164_;
goto v___jp_2105_;
}
v___jp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2107_, 0, v_relPkgDir_2101_);
lean_ctor_set(v___x_2107_, 1, v_remoteUrl_2102_);
lean_ctor_set(v___x_2107_, 2, v_a_2106_);
lean_ctor_set(v___x_2107_, 3, v_manifestEntry_2099_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2165_, lean_object* v_pkgDir_2166_, lean_object* v_relPkgDir_2167_, lean_object* v_remoteUrl_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2165_, v_pkgDir_2166_, v_relPkgDir_2167_, v_remoteUrl_2168_, v_a_2169_);
lean_dec_ref(v_a_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2173_, lean_object* v_lakeEnv_2174_, lean_object* v_wsDir_2175_, lean_object* v_relPkgsDir_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v_a_2182_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v_a_2190_; lean_object* v_a_2191_; lean_object* v_src_2218_; 
v_src_2218_ = lean_ctor_get(v_manifestEntry_2173_, 4);
lean_inc_ref(v_src_2218_);
if (lean_obj_tag(v_src_2218_) == 0)
{
lean_object* v_manifestFile_x3f_2219_; lean_object* v_dir_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_relPkgsDir_2176_);
v_manifestFile_x3f_2219_ = lean_ctor_get(v_manifestEntry_2173_, 3);
v_dir_2220_ = lean_ctor_get(v_src_2218_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_src_2218_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2222_ = v_src_2218_;
v_isShared_2223_ = v_isSharedCheck_2283_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_dir_2220_);
lean_dec(v_src_2218_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2283_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v_a_2226_; 
v___x_2224_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
if (lean_obj_tag(v_manifestFile_x3f_2219_) == 1)
{
lean_object* v_val_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_a_2236_; lean_object* v_a_2237_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_val_2231_ = lean_ctor_get(v_manifestFile_x3f_2219_, 0);
lean_inc_ref(v_dir_2220_);
v___x_2232_ = l_Lake_joinRelative(v_wsDir_2175_, v_dir_2220_);
lean_inc(v_val_2231_);
v___x_2233_ = l_Lake_joinRelative(v___x_2232_, v_val_2231_);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2264_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2265_ = l_Lake_Manifest_load(v___x_2233_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set_tag(v___x_2268_, 1);
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
v_a_2236_ = v___x_2271_;
v_a_2237_ = v___x_2264_;
goto v___jp_2235_;
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
v_a_2274_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2265_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2265_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 0);
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
v_a_2236_ = v___x_2279_;
v_a_2237_ = v___x_2264_;
goto v___jp_2235_;
}
}
}
v___jp_2235_:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = lean_array_get_size(v_a_2237_);
v___x_2239_ = lean_nat_dec_lt(v___x_2234_, v___x_2238_);
if (v___x_2239_ == 0)
{
v_a_2226_ = v_a_2236_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_box(0);
v___x_2241_ = lean_nat_dec_le(v___x_2238_, v___x_2238_);
if (v___x_2241_ == 0)
{
if (v___x_2239_ == 0)
{
v_a_2226_ = v_a_2236_;
goto v___jp_2225_;
}
else
{
size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = lean_usize_of_nat(v___x_2238_);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2237_, v___x_2242_, v___x_2243_, v___x_2240_, v_a_2177_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_dec_ref(v___x_2244_);
v_a_2226_ = v_a_2236_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v_a_2236_);
lean_del_object(v___x_2222_);
lean_dec_ref(v_dir_2220_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
size_t v___x_2253_; size_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = lean_usize_of_nat(v___x_2238_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2237_, v___x_2253_, v___x_2254_, v___x_2240_, v_a_2177_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_dec_ref(v___x_2255_);
v_a_2226_ = v_a_2236_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_a_2236_);
lean_del_object(v___x_2222_);
lean_dec_ref(v_dir_2220_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2282_; 
lean_dec_ref(v_wsDir_2175_);
v___x_2282_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v_a_2226_ = v___x_2282_;
goto v___jp_2225_;
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2227_, 0, v_dir_2220_);
lean_ctor_set(v___x_2227_, 1, v___x_2224_);
lean_ctor_set(v___x_2227_, 2, v_a_2226_);
lean_ctor_set(v___x_2227_, 3, v_manifestEntry_2173_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2227_);
v___x_2229_ = v___x_2222_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_name_2284_; lean_object* v_manifestFile_x3f_2285_; lean_object* v_url_2286_; lean_object* v_rev_2287_; lean_object* v_subDir_x3f_2288_; uint8_t v___x_2289_; lean_object* v_sname_2290_; lean_object* v_relGitDir_2291_; lean_object* v_gitDir_2292_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2326_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2342_; uint8_t v_a_2354_; lean_object* v___y_2364_; lean_object* v___y_2365_; uint8_t v_val_2366_; uint8_t v___y_2394_; lean_object* v_a_2395_; uint8_t v___x_2405_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_name_2284_ = lean_ctor_get(v_manifestEntry_2173_, 0);
v_manifestFile_x3f_2285_ = lean_ctor_get(v_manifestEntry_2173_, 3);
v_url_2286_ = lean_ctor_get(v_src_2218_, 0);
lean_inc_ref(v_url_2286_);
v_rev_2287_ = lean_ctor_get(v_src_2218_, 1);
lean_inc_ref(v_rev_2287_);
v_subDir_x3f_2288_ = lean_ctor_get(v_src_2218_, 3);
lean_inc(v_subDir_x3f_2288_);
lean_dec_ref(v_src_2218_);
v___x_2289_ = 0;
lean_inc(v_name_2284_);
v_sname_2290_ = l_Lean_Name_toString(v_name_2284_, v___x_2289_);
lean_inc_ref(v_sname_2290_);
v_relGitDir_2291_ = l_Lake_joinRelative(v_relPkgsDir_2176_, v_sname_2290_);
lean_inc_ref(v_relGitDir_2291_);
v_gitDir_2292_ = l_Lake_joinRelative(v_wsDir_2175_, v_relGitDir_2291_);
v___x_2405_ = l_System_FilePath_isDir(v_gitDir_2292_);
v___x_2438_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2439_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2439_ == 0)
{
goto v___jp_2406_;
}
else
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = lean_box(0);
v___x_2441_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2441_ == 0)
{
if (v___x_2439_ == 0)
{
goto v___jp_2406_;
}
else
{
size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2438_, v___x_2442_, v___x_2443_, v___x_2440_, v_a_2177_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_dec_ref(v___x_2444_);
goto v___jp_2406_;
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec_ref(v_sname_2290_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_rev_2287_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
else
{
size_t v___x_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = ((size_t)0ULL);
v___x_2454_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2438_, v___x_2453_, v___x_2454_, v___x_2440_, v_a_2177_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_dec_ref(v___x_2455_);
goto v___jp_2406_;
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec_ref(v_sname_2290_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_rev_2287_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
v___jp_2293_:
{
if (lean_obj_tag(v_manifestFile_x3f_2285_) == 1)
{
lean_object* v_val_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_val_2297_ = lean_ctor_get(v_manifestFile_x3f_2285_, 0);
lean_inc(v_val_2297_);
v___x_2298_ = l_Lake_joinRelative(v_gitDir_2292_, v_val_2297_);
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2301_ = l_Lake_Manifest_load(v___x_2298_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 1);
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
v___y_2186_ = v___y_2294_;
v___y_2187_ = v___x_2299_;
v___y_2188_ = v___y_2295_;
v___y_2189_ = v___y_2296_;
v_a_2190_ = v___x_2307_;
v_a_2191_ = v___x_2300_;
goto v___jp_2185_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_a_2310_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2301_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2301_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set_tag(v___x_2312_, 0);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
v___y_2186_ = v___y_2294_;
v___y_2187_ = v___x_2299_;
v___y_2188_ = v___y_2295_;
v___y_2189_ = v___y_2296_;
v_a_2190_ = v___x_2315_;
v_a_2191_ = v___x_2300_;
goto v___jp_2185_;
}
}
}
}
else
{
lean_object* v___x_2318_; 
lean_dec_ref(v_gitDir_2292_);
v___x_2318_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2180_ = v___y_2294_;
v___y_2181_ = v___y_2296_;
v_a_2182_ = v___x_2318_;
goto v___jp_2179_;
}
}
v___jp_2319_:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lake_Git_filterUrl_x3f(v_url_2286_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2294_ = v___y_2321_;
v___y_2295_ = v___y_2320_;
v___y_2296_ = v___x_2323_;
goto v___jp_2293_;
}
else
{
lean_object* v_val_2324_; 
v_val_2324_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_val_2324_);
lean_dec_ref(v___x_2322_);
v___y_2294_ = v___y_2321_;
v___y_2295_ = v___y_2320_;
v___y_2296_ = v_val_2324_;
goto v___jp_2293_;
}
}
v___jp_2325_:
{
if (lean_obj_tag(v_subDir_x3f_2288_) == 0)
{
v___y_2320_ = v___y_2326_;
v___y_2321_ = v_relGitDir_2291_;
goto v___jp_2319_;
}
else
{
lean_object* v_val_2327_; lean_object* v___x_2328_; 
v_val_2327_ = lean_ctor_get(v_subDir_x3f_2288_, 0);
lean_inc(v_val_2327_);
lean_dec_ref(v_subDir_x3f_2288_);
v___x_2328_ = l_Lake_joinRelative(v_relGitDir_2291_, v_val_2327_);
v___y_2320_ = v___y_2326_;
v___y_2321_ = v___x_2328_;
goto v___jp_2319_;
}
}
v___jp_2329_:
{
lean_object* v___x_2332_; 
lean_inc_ref(v_gitDir_2292_);
v___x_2332_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2177_, v_sname_2290_, v_gitDir_2292_, v___y_2331_, v___y_2330_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_dec_ref(v___x_2332_);
v___y_2326_ = v_a_2177_;
goto v___jp_2325_;
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
v___jp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_rev_2287_);
lean_inc_ref(v_gitDir_2292_);
v___x_2344_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_2177_, v_sname_2290_, v_gitDir_2292_, v___y_2342_, v___x_2343_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_dec_ref(v___x_2344_);
v___y_2326_ = v_a_2177_;
goto v___jp_2325_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
v___jp_2353_:
{
if (v_a_2354_ == 0)
{
lean_dec_ref(v_sname_2290_);
v___y_2326_ = v_a_2177_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2355_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
v___x_2356_ = lean_string_append(v_sname_2290_, v___x_2355_);
v___x_2357_ = lean_string_append(v___x_2356_, v_gitDir_2292_);
v___x_2358_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_2359_ = lean_string_append(v___x_2357_, v___x_2358_);
v___x_2360_ = 2;
v___x_2361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*1, v___x_2360_);
lean_inc_ref(v_a_2177_);
v___x_2362_ = lean_apply_2(v_a_2177_, v___x_2361_, lean_box(0));
v___y_2326_ = v_a_2177_;
goto v___jp_2325_;
}
}
v___jp_2363_:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = lean_array_get_size(v___y_2364_);
v___x_2368_ = lean_nat_dec_lt(v___y_2365_, v___x_2367_);
if (v___x_2368_ == 0)
{
v_a_2354_ = v_val_2366_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_nat_dec_le(v___x_2367_, v___x_2367_);
if (v___x_2370_ == 0)
{
if (v___x_2368_ == 0)
{
v_a_2354_ = v_val_2366_;
goto v___jp_2353_;
}
else
{
size_t v___x_2371_; size_t v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = ((size_t)0ULL);
v___x_2372_ = lean_usize_of_nat(v___x_2367_);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2364_, v___x_2371_, v___x_2372_, v___x_2369_, v_a_2177_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_dec_ref(v___x_2373_);
v_a_2354_ = v_val_2366_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec_ref(v_sname_2290_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
size_t v___x_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = ((size_t)0ULL);
v___x_2383_ = lean_usize_of_nat(v___x_2367_);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2364_, v___x_2382_, v___x_2383_, v___x_2369_, v_a_2177_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_dec_ref(v___x_2384_);
v_a_2354_ = v_val_2366_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec_ref(v_sname_2290_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
v___jp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2396_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_rev_2287_);
lean_inc_ref(v___x_2397_);
v___x_2398_ = l_Option_instDecidableEq___redArg(v___x_2396_, v_a_2395_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v_pkgUrlMap_2399_; lean_object* v___x_2400_; 
v_pkgUrlMap_2399_ = lean_ctor_get(v_lakeEnv_2174_, 5);
v___x_2400_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2399_, v_name_2284_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_inc_ref(v_url_2286_);
v___y_2330_ = v___x_2397_;
v___y_2331_ = v_url_2286_;
goto v___jp_2329_;
}
else
{
lean_object* v_val_2401_; 
v_val_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_val_2401_);
lean_dec_ref(v___x_2400_);
v___y_2330_ = v___x_2397_;
v___y_2331_ = v_val_2401_;
goto v___jp_2329_;
}
}
else
{
uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_dec_ref(v___x_2397_);
lean_inc_ref(v_gitDir_2292_);
v___x_2402_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_2292_);
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_2402_ == 0)
{
v___y_2364_ = v___x_2404_;
v___y_2365_ = v___x_2403_;
v_val_2366_ = v___y_2394_;
goto v___jp_2363_;
}
else
{
v___y_2364_ = v___x_2404_;
v___y_2365_ = v___x_2403_;
v_val_2366_ = v___x_2289_;
goto v___jp_2363_;
}
}
}
v___jp_2406_:
{
if (v___x_2405_ == 0)
{
lean_object* v_pkgUrlMap_2407_; lean_object* v___x_2408_; 
v_pkgUrlMap_2407_ = lean_ctor_get(v_lakeEnv_2174_, 5);
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2407_, v_name_2284_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_inc_ref(v_url_2286_);
v___y_2342_ = v_url_2286_;
goto v___jp_2341_;
}
else
{
lean_object* v_val_2409_; 
v_val_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2409_);
lean_dec_ref(v___x_2408_);
v___y_2342_ = v_val_2409_;
goto v___jp_2341_;
}
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2410_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_2292_);
v___x_2411_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2410_, v_gitDir_2292_);
v___x_2412_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2413_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2413_ == 0)
{
v___y_2394_ = v___x_2405_;
v_a_2395_ = v___x_2411_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2415_ == 0)
{
if (v___x_2413_ == 0)
{
v___y_2394_ = v___x_2405_;
v_a_2395_ = v___x_2411_;
goto v___jp_2393_;
}
else
{
size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2412_, v___x_2416_, v___x_2417_, v___x_2414_, v_a_2177_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_dec_ref(v___x_2418_);
v___y_2394_ = v___x_2405_;
v_a_2395_ = v___x_2411_;
goto v___jp_2393_;
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v___x_2411_);
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec_ref(v_sname_2290_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_rev_2287_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
else
{
size_t v___x_2427_; size_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = ((size_t)0ULL);
v___x_2428_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2412_, v___x_2427_, v___x_2428_, v___x_2414_, v_a_2177_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_dec_ref(v___x_2429_);
v___y_2394_ = v___x_2405_;
v_a_2395_ = v___x_2411_;
goto v___jp_2393_;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v___x_2411_);
lean_dec_ref(v_gitDir_2292_);
lean_dec_ref(v_relGitDir_2291_);
lean_dec_ref(v_sname_2290_);
lean_dec(v_subDir_x3f_2288_);
lean_dec_ref(v_rev_2287_);
lean_dec_ref(v_url_2286_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
}
}
}
v___jp_2179_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2183_, 0, v___y_2180_);
lean_ctor_set(v___x_2183_, 1, v___y_2181_);
lean_ctor_set(v___x_2183_, 2, v_a_2182_);
lean_ctor_set(v___x_2183_, 3, v_manifestEntry_2173_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
return v___x_2184_;
}
v___jp_2185_:
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = lean_array_get_size(v_a_2191_);
v___x_2193_ = lean_nat_dec_lt(v___y_2187_, v___x_2192_);
if (v___x_2193_ == 0)
{
v___y_2180_ = v___y_2186_;
v___y_2181_ = v___y_2189_;
v_a_2182_ = v_a_2190_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_nat_dec_le(v___x_2192_, v___x_2192_);
if (v___x_2195_ == 0)
{
if (v___x_2193_ == 0)
{
v___y_2180_ = v___y_2186_;
v___y_2181_ = v___y_2189_;
v_a_2182_ = v_a_2190_;
goto v___jp_2179_;
}
else
{
size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = ((size_t)0ULL);
v___x_2197_ = lean_usize_of_nat(v___x_2192_);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2191_, v___x_2196_, v___x_2197_, v___x_2194_, v___y_2188_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_dec_ref(v___x_2198_);
v___y_2180_ = v___y_2186_;
v___y_2181_ = v___y_2189_;
v_a_2182_ = v_a_2190_;
goto v___jp_2179_;
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_a_2190_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
else
{
size_t v___x_2207_; size_t v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = ((size_t)0ULL);
v___x_2208_ = lean_usize_of_nat(v___x_2192_);
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2191_, v___x_2207_, v___x_2208_, v___x_2194_, v___y_2188_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_dec_ref(v___x_2209_);
v___y_2180_ = v___y_2186_;
v___y_2181_ = v___y_2189_;
v_a_2182_ = v_a_2190_;
goto v___jp_2179_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_a_2190_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_manifestEntry_2173_);
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_2464_, lean_object* v_lakeEnv_2465_, lean_object* v_wsDir_2466_, lean_object* v_relPkgsDir_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lake_PackageEntry_materialize(v_manifestEntry_2464_, v_lakeEnv_2465_, v_wsDir_2466_, v_relPkgsDir_2467_, v_a_2468_);
lean_dec_ref(v_a_2468_);
lean_dec_ref(v_lakeEnv_2465_);
return v_res_2470_;
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
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Reservoir(builtin);
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
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Materialize(builtin);
}
#ifdef __cplusplus
}
#endif
