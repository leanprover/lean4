// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: public import Lake.Config.Env public import Lake.Load.Manifest public import Lake.Config.Package import Lake.Util.Git import Lake.Util.IO import Lake.Reservoir
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
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
extern lean_object* l_System_instInhabitedFilePath_default;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
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
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1;
static const lean_closure_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ": package directory not found: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
lean_ctor_set(v___x_922_, 2, v___x_920_);
lean_ctor_set(v___x_922_, 3, v___x_919_);
lean_ctor_set(v___x_922_, 4, v___x_918_);
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
v_manifestEntry_926_ = lean_ctor_get(v_self_925_, 4);
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
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_930_){
_start:
{
lean_object* v_manifestEntry_931_; lean_object* v_name_932_; uint8_t v___x_933_; lean_object* v___x_934_; 
v_manifestEntry_931_ = lean_ctor_get(v_self_930_, 4);
lean_inc_ref(v_manifestEntry_931_);
lean_dec_ref(v_self_930_);
v_name_932_ = lean_ctor_get(v_manifestEntry_931_, 0);
lean_inc(v_name_932_);
lean_dec_ref(v_manifestEntry_931_);
v___x_933_ = 0;
v___x_934_ = l_Lean_Name_toString(v_name_932_, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_935_){
_start:
{
lean_object* v_manifestEntry_936_; lean_object* v_scope_937_; 
v_manifestEntry_936_ = lean_ctor_get(v_self_935_, 4);
v_scope_937_ = lean_ctor_get(v_manifestEntry_936_, 1);
lean_inc_ref(v_scope_937_);
return v_scope_937_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lake_MaterializedDep_scope(v_self_938_);
lean_dec_ref(v_self_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_940_){
_start:
{
lean_object* v_manifestEntry_941_; lean_object* v_manifestFile_x3f_942_; 
v_manifestEntry_941_ = lean_ctor_get(v_self_940_, 4);
v_manifestFile_x3f_942_ = lean_ctor_get(v_manifestEntry_941_, 3);
lean_inc(v_manifestFile_x3f_942_);
return v_manifestFile_x3f_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_943_);
lean_dec_ref(v_self_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_945_){
_start:
{
lean_object* v_manifestEntry_946_; lean_object* v_manifestFile_x3f_947_; 
v_manifestEntry_946_ = lean_ctor_get(v_self_945_, 4);
v_manifestFile_x3f_947_ = lean_ctor_get(v_manifestEntry_946_, 3);
if (lean_obj_tag(v_manifestFile_x3f_947_) == 0)
{
lean_object* v___x_948_; 
v___x_948_ = l_Lake_defaultManifestFile;
return v___x_948_;
}
else
{
lean_object* v_val_949_; 
v_val_949_ = lean_ctor_get(v_manifestFile_x3f_947_, 0);
lean_inc(v_val_949_);
return v_val_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lake_MaterializedDep_relManifestFile(v_self_950_);
lean_dec_ref(v_self_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_952_){
_start:
{
lean_object* v_manifestEntry_953_; lean_object* v_manifestFile_x3f_954_; 
v_manifestEntry_953_ = lean_ctor_get(v_self_952_, 4);
v_manifestFile_x3f_954_ = lean_ctor_get(v_manifestEntry_953_, 3);
if (lean_obj_tag(v_manifestFile_x3f_954_) == 0)
{
lean_object* v_pkgDir_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_pkgDir_955_ = lean_ctor_get(v_self_952_, 0);
lean_inc_ref(v_pkgDir_955_);
lean_dec_ref(v_self_952_);
v___x_956_ = l_Lake_defaultManifestFile;
v___x_957_ = l_Lake_joinRelative(v_pkgDir_955_, v___x_956_);
return v___x_957_;
}
else
{
lean_object* v_pkgDir_958_; lean_object* v_val_959_; lean_object* v___x_960_; 
lean_inc_ref(v_manifestFile_x3f_954_);
v_pkgDir_958_ = lean_ctor_get(v_self_952_, 0);
lean_inc_ref(v_pkgDir_958_);
lean_dec_ref(v_self_952_);
v_val_959_ = lean_ctor_get(v_manifestFile_x3f_954_, 0);
lean_inc(v_val_959_);
lean_dec_ref(v_manifestFile_x3f_954_);
v___x_960_ = l_Lake_joinRelative(v_pkgDir_958_, v_val_959_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_961_){
_start:
{
lean_object* v_manifestEntry_962_; lean_object* v_configFile_963_; 
v_manifestEntry_962_ = lean_ctor_get(v_self_961_, 4);
v_configFile_963_ = lean_ctor_get(v_manifestEntry_962_, 2);
lean_inc_ref(v_configFile_963_);
return v_configFile_963_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lake_MaterializedDep_relConfigFile(v_self_964_);
lean_dec_ref(v_self_964_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_966_){
_start:
{
lean_object* v_manifestEntry_967_; lean_object* v_pkgDir_968_; lean_object* v_configFile_969_; lean_object* v___x_970_; 
v_manifestEntry_967_ = lean_ctor_get(v_self_966_, 4);
lean_inc_ref(v_manifestEntry_967_);
v_pkgDir_968_ = lean_ctor_get(v_self_966_, 0);
lean_inc_ref(v_pkgDir_968_);
lean_dec_ref(v_self_966_);
v_configFile_969_ = lean_ctor_get(v_manifestEntry_967_, 2);
lean_inc_ref(v_configFile_969_);
lean_dec_ref(v_manifestEntry_967_);
v___x_970_ = l_Lake_joinRelative(v_pkgDir_968_, v_configFile_969_);
return v___x_970_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_971_){
_start:
{
lean_object* v_manifest_x3f_972_; 
v_manifest_x3f_972_ = lean_ctor_get(v_self_971_, 3);
if (lean_obj_tag(v_manifest_x3f_972_) == 1)
{
lean_object* v_a_973_; uint8_t v_fixedToolchain_974_; 
v_a_973_ = lean_ctor_get(v_manifest_x3f_972_, 0);
v_fixedToolchain_974_ = lean_ctor_get_uint8(v_a_973_, sizeof(void*)*4);
return v_fixedToolchain_974_;
}
else
{
uint8_t v___x_975_; 
v___x_975_ = 0;
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Lake_MaterializedDep_fixedToolchain(v_self_976_);
lean_dec_ref(v_self_976_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* v_x_979_){
_start:
{
switch(lean_obj_tag(v_x_979_))
{
case 0:
{
lean_object* v___x_980_; 
v___x_980_ = lean_unsigned_to_nat(0u);
return v___x_980_;
}
case 1:
{
lean_object* v___x_981_; 
v___x_981_ = lean_unsigned_to_nat(1u);
return v___x_981_;
}
default: 
{
lean_object* v___x_982_; 
v___x_982_ = lean_unsigned_to_nat(2u);
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* v_x_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_983_);
lean_dec(v_x_983_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* v_t_985_, lean_object* v_k_986_){
_start:
{
if (lean_obj_tag(v_t_985_) == 0)
{
return v_k_986_;
}
else
{
lean_object* v_rev_987_; lean_object* v___x_988_; 
v_rev_987_ = lean_ctor_get(v_t_985_, 0);
lean_inc_ref(v_rev_987_);
lean_dec(v_t_985_);
v___x_988_ = lean_apply_1(v_k_986_, v_rev_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* v_motive_989_, lean_object* v_ctorIdx_990_, lean_object* v_t_991_, lean_object* v_h_992_, lean_object* v_k_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_991_, v_k_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* v_motive_995_, lean_object* v_ctorIdx_996_, lean_object* v_t_997_, lean_object* v_h_998_, lean_object* v_k_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(v_motive_995_, v_ctorIdx_996_, v_t_997_, v_h_998_, v_k_999_);
lean_dec(v_ctorIdx_996_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* v_t_1001_, lean_object* v_none_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1001_, v_none_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* v_motive_1004_, lean_object* v_t_1005_, lean_object* v_h_1006_, lean_object* v_none_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1005_, v_none_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* v_t_1009_, lean_object* v_git_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1009_, v_git_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* v_motive_1012_, lean_object* v_t_1013_, lean_object* v_h_1014_, lean_object* v_git_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1013_, v_git_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* v_t_1017_, lean_object* v_ver_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1017_, v_ver_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* v_motive_1020_, lean_object* v_t_1021_, lean_object* v_h_1022_, lean_object* v_ver_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1021_, v_ver_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_scope_1033_, lean_object* v_name_1034_, lean_object* v_ver_1035_){
_start:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; 
switch(lean_obj_tag(v_ver_1035_))
{
case 0:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1037_ = v___x_1059_;
v_snd_1038_ = v___x_1059_;
goto v___jp_1036_;
}
case 1:
{
lean_object* v_rev_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1075_; 
v_rev_1060_ = lean_ctor_get(v_ver_1035_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_ver_1035_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1062_ = v_ver_1035_;
v_isShared_1063_ = v_isSharedCheck_1075_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_rev_1060_);
lean_dec(v_ver_1035_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1075_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1064_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1065_ = l_String_quote(v_rev_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 3);
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1068_ = l_Std_Format_defWidth;
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = l_Std_Format_pretty(v___x_1067_, v___x_1068_, v___x_1069_, v___x_1069_);
v___x_1071_ = lean_string_append(v___x_1064_, v___x_1070_);
v___x_1072_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1073_ = lean_string_append(v___x_1072_, v___x_1070_);
lean_dec_ref(v___x_1070_);
v_fst_1037_ = v___x_1071_;
v_snd_1038_ = v___x_1073_;
goto v___jp_1036_;
}
}
}
default: 
{
lean_object* v_ver_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1092_; 
v_ver_1076_ = lean_ctor_get(v_ver_1035_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_ver_1035_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1078_ = v_ver_1035_;
v_isShared_1079_ = v_isSharedCheck_1092_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_ver_1076_);
lean_dec(v_ver_1035_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1092_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_toString_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v_toString_1080_ = lean_ctor_get(v_ver_1076_, 0);
lean_inc_ref(v_toString_1080_);
lean_dec_ref(v_ver_1076_);
v___x_1081_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1082_ = l_String_quote(v_toString_1080_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 3);
lean_ctor_set(v___x_1078_, 0, v___x_1082_);
v___x_1084_ = v___x_1078_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1085_ = l_Std_Format_defWidth;
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = l_Std_Format_pretty(v___x_1084_, v___x_1085_, v___x_1086_, v___x_1086_);
v___x_1088_ = lean_string_append(v___x_1081_, v___x_1087_);
v___x_1089_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1090_ = lean_string_append(v___x_1089_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v_fst_1037_ = v___x_1088_;
v_snd_1038_ = v___x_1090_;
goto v___jp_1036_;
}
}
}
}
v___jp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1039_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1033_);
v___x_1040_ = lean_string_append(v_scope_1033_, v___x_1039_);
v___x_1041_ = lean_string_append(v___x_1040_, v_name_1034_);
v___x_1042_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1043_ = lean_string_append(v___x_1041_, v___x_1042_);
v___x_1044_ = lean_string_append(v___x_1043_, v_scope_1033_);
v___x_1045_ = lean_string_append(v___x_1044_, v___x_1039_);
v___x_1046_ = lean_string_append(v___x_1045_, v_name_1034_);
v___x_1047_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_string_append(v___x_1048_, v_fst_1037_);
lean_dec_ref(v_fst_1037_);
v___x_1050_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
v___x_1052_ = lean_string_append(v___x_1051_, v_scope_1033_);
lean_dec_ref(v_scope_1033_);
v___x_1053_ = lean_string_append(v___x_1052_, v___x_1039_);
v___x_1054_ = lean_string_append(v___x_1053_, v_name_1034_);
v___x_1055_ = lean_string_append(v___x_1054_, v___x_1047_);
v___x_1056_ = lean_string_append(v___x_1055_, v_snd_1038_);
lean_dec_ref(v_snd_1038_);
v___x_1057_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* v_scope_1093_, lean_object* v_name_1094_, lean_object* v_ver_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1093_, v_name_1094_, v_ver_1095_);
lean_dec_ref(v_name_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_inc_ref(v___y_1099_);
v___x_1101_ = lean_apply_2(v___y_1099_, v___y_1098_, lean_box(0));
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(v_x_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref(v___y_1105_);
return v_res_1107_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0(void){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_instMonadEIO(lean_box(0));
return v___x_1108_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0);
v___x_1110_ = l_ReaderT_instMonad___redArg(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1113_, uint8_t v_inherited_1114_, lean_object* v_wsDir_1115_, lean_object* v_name_1116_, lean_object* v_relPkgDir_1117_, lean_object* v_remoteUrl_1118_, lean_object* v_src_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___y_1123_; lean_object* v_a_1124_; lean_object* v_pkgDir_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___f_1144_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v_val_1150_; lean_object* v_a_1180_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_val_1214_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
lean_inc_ref(v_relPkgDir_1117_);
v_pkgDir_1141_ = l_Lake_joinRelative(v_wsDir_1115_, v_relPkgDir_1117_);
v___x_1142_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_1141_);
v___x_1143_ = l_Lake_resolvePath(v_pkgDir_1141_);
v___f_1144_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1242_ = lean_string_utf8_byte_size(v___x_1143_);
v___x_1243_ = lean_nat_dec_eq(v___x_1242_, v___x_1211_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1143_);
v_val_1214_ = v___x_1244_;
goto v___jp_1213_;
}
else
{
lean_object* v___x_1245_; 
lean_dec_ref(v___x_1143_);
v___x_1245_ = lean_box(0);
v_val_1214_ = v___x_1245_;
goto v___jp_1213_;
}
v___jp_1122_:
{
lean_object* v_name_1125_; lean_object* v_scope_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1137_; 
v_name_1125_ = lean_ctor_get(v_dep_1113_, 0);
v_scope_1126_ = lean_ctor_get(v_dep_1113_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_dep_1113_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1138_ = lean_ctor_get(v_dep_1113_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_dep_1113_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_dep_1113_, 2);
lean_dec(v_unused_1140_);
v___x_1128_ = v_dep_1113_;
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_scope_1126_);
lean_inc(v_name_1125_);
lean_dec(v_dep_1113_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1130_ = l_Lake_defaultConfigFile;
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1132_, 0, v_name_1125_);
lean_ctor_set(v___x_1132_, 1, v_scope_1126_);
lean_ctor_set(v___x_1132_, 2, v___x_1130_);
lean_ctor_set(v___x_1132_, 3, v___x_1131_);
lean_ctor_set(v___x_1132_, 4, v_src_1119_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*5, v_inherited_1114_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v___x_1132_);
lean_ctor_set(v___x_1128_, 3, v_a_1124_);
lean_ctor_set(v___x_1128_, 2, v_remoteUrl_1118_);
lean_ctor_set(v___x_1128_, 1, v_relPkgDir_1117_);
lean_ctor_set(v___x_1128_, 0, v___y_1123_);
v___x_1134_ = v___x_1128_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___y_1123_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_relPkgDir_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_remoteUrl_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_a_1124_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
}
v___jp_1145_:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_array_get_size(v___y_1149_);
v___x_1152_ = lean_nat_dec_lt(v___y_1147_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_dec_ref(v___y_1148_);
v___y_1123_ = v___y_1146_;
v_a_1124_ = v_val_1150_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_nat_dec_le(v___x_1151_, v___x_1151_);
if (v___x_1154_ == 0)
{
if (v___x_1152_ == 0)
{
lean_dec_ref(v___y_1148_);
v___y_1123_ = v___y_1146_;
v_a_1124_ = v_val_1150_;
goto v___jp_1122_;
}
else
{
size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_2388__overap_1157_; lean_object* v___x_1158_; 
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = lean_usize_of_nat(v___x_1151_);
lean_inc_ref(v___y_1149_);
v___x_2388__overap_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1148_, v___f_1144_, v___y_1149_, v___x_1155_, v___x_1156_, v___x_1153_);
lean_inc_ref(v_a_1120_);
v___x_1158_ = lean_apply_2(v___x_2388__overap_1157_, v_a_1120_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_dec_ref(v___x_1158_);
v___y_1123_ = v___y_1146_;
v_a_1124_ = v_val_1150_;
goto v___jp_1122_;
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_val_1150_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_src_1119_);
lean_dec_ref(v_remoteUrl_1118_);
lean_dec_ref(v_relPkgDir_1117_);
lean_dec_ref(v_dep_1113_);
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
else
{
size_t v___x_1167_; size_t v___x_1168_; lean_object* v___x_2398__overap_1169_; lean_object* v___x_1170_; 
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = lean_usize_of_nat(v___x_1151_);
lean_inc_ref(v___y_1149_);
v___x_2398__overap_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1148_, v___f_1144_, v___y_1149_, v___x_1167_, v___x_1168_, v___x_1153_);
lean_inc_ref(v_a_1120_);
v___x_1170_ = lean_apply_2(v___x_2398__overap_1169_, v_a_1120_, lean_box(0));
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_dec_ref(v___x_1170_);
v___y_1123_ = v___y_1146_;
v_a_1124_ = v_val_1150_;
goto v___jp_1122_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_val_1150_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_src_1119_);
lean_dec_ref(v_remoteUrl_1118_);
lean_dec_ref(v_relPkgDir_1117_);
lean_dec_ref(v_dep_1113_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
v___jp_1179_:
{
if (lean_obj_tag(v_a_1180_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec_ref(v_pkgDir_1141_);
lean_dec_ref(v_name_1116_);
v_val_1181_ = lean_ctor_get(v_a_1180_, 0);
lean_inc_n(v_val_1181_, 2);
lean_dec_ref(v_a_1180_);
v___x_1182_ = l_Lake_defaultManifestFile;
v___x_1183_ = l_Lake_joinRelative(v_val_1181_, v___x_1182_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1186_ = l_Lake_Manifest_load(v___x_1183_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 1);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
v___y_1146_ = v_val_1181_;
v___y_1147_ = v___x_1184_;
v___y_1148_ = v___x_1142_;
v___y_1149_ = v___x_1185_;
v_val_1150_ = v___x_1192_;
goto v___jp_1145_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1186_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1186_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 0);
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v___y_1146_ = v_val_1181_;
v___y_1147_ = v___x_1184_;
v___y_1148_ = v___x_1142_;
v___y_1149_ = v___x_1185_;
v_val_1150_ = v___x_1200_;
goto v___jp_1145_;
}
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec(v_a_1180_);
lean_dec_ref(v_src_1119_);
lean_dec_ref(v_remoteUrl_1118_);
lean_dec_ref(v_relPkgDir_1117_);
lean_dec_ref(v_dep_1113_);
v___x_1203_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1204_ = lean_string_append(v_name_1116_, v___x_1203_);
v___x_1205_ = lean_string_append(v___x_1204_, v_pkgDir_1141_);
lean_dec_ref(v_pkgDir_1141_);
v___x_1206_ = 3;
v___x_1207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set_uint8(v___x_1207_, sizeof(void*)*1, v___x_1206_);
lean_inc_ref(v_a_1120_);
v___x_1208_ = lean_apply_2(v_a_1120_, v___x_1207_, lean_box(0));
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
}
v___jp_1213_:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1215_ == 0)
{
v_a_1180_ = v_val_1214_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1217_ == 0)
{
if (v___x_1215_ == 0)
{
v_a_1180_ = v_val_1214_;
goto v___jp_1179_;
}
else
{
size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_2450__overap_1220_; lean_object* v___x_1221_; 
v___x_1218_ = ((size_t)0ULL);
v___x_1219_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2450__overap_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1142_, v___f_1144_, v___x_1212_, v___x_1218_, v___x_1219_, v___x_1216_);
lean_inc_ref(v_a_1120_);
v___x_1221_ = lean_apply_2(v___x_2450__overap_1220_, v_a_1120_, lean_box(0));
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_dec_ref(v___x_1221_);
v_a_1180_ = v_val_1214_;
goto v___jp_1179_;
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_val_1214_);
lean_dec_ref(v_pkgDir_1141_);
lean_dec_ref(v_src_1119_);
lean_dec_ref(v_remoteUrl_1118_);
lean_dec_ref(v_relPkgDir_1117_);
lean_dec_ref(v_name_1116_);
lean_dec_ref(v_dep_1113_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
else
{
size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_2460__overap_1232_; lean_object* v___x_1233_; 
v___x_1230_ = ((size_t)0ULL);
v___x_1231_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2460__overap_1232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1142_, v___f_1144_, v___x_1212_, v___x_1230_, v___x_1231_, v___x_1216_);
lean_inc_ref(v_a_1120_);
v___x_1233_ = lean_apply_2(v___x_2460__overap_1232_, v_a_1120_, lean_box(0));
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_dec_ref(v___x_1233_);
v_a_1180_ = v_val_1214_;
goto v___jp_1179_;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_val_1214_);
lean_dec_ref(v_pkgDir_1141_);
lean_dec_ref(v_src_1119_);
lean_dec_ref(v_remoteUrl_1118_);
lean_dec_ref(v_relPkgDir_1117_);
lean_dec_ref(v_name_1116_);
lean_dec_ref(v_dep_1113_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1246_, lean_object* v_inherited_1247_, lean_object* v_wsDir_1248_, lean_object* v_name_1249_, lean_object* v_relPkgDir_1250_, lean_object* v_remoteUrl_1251_, lean_object* v_src_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
uint8_t v_inherited_boxed_1255_; lean_object* v_res_1256_; 
v_inherited_boxed_1255_ = lean_unbox(v_inherited_1247_);
v_res_1256_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1246_, v_inherited_boxed_1255_, v_wsDir_1248_, v_name_1249_, v_relPkgDir_1250_, v_remoteUrl_1251_, v_src_1252_, v_a_1253_);
lean_dec_ref(v_a_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1257_, lean_object* v_name_1258_, lean_object* v_repo_1259_, lean_object* v_url_1260_, lean_object* v_rev_x3f_1261_){
_start:
{
uint8_t v___x_1263_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1263_ = l_System_FilePath_isDir(v_repo_1259_);
v___x_1267_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1268_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1268_ == 0)
{
goto v___jp_1264_;
}
else
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1270_ == 0)
{
if (v___x_1268_ == 0)
{
goto v___jp_1264_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1267_, v___x_1271_, v___x_1272_, v___x_1269_, v_a_1257_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_dec_ref(v___x_1273_);
goto v___jp_1264_;
}
else
{
lean_dec(v_rev_x3f_1261_);
lean_dec_ref(v_url_1260_);
lean_dec_ref(v_repo_1259_);
lean_dec_ref(v_name_1258_);
return v___x_1273_;
}
}
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1267_, v___x_1274_, v___x_1275_, v___x_1269_, v_a_1257_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_dec_ref(v___x_1276_);
goto v___jp_1264_;
}
else
{
lean_dec(v_rev_x3f_1261_);
lean_dec_ref(v_url_1260_);
lean_dec_ref(v_repo_1259_);
lean_dec_ref(v_name_1258_);
return v___x_1276_;
}
}
}
v___jp_1264_:
{
if (v___x_1263_ == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1257_, v_name_1258_, v_repo_1259_, v_url_1260_, v_rev_x3f_1261_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1257_, v_name_1258_, v_repo_1259_, v_url_1260_, v_rev_x3f_1261_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1277_, lean_object* v_name_1278_, lean_object* v_repo_1279_, lean_object* v_url_1280_, lean_object* v_rev_x3f_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1277_, v_name_1278_, v_repo_1279_, v_url_1280_, v_rev_x3f_1281_);
lean_dec_ref(v_a_1277_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1284_, uint8_t v_inherited_1285_, lean_object* v_lakeEnv_1286_, lean_object* v_wsDir_1287_, lean_object* v_name_1288_, lean_object* v_relPkgDir_1289_, lean_object* v_gitUrl_1290_, lean_object* v_remoteUrl_1291_, lean_object* v_inputRev_x3f_1292_, lean_object* v_subDir_x3f_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_pkgUrlMap_1299_; lean_object* v_name_1300_; lean_object* v_scope_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1517_; 
v_pkgUrlMap_1299_ = lean_ctor_get(v_lakeEnv_1286_, 5);
v_name_1300_ = lean_ctor_get(v_dep_1284_, 0);
v_scope_1301_ = lean_ctor_get(v_dep_1284_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_dep_1284_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; 
v_unused_1518_ = lean_ctor_get(v_dep_1284_, 4);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_dep_1284_, 3);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_dep_1284_, 2);
lean_dec(v_unused_1520_);
v___x_1303_ = v_dep_1284_;
v_isShared_1304_ = v_isSharedCheck_1517_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_scope_1301_);
lean_inc(v_name_1300_);
lean_dec(v_dep_1284_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1517_;
goto v_resetjp_1302_;
}
v___jp_1296_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
v_resetjp_1302_:
{
lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v_a_1309_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v_val_1323_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v_a_1354_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v_val_1391_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1432_; lean_object* v_a_1433_; lean_object* v_gitDir_1436_; lean_object* v___y_1438_; lean_object* v___x_1515_; 
lean_inc_ref(v_relPkgDir_1289_);
lean_inc_ref(v_wsDir_1287_);
v_gitDir_1436_ = l_Lake_joinRelative(v_wsDir_1287_, v_relPkgDir_1289_);
v___x_1515_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1299_, v_name_1300_);
if (lean_obj_tag(v___x_1515_) == 0)
{
v___y_1438_ = v_gitUrl_1290_;
goto v___jp_1437_;
}
else
{
lean_object* v_val_1516_; 
lean_dec_ref(v_gitUrl_1290_);
v_val_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_val_1516_);
lean_dec_ref(v___x_1515_);
v___y_1438_ = v_val_1516_;
goto v___jp_1437_;
}
v___jp_1305_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1310_ = l_Lake_defaultConfigFile;
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1312_, 0, v_name_1300_);
lean_ctor_set(v___x_1312_, 1, v_scope_1301_);
lean_ctor_set(v___x_1312_, 2, v___x_1310_);
lean_ctor_set(v___x_1312_, 3, v___x_1311_);
lean_ctor_set(v___x_1312_, 4, v___y_1307_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*5, v_inherited_1285_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 4, v___x_1312_);
lean_ctor_set(v___x_1303_, 3, v_a_1309_);
lean_ctor_set(v___x_1303_, 2, v_remoteUrl_1291_);
lean_ctor_set(v___x_1303_, 1, v___y_1306_);
lean_ctor_set(v___x_1303_, 0, v___y_1308_);
v___x_1314_ = v___x_1303_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___y_1308_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___y_1306_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_remoteUrl_1291_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_a_1309_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
v___jp_1317_:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_array_get_size(v___y_1322_);
v___x_1325_ = lean_nat_dec_lt(v___y_1319_, v___x_1324_);
if (v___x_1325_ == 0)
{
v___y_1306_ = v___y_1318_;
v___y_1307_ = v___y_1320_;
v___y_1308_ = v___y_1321_;
v_a_1309_ = v_val_1323_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_nat_dec_le(v___x_1324_, v___x_1324_);
if (v___x_1327_ == 0)
{
if (v___x_1325_ == 0)
{
v___y_1306_ = v___y_1318_;
v___y_1307_ = v___y_1320_;
v___y_1308_ = v___y_1321_;
v_a_1309_ = v_val_1323_;
goto v___jp_1305_;
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1324_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1322_, v___x_1328_, v___x_1329_, v___x_1326_, v_a_1294_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_dec_ref(v___x_1330_);
v___y_1306_ = v___y_1318_;
v___y_1307_ = v___y_1320_;
v___y_1308_ = v___y_1321_;
v_a_1309_ = v_val_1323_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_val_1323_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1318_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec_ref(v_remoteUrl_1291_);
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
v___x_1340_ = lean_usize_of_nat(v___x_1324_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1322_, v___x_1339_, v___x_1340_, v___x_1326_, v_a_1294_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref(v___x_1341_);
v___y_1306_ = v___y_1318_;
v___y_1307_ = v___y_1320_;
v___y_1308_ = v___y_1321_;
v_a_1309_ = v_val_1323_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_val_1323_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1318_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec_ref(v_remoteUrl_1291_);
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
v___jp_1350_:
{
if (lean_obj_tag(v_a_1354_) == 1)
{
lean_object* v_val_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v___y_1352_);
lean_dec_ref(v_name_1288_);
v_val_1355_ = lean_ctor_get(v_a_1354_, 0);
lean_inc_n(v_val_1355_, 2);
lean_dec_ref(v_a_1354_);
v___x_1356_ = l_Lake_defaultManifestFile;
v___x_1357_ = l_Lake_joinRelative(v_val_1355_, v___x_1356_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1360_ = l_Lake_Manifest_load(v___x_1357_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 1);
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
v___y_1318_ = v___y_1351_;
v___y_1319_ = v___x_1358_;
v___y_1320_ = v___y_1353_;
v___y_1321_ = v_val_1355_;
v___y_1322_ = v___x_1359_;
v_val_1323_ = v___x_1366_;
goto v___jp_1317_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_a_1369_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1360_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1360_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 0);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
v___y_1318_ = v___y_1351_;
v___y_1319_ = v___x_1358_;
v___y_1320_ = v___y_1353_;
v___y_1321_ = v_val_1355_;
v___y_1322_ = v___x_1359_;
v_val_1323_ = v___x_1374_;
goto v___jp_1317_;
}
}
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_a_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v___y_1351_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec_ref(v_remoteUrl_1291_);
v___x_1377_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1378_ = lean_string_append(v_name_1288_, v___x_1377_);
v___x_1379_ = lean_string_append(v___x_1378_, v___y_1352_);
lean_dec_ref(v___y_1352_);
v___x_1380_ = 3;
v___x_1381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*1, v___x_1380_);
lean_inc_ref(v_a_1294_);
v___x_1382_ = lean_apply_2(v_a_1294_, v___x_1381_, lean_box(0));
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
v___jp_1385_:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_array_get_size(v___y_1390_);
v___x_1393_ = lean_nat_dec_lt(v___y_1387_, v___x_1392_);
if (v___x_1393_ == 0)
{
v___y_1351_ = v___y_1386_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___y_1388_;
v_a_1354_ = v_val_1391_;
goto v___jp_1350_;
}
else
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_nat_dec_le(v___x_1392_, v___x_1392_);
if (v___x_1395_ == 0)
{
if (v___x_1393_ == 0)
{
v___y_1351_ = v___y_1386_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___y_1388_;
v_a_1354_ = v_val_1391_;
goto v___jp_1350_;
}
else
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = lean_usize_of_nat(v___x_1392_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1390_, v___x_1396_, v___x_1397_, v___x_1394_, v_a_1294_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_dec_ref(v___x_1398_);
v___y_1351_ = v___y_1386_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___y_1388_;
v_a_1354_ = v_val_1391_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_val_1391_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1386_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_name_1288_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
else
{
size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = lean_usize_of_nat(v___x_1392_);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1390_, v___x_1407_, v___x_1408_, v___x_1394_, v_a_1294_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_dec_ref(v___x_1409_);
v___y_1351_ = v___y_1386_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___y_1388_;
v_a_1354_ = v_val_1391_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec(v_val_1391_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1386_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_name_1288_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
v___jp_1418_:
{
lean_object* v_pkgDir_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
lean_inc_ref(v___y_1421_);
v_pkgDir_1422_ = l_Lake_joinRelative(v_wsDir_1287_, v___y_1421_);
lean_inc_ref(v_pkgDir_1422_);
v___x_1423_ = l_Lake_resolvePath(v_pkgDir_1422_);
v___x_1424_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1424_, 0, v___y_1419_);
lean_ctor_set(v___x_1424_, 1, v___y_1420_);
lean_ctor_set(v___x_1424_, 2, v_inputRev_x3f_1292_);
lean_ctor_set(v___x_1424_, 3, v_subDir_x3f_1293_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1427_ = lean_string_utf8_byte_size(v___x_1423_);
v___x_1428_ = lean_nat_dec_eq(v___x_1427_, v___x_1425_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1423_);
v___y_1386_ = v___y_1421_;
v___y_1387_ = v___x_1425_;
v___y_1388_ = v___x_1424_;
v___y_1389_ = v_pkgDir_1422_;
v___y_1390_ = v___x_1426_;
v_val_1391_ = v___x_1429_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1430_; 
lean_dec_ref(v___x_1423_);
v___x_1430_ = lean_box(0);
v___y_1386_ = v___y_1421_;
v___y_1387_ = v___x_1425_;
v___y_1388_ = v___x_1424_;
v___y_1389_ = v_pkgDir_1422_;
v___y_1390_ = v___x_1426_;
v_val_1391_ = v___x_1430_;
goto v___jp_1385_;
}
}
v___jp_1431_:
{
if (lean_obj_tag(v_subDir_x3f_1293_) == 1)
{
lean_object* v_val_1434_; lean_object* v___x_1435_; 
v_val_1434_ = lean_ctor_get(v_subDir_x3f_1293_, 0);
lean_inc(v_val_1434_);
v___x_1435_ = l_Lake_joinRelative(v_relPkgDir_1289_, v_val_1434_);
v___y_1419_ = v___y_1432_;
v___y_1420_ = v_a_1433_;
v___y_1421_ = v___x_1435_;
goto v___jp_1418_;
}
else
{
v___y_1419_ = v___y_1432_;
v___y_1420_ = v_a_1433_;
v___y_1421_ = v_relPkgDir_1289_;
goto v___jp_1418_;
}
}
v___jp_1437_:
{
lean_object* v___x_1439_; 
lean_inc(v_inputRev_x3f_1292_);
lean_inc_ref(v___y_1438_);
lean_inc_ref(v_gitDir_1436_);
lean_inc_ref(v_name_1288_);
v___x_1439_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1294_, v_name_1288_, v_gitDir_1436_, v___y_1438_, v_inputRev_x3f_1292_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1505_; 
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1506_);
v___x_1441_ = v___x_1439_;
v_isShared_1442_ = v_isSharedCheck_1505_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v___x_1439_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1505_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1445_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1436_, v___x_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
lean_del_object(v___x_1441_);
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
v_a_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1445_);
v___x_1448_ = lean_array_get_size(v_a_1447_);
v___x_1449_ = lean_nat_dec_lt(v___x_1443_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_dec(v_a_1447_);
v___y_1432_ = v___y_1438_;
v_a_1433_ = v_a_1446_;
goto v___jp_1431_;
}
else
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = lean_box(0);
v___x_1451_ = lean_nat_dec_le(v___x_1448_, v___x_1448_);
if (v___x_1451_ == 0)
{
if (v___x_1449_ == 0)
{
lean_dec(v_a_1447_);
v___y_1432_ = v___y_1438_;
v_a_1433_ = v_a_1446_;
goto v___jp_1431_;
}
else
{
size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = ((size_t)0ULL);
v___x_1453_ = lean_usize_of_nat(v___x_1448_);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1447_, v___x_1452_, v___x_1453_, v___x_1450_, v_a_1294_);
lean_dec(v_a_1447_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_dec_ref(v___x_1454_);
v___y_1432_ = v___y_1438_;
v_a_1433_ = v_a_1446_;
goto v___jp_1431_;
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1446_);
lean_dec_ref(v___y_1438_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec(v_subDir_x3f_1293_);
lean_dec(v_inputRev_x3f_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1289_);
lean_dec_ref(v_name_1288_);
lean_dec_ref(v_wsDir_1287_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
else
{
size_t v___x_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = lean_usize_of_nat(v___x_1448_);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1447_, v___x_1463_, v___x_1464_, v___x_1450_, v_a_1294_);
lean_dec(v_a_1447_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_dec_ref(v___x_1465_);
v___y_1432_ = v___y_1438_;
v_a_1433_ = v_a_1446_;
goto v___jp_1431_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_a_1446_);
lean_dec_ref(v___y_1438_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec(v_subDir_x3f_1293_);
lean_dec(v_inputRev_x3f_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1289_);
lean_dec_ref(v_name_1288_);
lean_dec_ref(v_wsDir_1287_);
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
lean_dec_ref(v___y_1438_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec(v_subDir_x3f_1293_);
lean_dec(v_inputRev_x3f_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1289_);
lean_dec_ref(v_name_1288_);
lean_dec_ref(v_wsDir_1287_);
v_a_1474_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1445_);
v___x_1475_ = lean_array_get_size(v_a_1474_);
v___x_1476_ = lean_nat_dec_lt(v___x_1443_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v_a_1474_);
v___x_1477_ = lean_box(0);
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 1);
lean_ctor_set(v___x_1441_, 0, v___x_1477_);
v___x_1479_ = v___x_1441_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
lean_del_object(v___x_1441_);
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_nat_dec_le(v___x_1475_, v___x_1475_);
if (v___x_1482_ == 0)
{
if (v___x_1476_ == 0)
{
lean_dec(v_a_1474_);
goto v___jp_1296_;
}
else
{
size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((size_t)0ULL);
v___x_1484_ = lean_usize_of_nat(v___x_1475_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1474_, v___x_1483_, v___x_1484_, v___x_1481_, v_a_1294_);
lean_dec(v_a_1474_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref(v___x_1485_);
goto v___jp_1296_;
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
else
{
size_t v___x_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = ((size_t)0ULL);
v___x_1495_ = lean_usize_of_nat(v___x_1475_);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1474_, v___x_1494_, v___x_1495_, v___x_1481_, v_a_1294_);
lean_dec(v_a_1474_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_dec_ref(v___x_1496_);
goto v___jp_1296_;
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
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
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_gitDir_1436_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_scope_1301_);
lean_dec(v_name_1300_);
lean_dec(v_subDir_x3f_1293_);
lean_dec(v_inputRev_x3f_1292_);
lean_dec_ref(v_remoteUrl_1291_);
lean_dec_ref(v_relPkgDir_1289_);
lean_dec_ref(v_name_1288_);
lean_dec_ref(v_wsDir_1287_);
v_a_1507_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1439_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1439_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1521_, lean_object* v_inherited_1522_, lean_object* v_lakeEnv_1523_, lean_object* v_wsDir_1524_, lean_object* v_name_1525_, lean_object* v_relPkgDir_1526_, lean_object* v_gitUrl_1527_, lean_object* v_remoteUrl_1528_, lean_object* v_inputRev_x3f_1529_, lean_object* v_subDir_x3f_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
uint8_t v_inherited_boxed_1533_; lean_object* v_res_1534_; 
v_inherited_boxed_1533_ = lean_unbox(v_inherited_1522_);
v_res_1534_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1521_, v_inherited_boxed_1533_, v_lakeEnv_1523_, v_wsDir_1524_, v_name_1525_, v_relPkgDir_1526_, v_gitUrl_1527_, v_remoteUrl_1528_, v_inputRev_x3f_1529_, v_subDir_x3f_1530_, v_a_1531_);
lean_dec_ref(v_a_1531_);
lean_dec_ref(v_lakeEnv_1523_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1535_, lean_object* v_dep_1536_, uint8_t v_inherited_1537_, lean_object* v_lakeEnv_1538_, lean_object* v_wsDir_1539_, lean_object* v_name_1540_, lean_object* v_relPkgDir_1541_, lean_object* v_gitUrl_1542_, lean_object* v_remoteUrl_1543_, lean_object* v_inputRev_x3f_1544_, lean_object* v_subDir_x3f_1545_){
_start:
{
lean_object* v_pkgUrlMap_1550_; lean_object* v_name_1551_; lean_object* v_scope_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1768_; 
v_pkgUrlMap_1550_ = lean_ctor_get(v_lakeEnv_1538_, 5);
v_name_1551_ = lean_ctor_get(v_dep_1536_, 0);
v_scope_1552_ = lean_ctor_get(v_dep_1536_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_dep_1536_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; lean_object* v_unused_1770_; lean_object* v_unused_1771_; 
v_unused_1769_ = lean_ctor_get(v_dep_1536_, 4);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_dep_1536_, 3);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_dep_1536_, 2);
lean_dec(v_unused_1771_);
v___x_1554_ = v_dep_1536_;
v_isShared_1555_ = v_isSharedCheck_1768_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_scope_1552_);
lean_inc(v_name_1551_);
lean_dec(v_dep_1536_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1768_;
goto v_resetjp_1553_;
}
v___jp_1547_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
v_resetjp_1553_:
{
lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v_a_1560_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_val_1574_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v_a_1605_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v_val_1642_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1683_; lean_object* v_a_1684_; lean_object* v_gitDir_1687_; lean_object* v___y_1689_; lean_object* v___x_1766_; 
lean_inc_ref(v_relPkgDir_1541_);
lean_inc_ref(v_wsDir_1539_);
v_gitDir_1687_ = l_Lake_joinRelative(v_wsDir_1539_, v_relPkgDir_1541_);
v___x_1766_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1550_, v_name_1551_);
if (lean_obj_tag(v___x_1766_) == 0)
{
v___y_1689_ = v_gitUrl_1542_;
goto v___jp_1688_;
}
else
{
lean_object* v_val_1767_; 
lean_dec_ref(v_gitUrl_1542_);
v_val_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_val_1767_);
lean_dec_ref(v___x_1766_);
v___y_1689_ = v_val_1767_;
goto v___jp_1688_;
}
v___jp_1556_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1561_ = l_Lake_defaultConfigFile;
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1563_, 0, v_name_1551_);
lean_ctor_set(v___x_1563_, 1, v_scope_1552_);
lean_ctor_set(v___x_1563_, 2, v___x_1561_);
lean_ctor_set(v___x_1563_, 3, v___x_1562_);
lean_ctor_set(v___x_1563_, 4, v___y_1558_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*5, v_inherited_1537_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v___x_1563_);
lean_ctor_set(v___x_1554_, 3, v_a_1560_);
lean_ctor_set(v___x_1554_, 2, v_remoteUrl_1543_);
lean_ctor_set(v___x_1554_, 1, v___y_1557_);
lean_ctor_set(v___x_1554_, 0, v___y_1559_);
v___x_1565_ = v___x_1554_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___y_1559_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___y_1557_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_remoteUrl_1543_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_a_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
v___jp_1568_:
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = lean_array_get_size(v___y_1569_);
v___x_1576_ = lean_nat_dec_lt(v___y_1570_, v___x_1575_);
if (v___x_1576_ == 0)
{
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1573_;
v_a_1560_ = v_val_1574_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_nat_dec_le(v___x_1575_, v___x_1575_);
if (v___x_1578_ == 0)
{
if (v___x_1576_ == 0)
{
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1573_;
v_a_1560_ = v_val_1574_;
goto v___jp_1556_;
}
else
{
size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = lean_usize_of_nat(v___x_1575_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1569_, v___x_1579_, v___x_1580_, v___x_1577_, v_a_1535_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref(v___x_1581_);
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1573_;
v_a_1560_ = v_val_1574_;
goto v___jp_1556_;
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_val_1574_);
lean_dec_ref(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec_ref(v_remoteUrl_1543_);
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
else
{
size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = lean_usize_of_nat(v___x_1575_);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1569_, v___x_1590_, v___x_1591_, v___x_1577_, v_a_1535_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_dec_ref(v___x_1592_);
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1573_;
v_a_1560_ = v_val_1574_;
goto v___jp_1556_;
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_val_1574_);
lean_dec_ref(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec_ref(v_remoteUrl_1543_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
v___jp_1601_:
{
if (lean_obj_tag(v_a_1605_) == 1)
{
lean_object* v_val_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_name_1540_);
v_val_1606_ = lean_ctor_get(v_a_1605_, 0);
lean_inc_n(v_val_1606_, 2);
lean_dec_ref(v_a_1605_);
v___x_1607_ = l_Lake_defaultManifestFile;
v___x_1608_ = l_Lake_joinRelative(v_val_1606_, v___x_1607_);
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1611_ = l_Lake_Manifest_load(v___x_1608_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 1);
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
v___y_1569_ = v___x_1610_;
v___y_1570_ = v___x_1609_;
v___y_1571_ = v___y_1603_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v_val_1606_;
v_val_1574_ = v___x_1617_;
goto v___jp_1568_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1611_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
v___y_1569_ = v___x_1610_;
v___y_1570_ = v___x_1609_;
v___y_1571_ = v___y_1603_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v_val_1606_;
v_val_1574_ = v___x_1625_;
goto v___jp_1568_;
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v_a_1605_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec_ref(v_remoteUrl_1543_);
v___x_1628_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1629_ = lean_string_append(v_name_1540_, v___x_1628_);
v___x_1630_ = lean_string_append(v___x_1629_, v___y_1602_);
lean_dec_ref(v___y_1602_);
v___x_1631_ = 3;
v___x_1632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*1, v___x_1631_);
lean_inc_ref(v_a_1535_);
v___x_1633_ = lean_apply_2(v_a_1535_, v___x_1632_, lean_box(0));
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
}
v___jp_1636_:
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = lean_array_get_size(v___y_1640_);
v___x_1644_ = lean_nat_dec_lt(v___y_1638_, v___x_1643_);
if (v___x_1644_ == 0)
{
v___y_1602_ = v___y_1637_;
v___y_1603_ = v___y_1639_;
v___y_1604_ = v___y_1641_;
v_a_1605_ = v_val_1642_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_nat_dec_le(v___x_1643_, v___x_1643_);
if (v___x_1646_ == 0)
{
if (v___x_1644_ == 0)
{
v___y_1602_ = v___y_1637_;
v___y_1603_ = v___y_1639_;
v___y_1604_ = v___y_1641_;
v_a_1605_ = v_val_1642_;
goto v___jp_1601_;
}
else
{
size_t v___x_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = lean_usize_of_nat(v___x_1643_);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1640_, v___x_1647_, v___x_1648_, v___x_1645_, v_a_1535_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_dec_ref(v___x_1649_);
v___y_1602_ = v___y_1637_;
v___y_1603_ = v___y_1639_;
v___y_1604_ = v___y_1641_;
v_a_1605_ = v_val_1642_;
goto v___jp_1601_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_val_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1637_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec_ref(v_remoteUrl_1543_);
lean_dec_ref(v_name_1540_);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
else
{
size_t v___x_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = ((size_t)0ULL);
v___x_1659_ = lean_usize_of_nat(v___x_1643_);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1640_, v___x_1658_, v___x_1659_, v___x_1645_, v_a_1535_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_dec_ref(v___x_1660_);
v___y_1602_ = v___y_1637_;
v___y_1603_ = v___y_1639_;
v___y_1604_ = v___y_1641_;
v_a_1605_ = v_val_1642_;
goto v___jp_1601_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_val_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1637_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec_ref(v_remoteUrl_1543_);
lean_dec_ref(v_name_1540_);
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
}
v___jp_1669_:
{
lean_object* v_pkgDir_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
lean_inc_ref(v___y_1672_);
v_pkgDir_1673_ = l_Lake_joinRelative(v_wsDir_1539_, v___y_1672_);
lean_inc_ref(v_pkgDir_1673_);
v___x_1674_ = l_Lake_resolvePath(v_pkgDir_1673_);
v___x_1675_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1675_, 0, v___y_1670_);
lean_ctor_set(v___x_1675_, 1, v___y_1671_);
lean_ctor_set(v___x_1675_, 2, v_inputRev_x3f_1544_);
lean_ctor_set(v___x_1675_, 3, v_subDir_x3f_1545_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1678_ = lean_string_utf8_byte_size(v___x_1674_);
v___x_1679_ = lean_nat_dec_eq(v___x_1678_, v___x_1676_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1674_);
v___y_1637_ = v_pkgDir_1673_;
v___y_1638_ = v___x_1676_;
v___y_1639_ = v___y_1672_;
v___y_1640_ = v___x_1677_;
v___y_1641_ = v___x_1675_;
v_val_1642_ = v___x_1680_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1681_; 
lean_dec_ref(v___x_1674_);
v___x_1681_ = lean_box(0);
v___y_1637_ = v_pkgDir_1673_;
v___y_1638_ = v___x_1676_;
v___y_1639_ = v___y_1672_;
v___y_1640_ = v___x_1677_;
v___y_1641_ = v___x_1675_;
v_val_1642_ = v___x_1681_;
goto v___jp_1636_;
}
}
v___jp_1682_:
{
if (lean_obj_tag(v_subDir_x3f_1545_) == 1)
{
lean_object* v_val_1685_; lean_object* v___x_1686_; 
v_val_1685_ = lean_ctor_get(v_subDir_x3f_1545_, 0);
lean_inc(v_val_1685_);
v___x_1686_ = l_Lake_joinRelative(v_relPkgDir_1541_, v_val_1685_);
v___y_1670_ = v___y_1683_;
v___y_1671_ = v_a_1684_;
v___y_1672_ = v___x_1686_;
goto v___jp_1669_;
}
else
{
v___y_1670_ = v___y_1683_;
v___y_1671_ = v_a_1684_;
v___y_1672_ = v_relPkgDir_1541_;
goto v___jp_1669_;
}
}
v___jp_1688_:
{
lean_object* v___x_1690_; 
lean_inc(v_inputRev_x3f_1544_);
lean_inc_ref(v___y_1689_);
lean_inc_ref(v_gitDir_1687_);
lean_inc_ref(v_name_1540_);
v___x_1690_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1535_, v_name_1540_, v_gitDir_1687_, v___y_1689_, v_inputRev_x3f_1544_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1756_; 
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v___x_1690_, 0);
lean_dec(v_unused_1757_);
v___x_1692_ = v___x_1690_;
v_isShared_1693_ = v_isSharedCheck_1756_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v___x_1690_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1756_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_unsigned_to_nat(0u);
v___x_1695_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1696_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1687_, v___x_1695_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v_a_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
lean_del_object(v___x_1692_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
v_a_1698_ = lean_ctor_get(v___x_1696_, 1);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1696_);
v___x_1699_ = lean_array_get_size(v_a_1698_);
v___x_1700_ = lean_nat_dec_lt(v___x_1694_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_dec(v_a_1698_);
v___y_1683_ = v___y_1689_;
v_a_1684_ = v_a_1697_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_nat_dec_le(v___x_1699_, v___x_1699_);
if (v___x_1702_ == 0)
{
if (v___x_1700_ == 0)
{
lean_dec(v_a_1698_);
v___y_1683_ = v___y_1689_;
v_a_1684_ = v_a_1697_;
goto v___jp_1682_;
}
else
{
size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1699_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1698_, v___x_1703_, v___x_1704_, v___x_1701_, v_a_1535_);
lean_dec(v_a_1698_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec_ref(v___x_1705_);
v___y_1683_ = v___y_1689_;
v_a_1684_ = v_a_1697_;
goto v___jp_1682_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_a_1697_);
lean_dec_ref(v___y_1689_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec(v_subDir_x3f_1545_);
lean_dec(v_inputRev_x3f_1544_);
lean_dec_ref(v_remoteUrl_1543_);
lean_dec_ref(v_relPkgDir_1541_);
lean_dec_ref(v_name_1540_);
lean_dec_ref(v_wsDir_1539_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
else
{
size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = lean_usize_of_nat(v___x_1699_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1698_, v___x_1714_, v___x_1715_, v___x_1701_, v_a_1535_);
lean_dec(v_a_1698_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_dec_ref(v___x_1716_);
v___y_1683_ = v___y_1689_;
v_a_1684_ = v_a_1697_;
goto v___jp_1682_;
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1697_);
lean_dec_ref(v___y_1689_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec(v_subDir_x3f_1545_);
lean_dec(v_inputRev_x3f_1544_);
lean_dec_ref(v_remoteUrl_1543_);
lean_dec_ref(v_relPkgDir_1541_);
lean_dec_ref(v_name_1540_);
lean_dec_ref(v_wsDir_1539_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
lean_dec_ref(v___y_1689_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec(v_subDir_x3f_1545_);
lean_dec(v_inputRev_x3f_1544_);
lean_dec_ref(v_remoteUrl_1543_);
lean_dec_ref(v_relPkgDir_1541_);
lean_dec_ref(v_name_1540_);
lean_dec_ref(v_wsDir_1539_);
v_a_1725_ = lean_ctor_get(v___x_1696_, 1);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1696_);
v___x_1726_ = lean_array_get_size(v_a_1725_);
v___x_1727_ = lean_nat_dec_lt(v___x_1694_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec(v_a_1725_);
v___x_1728_ = lean_box(0);
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
lean_ctor_set(v___x_1692_, 0, v___x_1728_);
v___x_1730_ = v___x_1692_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
lean_del_object(v___x_1692_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_nat_dec_le(v___x_1726_, v___x_1726_);
if (v___x_1733_ == 0)
{
if (v___x_1727_ == 0)
{
lean_dec(v_a_1725_);
goto v___jp_1547_;
}
else
{
size_t v___x_1734_; size_t v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = ((size_t)0ULL);
v___x_1735_ = lean_usize_of_nat(v___x_1726_);
v___x_1736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1725_, v___x_1734_, v___x_1735_, v___x_1732_, v_a_1535_);
lean_dec(v_a_1725_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_dec_ref(v___x_1736_);
goto v___jp_1547_;
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
else
{
size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = lean_usize_of_nat(v___x_1726_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1725_, v___x_1745_, v___x_1746_, v___x_1732_, v_a_1535_);
lean_dec(v_a_1725_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_dec_ref(v___x_1747_);
goto v___jp_1547_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
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
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v___y_1689_);
lean_dec_ref(v_gitDir_1687_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_scope_1552_);
lean_dec(v_name_1551_);
lean_dec(v_subDir_x3f_1545_);
lean_dec(v_inputRev_x3f_1544_);
lean_dec_ref(v_remoteUrl_1543_);
lean_dec_ref(v_relPkgDir_1541_);
lean_dec_ref(v_name_1540_);
lean_dec_ref(v_wsDir_1539_);
v_a_1758_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1690_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1690_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1772_, lean_object* v_dep_1773_, lean_object* v_inherited_1774_, lean_object* v_lakeEnv_1775_, lean_object* v_wsDir_1776_, lean_object* v_name_1777_, lean_object* v_relPkgDir_1778_, lean_object* v_gitUrl_1779_, lean_object* v_remoteUrl_1780_, lean_object* v_inputRev_x3f_1781_, lean_object* v_subDir_x3f_1782_, lean_object* v_a_1783_){
_start:
{
uint8_t v_inherited_boxed_1784_; lean_object* v_res_1785_; 
v_inherited_boxed_1784_ = lean_unbox(v_inherited_1774_);
v_res_1785_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1772_, v_dep_1773_, v_inherited_boxed_1784_, v_lakeEnv_1775_, v_wsDir_1776_, v_name_1777_, v_relPkgDir_1778_, v_gitUrl_1779_, v_remoteUrl_1780_, v_inputRev_x3f_1781_, v_subDir_x3f_1782_);
lean_dec_ref(v_lakeEnv_1775_);
lean_dec_ref(v_a_1772_);
return v_res_1785_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1788_ = lean_string_utf8_byte_size(v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* v_s_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1790_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1791_ = lean_string_utf8_byte_size(v_s_1789_);
v___x_1792_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
v___x_1793_ = lean_nat_dec_le(v___x_1792_, v___x_1791_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
lean_dec_ref(v_s_1789_);
v___x_1794_ = lean_box(0);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_string_memcmp(v_s_1789_, v___x_1790_, v___x_1795_, v___x_1795_, v___x_1792_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref(v_s_1789_);
v___x_1797_ = lean_box(0);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_inc_ref(v_s_1789_);
v___x_1798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1798_, 0, v_s_1789_);
lean_ctor_set(v___x_1798_, 1, v___x_1795_);
lean_ctor_set(v___x_1798_, 2, v___x_1791_);
v___x_1799_ = l_String_Slice_pos_x21(v___x_1798_, v___x_1792_);
lean_dec_ref(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1800_, 0, v_s_1789_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
lean_ctor_set(v___x_1800_, 2, v___x_1791_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* v_s_1802_, lean_object* v_pat_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* v_s_1805_, lean_object* v_pat_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(v_s_1805_, v_pat_1806_);
lean_dec_ref(v_pat_1806_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1811_, lean_object* v_as_1812_, size_t v_sz_1813_, size_t v_i_1814_, lean_object* v_b_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_usize_dec_lt(v_i_1814_, v_sz_1813_);
if (v___x_1816_ == 0)
{
lean_inc_ref(v_b_1815_);
return v_b_1815_;
}
else
{
lean_object* v_a_1817_; lean_object* v_version_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v_a_1817_ = lean_array_uget_borrowed(v_as_1812_, v_i_1814_);
v_version_1818_ = lean_ctor_get(v_a_1817_, 0);
v___x_1819_ = lean_box(0);
v___x_1820_ = l_Lake_VerRange_test(v_ver_1811_, v_version_1818_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; size_t v___x_1822_; size_t v___x_1823_; 
v___x_1821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1814_, v___x_1822_);
v_i_1814_ = v___x_1823_;
v_b_1815_ = v___x_1821_;
goto _start;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_inc(v_a_1817_);
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_a_1817_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v___x_1819_);
return v___x_1827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1828_, lean_object* v_as_1829_, lean_object* v_sz_1830_, lean_object* v_i_1831_, lean_object* v_b_1832_){
_start:
{
size_t v_sz_boxed_1833_; size_t v_i_boxed_1834_; lean_object* v_res_1835_; 
v_sz_boxed_1833_ = lean_unbox_usize(v_sz_1830_);
lean_dec(v_sz_1830_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1831_);
lean_dec(v_i_1831_);
v_res_1835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1828_, v_as_1829_, v_sz_boxed_1833_, v_i_boxed_1834_, v_b_1832_);
lean_dec_ref(v_b_1832_);
lean_dec_ref(v_as_1829_);
lean_dec_ref(v_ver_1828_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1847_, uint8_t v_inherited_1848_, lean_object* v_lakeEnv_1849_, lean_object* v_wsDir_1850_, lean_object* v_relPkgsDir_1851_, lean_object* v_relParentDir_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v_rev_x3f_1885_; lean_object* v___y_1886_; lean_object* v_name_1889_; lean_object* v_scope_1890_; lean_object* v_version_x3f_1891_; lean_object* v_src_x3f_1892_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v_a_1918_; 
v_name_1889_ = lean_ctor_get(v_dep_1847_, 0);
v_scope_1890_ = lean_ctor_get(v_dep_1847_, 1);
v_version_x3f_1891_ = lean_ctor_get(v_dep_1847_, 2);
v_src_x3f_1892_ = lean_ctor_get(v_dep_1847_, 3);
lean_inc(v_src_x3f_1892_);
if (lean_obj_tag(v_src_x3f_1892_) == 1)
{
lean_object* v_val_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2106_; 
v_val_1961_ = lean_ctor_get(v_src_x3f_1892_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_src_x3f_1892_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_1963_ = v_src_x3f_1892_;
v_isShared_1964_ = v_isSharedCheck_2106_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_val_1961_);
lean_dec(v_src_x3f_1892_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2106_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
uint8_t v___x_1965_; lean_object* v_sname_1966_; 
v___x_1965_ = 0;
lean_inc(v_name_1889_);
v_sname_1966_ = l_Lean_Name_toString(v_name_1889_, v___x_1965_);
if (lean_obj_tag(v_val_1961_) == 0)
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2090_; 
lean_inc_ref(v_scope_1890_);
lean_inc(v_name_1889_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_lakeEnv_1849_);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_dep_1847_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; lean_object* v_unused_2095_; 
v_unused_2091_ = lean_ctor_get(v_dep_1847_, 4);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_dep_1847_, 3);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_dep_1847_, 2);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_dep_1847_, 1);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_dep_1847_, 0);
lean_dec(v_unused_2095_);
v___x_1968_ = v_dep_1847_;
v_isShared_1969_ = v_isSharedCheck_2090_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v_dep_1847_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2090_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_dir_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2089_; 
v_dir_1970_ = lean_ctor_get(v_val_1961_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_val_1961_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_1972_ = v_val_1961_;
v_isShared_1973_ = v_isSharedCheck_2089_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_dir_1970_);
lean_dec(v_val_1961_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2089_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_relPkgDir_1974_; lean_object* v___x_1976_; 
v_relPkgDir_1974_ = l_Lake_joinRelative(v_relParentDir_1852_, v_dir_1970_);
lean_inc_ref(v_relPkgDir_1974_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_relPkgDir_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_relPkgDir_1974_);
v___x_1976_ = v_reuseFailAlloc_2088_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v_pkgDir_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___y_1981_; lean_object* v_a_1982_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v_val_1994_; lean_object* v_a_2022_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_val_2056_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_inc_ref(v_relPkgDir_1974_);
v_pkgDir_1977_ = l_Lake_joinRelative(v_wsDir_1850_, v_relPkgDir_1974_);
lean_inc_ref(v_pkgDir_1977_);
v___x_1978_ = l_Lake_resolvePath(v_pkgDir_1977_);
v___x_1979_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2082_ = lean_string_utf8_byte_size(v___x_1978_);
v___x_2083_ = lean_nat_dec_eq(v___x_2082_, v___x_2053_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2085_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1978_);
v___x_2085_ = v___x_1963_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_1978_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
v_val_2056_ = v___x_2085_;
goto v___jp_2055_;
}
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref(v___x_1978_);
lean_del_object(v___x_1963_);
v___x_2087_ = lean_box(0);
v_val_2056_ = v___x_2087_;
goto v___jp_2055_;
}
v___jp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1983_ = l_Lake_defaultConfigFile;
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1985_, 0, v_name_1889_);
lean_ctor_set(v___x_1985_, 1, v_scope_1890_);
lean_ctor_set(v___x_1985_, 2, v___x_1983_);
lean_ctor_set(v___x_1985_, 3, v___x_1984_);
lean_ctor_set(v___x_1985_, 4, v___x_1976_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*5, v_inherited_1848_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_1985_);
lean_ctor_set(v___x_1968_, 3, v_a_1982_);
lean_ctor_set(v___x_1968_, 2, v___x_1979_);
lean_ctor_set(v___x_1968_, 1, v_relPkgDir_1974_);
lean_ctor_set(v___x_1968_, 0, v___y_1981_);
v___x_1987_ = v___x_1968_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___y_1981_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_relPkgDir_1974_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_a_1982_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
}
v___jp_1990_:
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_array_get_size(v___y_1993_);
v___x_1996_ = lean_nat_dec_lt(v___y_1992_, v___x_1995_);
if (v___x_1996_ == 0)
{
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_val_1994_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = lean_nat_dec_le(v___x_1995_, v___x_1995_);
if (v___x_1998_ == 0)
{
if (v___x_1996_ == 0)
{
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_val_1994_;
goto v___jp_1980_;
}
else
{
size_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = lean_usize_of_nat(v___x_1995_);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1993_, v___x_1999_, v___x_2000_, v___x_1997_, v_a_1853_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_dec_ref(v___x_2001_);
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_val_1994_;
goto v___jp_1980_;
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_val_1994_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v_relPkgDir_1974_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1890_);
lean_dec(v_name_1889_);
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
size_t v___x_2010_; size_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = ((size_t)0ULL);
v___x_2011_ = lean_usize_of_nat(v___x_1995_);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1993_, v___x_2010_, v___x_2011_, v___x_1997_, v_a_1853_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref(v___x_2012_);
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_val_1994_;
goto v___jp_1980_;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_val_1994_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v_relPkgDir_1974_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1890_);
lean_dec(v_name_1889_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
v___jp_2021_:
{
if (lean_obj_tag(v_a_2022_) == 1)
{
lean_object* v_val_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec_ref(v_pkgDir_1977_);
lean_dec_ref(v_sname_1966_);
v_val_2023_ = lean_ctor_get(v_a_2022_, 0);
lean_inc_n(v_val_2023_, 2);
lean_dec_ref(v_a_2022_);
v___x_2024_ = l_Lake_defaultManifestFile;
v___x_2025_ = l_Lake_joinRelative(v_val_2023_, v___x_2024_);
v___x_2026_ = lean_unsigned_to_nat(0u);
v___x_2027_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2028_ = l_Lake_Manifest_load(v___x_2025_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 1);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
v___y_1991_ = v_val_2023_;
v___y_1992_ = v___x_2026_;
v___y_1993_ = v___x_2027_;
v_val_1994_ = v___x_2034_;
goto v___jp_1990_;
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
v_a_2037_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2028_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2028_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set_tag(v___x_2039_, 0);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
v___y_1991_ = v_val_2023_;
v___y_1992_ = v___x_2026_;
v___y_1993_ = v___x_2027_;
v_val_1994_ = v___x_2042_;
goto v___jp_1990_;
}
}
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec(v_a_2022_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v_relPkgDir_1974_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1890_);
lean_dec(v_name_1889_);
v___x_2045_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2046_ = lean_string_append(v_sname_1966_, v___x_2045_);
v___x_2047_ = lean_string_append(v___x_2046_, v_pkgDir_1977_);
lean_dec_ref(v_pkgDir_1977_);
v___x_2048_ = 3;
v___x_2049_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*1, v___x_2048_);
lean_inc_ref(v_a_1853_);
v___x_2050_ = lean_apply_2(v_a_1853_, v___x_2049_, lean_box(0));
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
v___jp_2055_:
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2057_ == 0)
{
v_a_2022_ = v_val_2056_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2059_ == 0)
{
if (v___x_2057_ == 0)
{
v_a_2022_ = v_val_2056_;
goto v___jp_2021_;
}
else
{
size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = ((size_t)0ULL);
v___x_2061_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2054_, v___x_2060_, v___x_2061_, v___x_2058_, v_a_1853_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_dec_ref(v___x_2062_);
v_a_2022_ = v_val_2056_;
goto v___jp_2021_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_val_2056_);
lean_dec_ref(v_pkgDir_1977_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v_relPkgDir_1974_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_sname_1966_);
lean_dec_ref(v_scope_1890_);
lean_dec(v_name_1889_);
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
else
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2054_, v___x_2071_, v___x_2072_, v___x_2058_, v_a_1853_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_dec_ref(v___x_2073_);
v_a_2022_ = v_val_2056_;
goto v___jp_2021_;
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_val_2056_);
lean_dec_ref(v_pkgDir_1977_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v_relPkgDir_1974_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_sname_1966_);
lean_dec_ref(v_scope_1890_);
lean_dec(v_name_1889_);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
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
lean_object* v_url_2096_; lean_object* v_rev_2097_; lean_object* v_subDir_2098_; lean_object* v___y_2100_; lean_object* v___x_2103_; 
lean_del_object(v___x_1963_);
lean_dec_ref(v_relParentDir_1852_);
v_url_2096_ = lean_ctor_get(v_val_1961_, 0);
lean_inc_ref_n(v_url_2096_, 2);
v_rev_2097_ = lean_ctor_get(v_val_1961_, 1);
lean_inc(v_rev_2097_);
v_subDir_2098_ = lean_ctor_get(v_val_1961_, 2);
lean_inc(v_subDir_2098_);
lean_dec_ref(v_val_1961_);
v___x_2103_ = l_Lake_Git_filterUrl_x3f(v_url_2096_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2100_ = v___x_2104_;
goto v___jp_2099_;
}
else
{
lean_object* v_val_2105_; 
v_val_2105_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_val_2105_);
lean_dec_ref(v___x_2103_);
v___y_2100_ = v_val_2105_;
goto v___jp_2099_;
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_inc_ref(v_sname_1966_);
v___x_2101_ = l_Lake_joinRelative(v_relPkgsDir_1851_, v_sname_1966_);
v___x_2102_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1853_, v_dep_1847_, v_inherited_1848_, v_lakeEnv_1849_, v_wsDir_1850_, v_sname_1966_, v___x_2101_, v_url_2096_, v___y_2100_, v_rev_2097_, v_subDir_2098_);
lean_dec_ref(v_lakeEnv_1849_);
return v___x_2102_;
}
}
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v_a_2148_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v_fst_2283_; lean_object* v_snd_2284_; uint8_t v___x_2311_; lean_object* v_a_2313_; 
lean_dec(v_src_x3f_1892_);
lean_dec_ref(v_relParentDir_1852_);
v___x_2107_ = lean_string_utf8_byte_size(v_scope_1890_);
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2311_ = lean_nat_dec_eq(v___x_2107_, v___x_2108_);
if (v___x_2311_ == 0)
{
if (lean_obj_tag(v_version_x3f_1891_) == 1)
{
lean_object* v_val_2323_; lean_object* v___x_2324_; 
v_val_2323_ = lean_ctor_get(v_version_x3f_1891_, 0);
lean_inc(v_val_2323_);
v___x_2324_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_2323_);
if (lean_obj_tag(v___x_2324_) == 1)
{
lean_object* v_val_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
v_val_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_val_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = l_String_Slice_toString(v_val_2325_);
lean_dec(v_val_2325_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
v_a_2313_ = v___x_2331_;
goto v___jp_2312_;
}
}
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v___x_2324_);
v___x_2334_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2335_ = lean_string_utf8_byte_size(v_val_2323_);
lean_inc(v_val_2323_);
v___x_2336_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_val_2323_, v___x_2334_, v___x_2108_, v___x_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2353_; 
lean_inc(v_name_1889_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2353_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2353_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2341_ = 1;
v___x_2342_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1889_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
v___x_2344_ = lean_string_append(v___x_2342_, v___x_2343_);
v___x_2345_ = lean_string_append(v___x_2344_, v_a_2337_);
lean_dec(v_a_2337_);
v___x_2346_ = 3;
v___x_2347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*1, v___x_2346_);
lean_inc_ref(v_a_1853_);
v___x_2348_ = lean_apply_2(v_a_1853_, v___x_2347_, lean_box(0));
v___x_2349_ = lean_box(0);
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 1);
lean_ctor_set(v___x_2339_, 0, v___x_2349_);
v___x_2351_ = v___x_2339_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2336_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2336_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 2);
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
v_a_2313_ = v___x_2359_;
goto v___jp_2312_;
}
}
}
}
}
else
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_box(0);
v_a_2313_ = v___x_2362_;
goto v___jp_2312_;
}
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_inc(v_name_1889_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___x_2363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1889_, v___x_2311_);
v___x_2364_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
v___x_2365_ = lean_string_append(v___x_2363_, v___x_2364_);
v___x_2366_ = 3;
v___x_2367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2366_);
lean_inc_ref(v_a_1853_);
v___x_2368_ = lean_apply_2(v_a_1853_, v___x_2367_, lean_box(0));
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
v___jp_2109_:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = lean_array_get_size(v_snd_2118_);
v___x_2120_ = lean_nat_dec_lt(v___x_2108_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_dec_ref(v_snd_2118_);
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2113_;
v___y_1914_ = v___y_2112_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2116_;
v___y_1917_ = v___y_2115_;
v_a_1918_ = v_fst_2117_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_nat_dec_le(v___x_2119_, v___x_2119_);
if (v___x_2122_ == 0)
{
if (v___x_2120_ == 0)
{
lean_dec_ref(v_snd_2118_);
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2113_;
v___y_1914_ = v___y_2112_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2116_;
v___y_1917_ = v___y_2115_;
v_a_1918_ = v_fst_2117_;
goto v___jp_1910_;
}
else
{
size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = lean_usize_of_nat(v___x_2119_);
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2118_, v___x_2123_, v___x_2124_, v___x_2121_, v_a_1853_);
lean_dec_ref(v_snd_2118_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_dec_ref(v___x_2125_);
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2113_;
v___y_1914_ = v___y_2112_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2116_;
v___y_1917_ = v___y_2115_;
v_a_1918_ = v_fst_2117_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_fst_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
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
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = lean_usize_of_nat(v___x_2119_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2118_, v___x_2134_, v___x_2135_, v___x_2121_, v_a_1853_);
lean_dec_ref(v_snd_2118_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_dec_ref(v___x_2136_);
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2113_;
v___y_1914_ = v___y_2112_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2116_;
v___y_1917_ = v___y_2115_;
v_a_1918_ = v_fst_2117_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_fst_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
v___jp_2145_:
{
if (lean_obj_tag(v_a_2148_) == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_inc_ref(v_scope_1890_);
lean_dec_ref(v_a_2148_);
lean_dec(v___y_2146_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___x_2149_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2150_ = lean_string_append(v_scope_1890_, v___x_2149_);
v___x_2151_ = lean_string_append(v___x_2150_, v___y_2147_);
lean_dec_ref(v___y_2147_);
v___x_2152_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
v___x_2154_ = 3;
v___x_2155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*1, v___x_2154_);
lean_inc_ref(v_a_1853_);
v___x_2156_ = lean_apply_2(v_a_1853_, v___x_2155_, lean_box(0));
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2279_; 
v_a_2159_ = lean_ctor_get(v_a_2148_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_a_2148_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2161_ = v_a_2148_;
v_isShared_2162_ = v_isSharedCheck_2279_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v_a_2148_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2279_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
if (lean_obj_tag(v_a_2159_) == 0)
{
lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_inc_ref(v_scope_1890_);
lean_del_object(v___x_2161_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___x_2163_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1890_, v___y_2147_, v___y_2146_);
lean_dec_ref(v___y_2147_);
v___x_2164_ = 3;
v___x_2165_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set_uint8(v___x_2165_, sizeof(void*)*1, v___x_2164_);
lean_inc_ref(v_a_1853_);
v___x_2166_ = lean_apply_2(v_a_1853_, v___x_2165_, lean_box(0));
v___x_2167_ = lean_box(0);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
else
{
lean_object* v_val_2169_; lean_object* v___x_2170_; 
v_val_2169_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_val_2169_);
lean_dec_ref(v_a_2159_);
v___x_2170_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2169_);
if (lean_obj_tag(v___x_2170_) == 1)
{
lean_object* v_val_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2278_; 
v_val_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2278_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_val_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2278_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
if (lean_obj_tag(v_val_2171_) == 0)
{
lean_object* v_url_2175_; lean_object* v_githubUrl_x3f_2176_; lean_object* v_defaultBranch_x3f_2177_; lean_object* v_subDir_x3f_2178_; lean_object* v_name_2179_; lean_object* v_fullName_2180_; lean_object* v___x_2181_; 
v_url_2175_ = lean_ctor_get(v_val_2171_, 1);
lean_inc_ref(v_url_2175_);
v_githubUrl_x3f_2176_ = lean_ctor_get(v_val_2171_, 2);
lean_inc(v_githubUrl_x3f_2176_);
v_defaultBranch_x3f_2177_ = lean_ctor_get(v_val_2171_, 3);
lean_inc(v_defaultBranch_x3f_2177_);
v_subDir_x3f_2178_ = lean_ctor_get(v_val_2171_, 4);
lean_inc(v_subDir_x3f_2178_);
lean_dec_ref(v_val_2171_);
v_name_2179_ = lean_ctor_get(v_val_2169_, 0);
lean_inc_ref(v_name_2179_);
v_fullName_2180_ = lean_ctor_get(v_val_2169_, 1);
lean_inc_ref(v_fullName_2180_);
lean_dec(v_val_2169_);
v___x_2181_ = l_Lake_joinRelative(v_relPkgsDir_1851_, v_name_2179_);
switch(lean_obj_tag(v___y_2146_))
{
case 0:
{
lean_object* v___x_2182_; 
lean_del_object(v___x_2161_);
lean_dec_ref(v___y_2147_);
v___x_2182_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v_defaultBranch_x3f_2177_) == 0)
{
uint8_t v___x_2183_; 
lean_dec_ref(v___x_2181_);
lean_dec_ref(v_fullName_2180_);
lean_dec(v_subDir_x3f_2178_);
lean_dec(v_githubUrl_x3f_2176_);
lean_dec_ref(v_url_2175_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___x_2183_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = lean_box(0);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2184_);
v___x_2186_ = v___x_2173_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
lean_del_object(v___x_2173_);
v___x_2188_ = lean_box(0);
v___x_2189_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2189_ == 0)
{
if (v___x_2183_ == 0)
{
goto v___jp_1855_;
}
else
{
size_t v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2182_, v___x_2190_, v___x_2191_, v___x_2188_, v_a_1853_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_dec_ref(v___x_2192_);
goto v___jp_1855_;
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
else
{
size_t v___x_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2182_, v___x_2201_, v___x_2202_, v___x_2188_, v_a_1853_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_dec_ref(v___x_2203_);
goto v___jp_1855_;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
else
{
lean_object* v_val_2212_; uint8_t v___x_2213_; 
lean_del_object(v___x_2173_);
v_val_2212_ = lean_ctor_get(v_defaultBranch_x3f_2177_, 0);
lean_inc(v_val_2212_);
lean_dec_ref(v_defaultBranch_x3f_2177_);
v___x_2213_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2213_ == 0)
{
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_val_2212_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2215_ == 0)
{
if (v___x_2213_ == 0)
{
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_val_2212_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
size_t v___x_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2182_, v___x_2216_, v___x_2217_, v___x_2214_, v_a_1853_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_dec_ref(v___x_2218_);
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_val_2212_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_val_2212_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v_fullName_2180_);
lean_dec(v_subDir_x3f_2178_);
lean_dec(v_githubUrl_x3f_2176_);
lean_dec_ref(v_url_2175_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
else
{
size_t v___x_2227_; size_t v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = ((size_t)0ULL);
v___x_2228_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2182_, v___x_2227_, v___x_2228_, v___x_2214_, v_a_1853_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_dec_ref(v___x_2229_);
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_val_2212_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_val_2212_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v_fullName_2180_);
lean_dec(v_subDir_x3f_2178_);
lean_dec(v_githubUrl_x3f_2176_);
lean_dec_ref(v_url_2175_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
lean_dec(v_defaultBranch_x3f_2177_);
lean_del_object(v___x_2173_);
lean_del_object(v___x_2161_);
lean_dec_ref(v___y_2147_);
v_rev_2238_ = lean_ctor_get(v___y_2146_, 0);
lean_inc_ref(v_rev_2238_);
lean_dec_ref(v___y_2146_);
v___x_2239_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2240_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2240_ == 0)
{
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_rev_2238_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2242_ == 0)
{
if (v___x_2240_ == 0)
{
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_rev_2238_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
size_t v___x_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2239_, v___x_2243_, v___x_2244_, v___x_2241_, v_a_1853_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_dec_ref(v___x_2245_);
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_rev_2238_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v_rev_2238_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v_fullName_2180_);
lean_dec(v_subDir_x3f_2178_);
lean_dec(v_githubUrl_x3f_2176_);
lean_dec_ref(v_url_2175_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = ((size_t)0ULL);
v___x_2255_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2239_, v___x_2254_, v___x_2255_, v___x_2241_, v_a_1853_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_dec_ref(v___x_2256_);
v___y_1880_ = v_subDir_x3f_2178_;
v___y_1881_ = v_fullName_2180_;
v___y_1882_ = v___x_2181_;
v___y_1883_ = v_githubUrl_x3f_2176_;
v___y_1884_ = v_url_2175_;
v_rev_x3f_1885_ = v_rev_2238_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_rev_2238_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v_fullName_2180_);
lean_dec(v_subDir_x3f_2178_);
lean_dec(v_githubUrl_x3f_2176_);
lean_dec_ref(v_url_2175_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
default: 
{
lean_object* v_ver_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec(v_defaultBranch_x3f_2177_);
lean_del_object(v___x_2173_);
v_ver_2265_ = lean_ctor_get(v___y_2146_, 0);
lean_inc_ref(v_ver_2265_);
lean_dec_ref(v___y_2146_);
v___x_2266_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___y_2147_);
lean_inc_ref(v_scope_1890_);
lean_inc_ref(v_lakeEnv_1849_);
v___x_2267_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1849_, v_scope_1890_, v___y_2147_, v___x_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v___x_2271_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
v_a_2269_ = lean_ctor_get(v___x_2267_, 1);
lean_inc(v_a_2269_);
lean_dec_ref(v___x_2267_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v_a_2268_);
v___x_2271_ = v___x_2161_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2268_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
v___y_2110_ = v_ver_2265_;
v___y_2111_ = v_subDir_x3f_2178_;
v___y_2112_ = v_fullName_2180_;
v___y_2113_ = v___x_2181_;
v___y_2114_ = v___y_2147_;
v___y_2115_ = v_githubUrl_x3f_2176_;
v___y_2116_ = v_url_2175_;
v_fst_2117_ = v___x_2271_;
v_snd_2118_ = v_a_2269_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2273_; lean_object* v_a_2274_; lean_object* v___x_2276_; 
v_a_2273_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2273_);
v_a_2274_ = lean_ctor_get(v___x_2267_, 1);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2267_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set_tag(v___x_2161_, 0);
lean_ctor_set(v___x_2161_, 0, v_a_2273_);
v___x_2276_ = v___x_2161_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2273_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
v___y_2110_ = v_ver_2265_;
v___y_2111_ = v_subDir_x3f_2178_;
v___y_2112_ = v_fullName_2180_;
v___y_2113_ = v___x_2181_;
v___y_2114_ = v___y_2147_;
v___y_2115_ = v_githubUrl_x3f_2176_;
v___y_2116_ = v_url_2175_;
v_fst_2117_ = v___x_2276_;
v_snd_2118_ = v_a_2274_;
goto v___jp_2109_;
}
}
}
}
}
else
{
lean_del_object(v___x_2173_);
lean_dec(v_val_2171_);
lean_del_object(v___x_2161_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___y_1859_ = v_val_2169_;
v___y_1860_ = v_a_1853_;
goto v___jp_1858_;
}
}
}
else
{
lean_dec(v___x_2170_);
lean_del_object(v___x_2161_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___y_1859_ = v_val_2169_;
v___y_1860_ = v_a_1853_;
goto v___jp_1858_;
}
}
}
}
}
v___jp_2280_:
{
lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = lean_array_get_size(v_snd_2284_);
v___x_2286_ = lean_nat_dec_lt(v___x_2108_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_dec_ref(v_snd_2284_);
v___y_2146_ = v___y_2281_;
v___y_2147_ = v___y_2282_;
v_a_2148_ = v_fst_2283_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_nat_dec_le(v___x_2285_, v___x_2285_);
if (v___x_2288_ == 0)
{
if (v___x_2286_ == 0)
{
lean_dec_ref(v_snd_2284_);
v___y_2146_ = v___y_2281_;
v___y_2147_ = v___y_2282_;
v_a_2148_ = v_fst_2283_;
goto v___jp_2145_;
}
else
{
size_t v___x_2289_; size_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = ((size_t)0ULL);
v___x_2290_ = lean_usize_of_nat(v___x_2285_);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2284_, v___x_2289_, v___x_2290_, v___x_2287_, v_a_1853_);
lean_dec_ref(v_snd_2284_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_dec_ref(v___x_2291_);
v___y_2146_ = v___y_2281_;
v___y_2147_ = v___y_2282_;
v_a_2148_ = v_fst_2283_;
goto v___jp_2145_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_fst_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
else
{
size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2285_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2284_, v___x_2300_, v___x_2301_, v___x_2287_, v_a_1853_);
lean_dec_ref(v_snd_2284_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_dec_ref(v___x_2302_);
v___y_2146_ = v___y_2281_;
v___y_2147_ = v___y_2282_;
v_a_2148_ = v_fst_2283_;
goto v___jp_2145_;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_fst_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v_relPkgsDir_1851_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
v___jp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_inc(v_name_1889_);
v___x_2314_ = l_Lean_Name_toString(v_name_1889_, v___x_2311_);
v___x_2315_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___x_2314_);
lean_inc_ref(v_scope_1890_);
lean_inc_ref(v_lakeEnv_1849_);
v___x_2316_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1849_, v_scope_1890_, v___x_2314_, v___x_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
v_a_2318_ = lean_ctor_get(v___x_2316_, 1);
lean_inc(v_a_2318_);
lean_dec_ref(v___x_2316_);
v___x_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2319_, 0, v_a_2317_);
v___y_2281_ = v_a_2313_;
v___y_2282_ = v___x_2314_;
v_fst_2283_ = v___x_2319_;
v_snd_2284_ = v_a_2318_;
goto v___jp_2280_;
}
else
{
lean_object* v_a_2320_; lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2320_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2320_);
v_a_2321_ = lean_ctor_get(v___x_2316_, 1);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2316_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_a_2320_);
v___y_2281_ = v_a_2313_;
v___y_2282_ = v___x_2314_;
v_fst_2283_ = v___x_2322_;
v_snd_2284_ = v_a_2321_;
goto v___jp_2280_;
}
}
}
v___jp_1855_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
v___jp_1858_:
{
lean_object* v_fullName_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_fullName_1861_ = lean_ctor_get(v___y_1859_, 1);
lean_inc_ref(v_fullName_1861_);
lean_dec_ref(v___y_1859_);
v___x_1862_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1863_ = lean_string_append(v_fullName_1861_, v___x_1862_);
v___x_1864_ = 3;
v___x_1865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*1, v___x_1864_);
lean_inc_ref(v___y_1860_);
v___x_1866_ = lean_apply_2(v___y_1860_, v___x_1865_, lean_box(0));
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
v___jp_1869_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___y_1870_);
v___x_1878_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1847_, v_inherited_1848_, v_lakeEnv_1849_, v_wsDir_1850_, v___y_1873_, v___y_1872_, v___y_1875_, v___y_1876_, v___x_1877_, v___y_1871_, v___y_1874_);
lean_dec_ref(v_lakeEnv_1849_);
return v___x_1878_;
}
v___jp_1879_:
{
if (lean_obj_tag(v___y_1883_) == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1870_ = v_rev_x3f_1885_;
v___y_1871_ = v___y_1880_;
v___y_1872_ = v___y_1882_;
v___y_1873_ = v___y_1881_;
v___y_1874_ = v___y_1886_;
v___y_1875_ = v___y_1884_;
v___y_1876_ = v___x_1887_;
goto v___jp_1869_;
}
else
{
lean_object* v_val_1888_; 
v_val_1888_ = lean_ctor_get(v___y_1883_, 0);
lean_inc(v_val_1888_);
lean_dec_ref(v___y_1883_);
v___y_1870_ = v_rev_x3f_1885_;
v___y_1871_ = v___y_1880_;
v___y_1872_ = v___y_1882_;
v___y_1873_ = v___y_1881_;
v___y_1874_ = v___y_1886_;
v___y_1875_ = v___y_1884_;
v___y_1876_ = v_val_1888_;
goto v___jp_1869_;
}
}
v___jp_1893_:
{
lean_object* v_toString_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_toString_1896_ = lean_ctor_get(v___y_1894_, 0);
lean_inc_ref(v_toString_1896_);
lean_dec_ref(v___y_1894_);
v___x_1897_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1898_ = lean_string_append(v_scope_1890_, v___x_1897_);
v___x_1899_ = lean_string_append(v___x_1898_, v___y_1895_);
lean_dec_ref(v___y_1895_);
v___x_1900_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1901_ = lean_string_append(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_string_append(v___x_1901_, v_toString_1896_);
lean_dec_ref(v_toString_1896_);
v___x_1903_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1904_ = lean_string_append(v___x_1902_, v___x_1903_);
v___x_1905_ = 3;
v___x_1906_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*1, v___x_1905_);
lean_inc_ref(v_a_1853_);
v___x_1907_ = lean_apply_2(v_a_1853_, v___x_1906_, lean_box(0));
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
v___jp_1910_:
{
if (lean_obj_tag(v_a_1918_) == 0)
{
lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1934_; 
lean_inc_ref(v_scope_1890_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_a_1918_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v_a_1918_, 0);
lean_dec(v_unused_1935_);
v___x_1920_ = v_a_1918_;
v_isShared_1921_ = v_isSharedCheck_1934_;
goto v_resetjp_1919_;
}
else
{
lean_dec(v_a_1918_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1934_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1922_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1923_ = lean_string_append(v_scope_1890_, v___x_1922_);
v___x_1924_ = lean_string_append(v___x_1923_, v___y_1915_);
lean_dec_ref(v___y_1915_);
v___x_1925_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_1926_ = lean_string_append(v___x_1924_, v___x_1925_);
v___x_1927_ = 3;
v___x_1928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*1, v___x_1927_);
lean_inc_ref(v_a_1853_);
v___x_1929_ = lean_apply_2(v_a_1853_, v___x_1928_, lean_box(0));
v___x_1930_ = lean_box(0);
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 1);
lean_ctor_set(v___x_1920_, 0, v___x_1930_);
v___x_1932_ = v___x_1920_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1937_; size_t v_sz_1938_; size_t v___x_1939_; lean_object* v___x_1940_; lean_object* v_fst_1941_; 
v_a_1936_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v_a_1918_);
v___x_1937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_1938_ = lean_array_size(v_a_1936_);
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1911_, v_a_1936_, v_sz_1938_, v___x_1939_, v___x_1937_);
lean_dec(v_a_1936_);
v_fst_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_fst_1941_);
lean_dec_ref(v___x_1940_);
if (lean_obj_tag(v_fst_1941_) == 0)
{
lean_inc_ref(v_scope_1890_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___y_1894_ = v___y_1911_;
v___y_1895_ = v___y_1915_;
goto v___jp_1893_;
}
else
{
lean_object* v_val_1942_; 
v_val_1942_ = lean_ctor_get(v_fst_1941_, 0);
lean_inc(v_val_1942_);
lean_dec_ref(v_fst_1941_);
if (lean_obj_tag(v_val_1942_) == 1)
{
lean_object* v_val_1943_; lean_object* v_version_1944_; lean_object* v_revision_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec_ref(v___y_1911_);
v_val_1943_ = lean_ctor_get(v_val_1942_, 0);
lean_inc(v_val_1943_);
lean_dec_ref(v_val_1942_);
v_version_1944_ = lean_ctor_get(v_val_1943_, 0);
lean_inc_ref(v_version_1944_);
v_revision_1945_ = lean_ctor_get(v_val_1943_, 1);
lean_inc_ref(v_revision_1945_);
lean_dec(v_val_1943_);
v___x_1946_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1890_);
v___x_1947_ = lean_string_append(v_scope_1890_, v___x_1946_);
v___x_1948_ = lean_string_append(v___x_1947_, v___y_1915_);
lean_dec_ref(v___y_1915_);
v___x_1949_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_1950_ = lean_string_append(v___x_1948_, v___x_1949_);
v___x_1951_ = l_Lake_StdVer_toString(v_version_1944_);
v___x_1952_ = lean_string_append(v___x_1950_, v___x_1951_);
lean_dec_ref(v___x_1951_);
v___x_1953_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_1954_ = lean_string_append(v___x_1952_, v___x_1953_);
v___x_1955_ = lean_string_append(v___x_1954_, v_revision_1945_);
v___x_1956_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_1957_ = lean_string_append(v___x_1955_, v___x_1956_);
v___x_1958_ = 1;
v___x_1959_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*1, v___x_1958_);
lean_inc_ref(v_a_1853_);
v___x_1960_ = lean_apply_2(v_a_1853_, v___x_1959_, lean_box(0));
v___y_1880_ = v___y_1912_;
v___y_1881_ = v___y_1914_;
v___y_1882_ = v___y_1913_;
v___y_1883_ = v___y_1917_;
v___y_1884_ = v___y_1916_;
v_rev_x3f_1885_ = v_revision_1945_;
v___y_1886_ = v_a_1853_;
goto v___jp_1879_;
}
else
{
lean_inc_ref(v_scope_1890_);
lean_dec(v_val_1942_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v_wsDir_1850_);
lean_dec_ref(v_lakeEnv_1849_);
lean_dec_ref(v_dep_1847_);
v___y_1894_ = v___y_1911_;
v___y_1895_ = v___y_1915_;
goto v___jp_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2371_, lean_object* v_inherited_2372_, lean_object* v_lakeEnv_2373_, lean_object* v_wsDir_2374_, lean_object* v_relPkgsDir_2375_, lean_object* v_relParentDir_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
uint8_t v_inherited_boxed_2379_; lean_object* v_res_2380_; 
v_inherited_boxed_2379_ = lean_unbox(v_inherited_2372_);
v_res_2380_ = l_Lake_Dependency_materialize(v_dep_2371_, v_inherited_boxed_2379_, v_lakeEnv_2373_, v_wsDir_2374_, v_relPkgsDir_2375_, v_relParentDir_2376_, v_a_2377_);
lean_dec_ref(v_a_2377_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2386_, lean_object* v_wsDir_2387_, lean_object* v_relPkgDir_2388_, lean_object* v_remoteUrl_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v___y_2393_; lean_object* v_a_2394_; lean_object* v_pkgDir_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v_val_2406_; lean_object* v_a_2436_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_val_2476_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
lean_inc_ref(v_relPkgDir_2388_);
v_pkgDir_2397_ = l_Lake_joinRelative(v_wsDir_2387_, v_relPkgDir_2388_);
v___x_2398_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_2397_);
v___x_2399_ = l_Lake_resolvePath(v_pkgDir_2397_);
v___f_2400_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2504_ = lean_string_utf8_byte_size(v___x_2399_);
v___x_2505_ = lean_nat_dec_eq(v___x_2504_, v___x_2473_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2399_);
v_val_2476_ = v___x_2506_;
goto v___jp_2475_;
}
else
{
lean_object* v___x_2507_; 
lean_dec_ref(v___x_2399_);
v___x_2507_ = lean_box(0);
v_val_2476_ = v___x_2507_;
goto v___jp_2475_;
}
v___jp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2395_, 0, v___y_2393_);
lean_ctor_set(v___x_2395_, 1, v_relPkgDir_2388_);
lean_ctor_set(v___x_2395_, 2, v_remoteUrl_2389_);
lean_ctor_set(v___x_2395_, 3, v_a_2394_);
lean_ctor_set(v___x_2395_, 4, v_manifestEntry_2386_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
v___jp_2401_:
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = lean_array_get_size(v___y_2402_);
v___x_2408_ = lean_nat_dec_lt(v___y_2403_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v___y_2405_);
v___y_2393_ = v___y_2404_;
v_a_2394_ = v_val_2406_;
goto v___jp_2392_;
}
else
{
lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_nat_dec_le(v___x_2407_, v___x_2407_);
if (v___x_2410_ == 0)
{
if (v___x_2408_ == 0)
{
lean_dec_ref(v___y_2405_);
v___y_2393_ = v___y_2404_;
v_a_2394_ = v_val_2406_;
goto v___jp_2392_;
}
else
{
size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2400__overap_2413_; lean_object* v___x_2414_; 
v___x_2411_ = ((size_t)0ULL);
v___x_2412_ = lean_usize_of_nat(v___x_2407_);
lean_inc_ref(v___y_2402_);
v___x_2400__overap_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2405_, v___f_2400_, v___y_2402_, v___x_2411_, v___x_2412_, v___x_2409_);
lean_inc_ref(v_a_2390_);
v___x_2414_ = lean_apply_2(v___x_2400__overap_2413_, v_a_2390_, lean_box(0));
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_dec_ref(v___x_2414_);
v___y_2393_ = v___y_2404_;
v_a_2394_ = v_val_2406_;
goto v___jp_2392_;
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec_ref(v_val_2406_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_remoteUrl_2389_);
lean_dec_ref(v_relPkgDir_2388_);
lean_dec_ref(v_manifestEntry_2386_);
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
else
{
size_t v___x_2423_; size_t v___x_2424_; lean_object* v___x_2410__overap_2425_; lean_object* v___x_2426_; 
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = lean_usize_of_nat(v___x_2407_);
lean_inc_ref(v___y_2402_);
v___x_2410__overap_2425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2405_, v___f_2400_, v___y_2402_, v___x_2423_, v___x_2424_, v___x_2409_);
lean_inc_ref(v_a_2390_);
v___x_2426_ = lean_apply_2(v___x_2410__overap_2425_, v_a_2390_, lean_box(0));
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_dec_ref(v___x_2426_);
v___y_2393_ = v___y_2404_;
v_a_2394_ = v_val_2406_;
goto v___jp_2392_;
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec_ref(v_val_2406_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_remoteUrl_2389_);
lean_dec_ref(v_relPkgDir_2388_);
lean_dec_ref(v_manifestEntry_2386_);
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
}
v___jp_2435_:
{
if (lean_obj_tag(v_a_2436_) == 1)
{
lean_object* v_manifestFile_x3f_2437_; 
lean_dec_ref(v_pkgDir_2397_);
v_manifestFile_x3f_2437_ = lean_ctor_get(v_manifestEntry_2386_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2437_) == 1)
{
lean_object* v_val_2438_; lean_object* v_val_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_val_2438_ = lean_ctor_get(v_a_2436_, 0);
lean_inc_n(v_val_2438_, 2);
lean_dec_ref(v_a_2436_);
v_val_2439_ = lean_ctor_get(v_manifestFile_x3f_2437_, 0);
lean_inc(v_val_2439_);
v___x_2440_ = l_Lake_joinRelative(v_val_2438_, v_val_2439_);
v___x_2441_ = lean_unsigned_to_nat(0u);
v___x_2442_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2443_ = l_Lake_Manifest_load(v___x_2440_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 1);
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
v___y_2402_ = v___x_2442_;
v___y_2403_ = v___x_2441_;
v___y_2404_ = v_val_2438_;
v___y_2405_ = v___x_2398_;
v_val_2406_ = v___x_2449_;
goto v___jp_2401_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2443_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2443_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set_tag(v___x_2454_, 0);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
v___y_2402_ = v___x_2442_;
v___y_2403_ = v___x_2441_;
v___y_2404_ = v_val_2438_;
v___y_2405_ = v___x_2398_;
v_val_2406_ = v___x_2457_;
goto v___jp_2401_;
}
}
}
}
else
{
lean_object* v_val_2460_; lean_object* v___x_2461_; 
v_val_2460_ = lean_ctor_get(v_a_2436_, 0);
lean_inc(v_val_2460_);
lean_dec_ref(v_a_2436_);
v___x_2461_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2393_ = v_val_2460_;
v_a_2394_ = v___x_2461_;
goto v___jp_2392_;
}
}
else
{
lean_object* v_name_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_remoteUrl_2389_);
lean_dec_ref(v_relPkgDir_2388_);
v_name_2462_ = lean_ctor_get(v_manifestEntry_2386_, 0);
lean_inc(v_name_2462_);
lean_dec_ref(v_manifestEntry_2386_);
v___x_2463_ = 0;
v___x_2464_ = l_Lean_Name_toString(v_name_2462_, v___x_2463_);
v___x_2465_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
v___x_2467_ = lean_string_append(v___x_2466_, v_pkgDir_2397_);
lean_dec_ref(v_pkgDir_2397_);
v___x_2468_ = 3;
v___x_2469_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*1, v___x_2468_);
lean_inc_ref(v_a_2390_);
v___x_2470_ = lean_apply_2(v_a_2390_, v___x_2469_, lean_box(0));
v___x_2471_ = lean_box(0);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
v___jp_2475_:
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2477_ == 0)
{
v_a_2436_ = v_val_2476_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2479_ == 0)
{
if (v___x_2477_ == 0)
{
v_a_2436_ = v_val_2476_;
goto v___jp_2435_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2466__overap_2482_; lean_object* v___x_2483_; 
v___x_2480_ = ((size_t)0ULL);
v___x_2481_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2466__overap_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2398_, v___f_2400_, v___x_2474_, v___x_2480_, v___x_2481_, v___x_2478_);
lean_inc_ref(v_a_2390_);
v___x_2483_ = lean_apply_2(v___x_2466__overap_2482_, v_a_2390_, lean_box(0));
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_dec_ref(v___x_2483_);
v_a_2436_ = v_val_2476_;
goto v___jp_2435_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_val_2476_);
lean_dec_ref(v_pkgDir_2397_);
lean_dec_ref(v_remoteUrl_2389_);
lean_dec_ref(v_relPkgDir_2388_);
lean_dec_ref(v_manifestEntry_2386_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
else
{
size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2476__overap_2494_; lean_object* v___x_2495_; 
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2476__overap_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2398_, v___f_2400_, v___x_2474_, v___x_2492_, v___x_2493_, v___x_2478_);
lean_inc_ref(v_a_2390_);
v___x_2495_ = lean_apply_2(v___x_2476__overap_2494_, v_a_2390_, lean_box(0));
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_dec_ref(v___x_2495_);
v_a_2436_ = v_val_2476_;
goto v___jp_2435_;
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_val_2476_);
lean_dec_ref(v_pkgDir_2397_);
lean_dec_ref(v_remoteUrl_2389_);
lean_dec_ref(v_relPkgDir_2388_);
lean_dec_ref(v_manifestEntry_2386_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2508_, lean_object* v_wsDir_2509_, lean_object* v_relPkgDir_2510_, lean_object* v_remoteUrl_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2508_, v_wsDir_2509_, v_relPkgDir_2510_, v_remoteUrl_2511_, v_a_2512_);
lean_dec_ref(v_a_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2516_, lean_object* v_lakeEnv_2517_, lean_object* v_wsDir_2518_, lean_object* v_relPkgsDir_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v_a_2526_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v_val_2536_; lean_object* v_src_2563_; 
v_src_2563_ = lean_ctor_get(v_manifestEntry_2516_, 4);
lean_inc_ref(v_src_2563_);
if (lean_obj_tag(v_src_2563_) == 0)
{
lean_object* v_name_2564_; lean_object* v_manifestFile_x3f_2565_; lean_object* v_dir_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v_relPkgsDir_2519_);
v_name_2564_ = lean_ctor_get(v_manifestEntry_2516_, 0);
v_manifestFile_x3f_2565_ = lean_ctor_get(v_manifestEntry_2516_, 3);
v_dir_2566_ = lean_ctor_get(v_src_2563_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_src_2563_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2568_ = v_src_2563_;
v_isShared_2569_ = v_isSharedCheck_2680_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_dir_2566_);
lean_dec(v_src_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2680_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_pkgDir_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___y_2574_; lean_object* v_a_2575_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v_val_2584_; lean_object* v_a_2612_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v_val_2650_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
lean_inc_ref(v_dir_2566_);
v_pkgDir_2570_ = l_Lake_joinRelative(v_wsDir_2518_, v_dir_2566_);
lean_inc_ref(v_pkgDir_2570_);
v___x_2571_ = l_Lake_resolvePath(v_pkgDir_2570_);
v___x_2572_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2676_ = lean_string_utf8_byte_size(v___x_2571_);
v___x_2677_ = lean_nat_dec_eq(v___x_2676_, v___x_2647_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2571_);
v_val_2650_ = v___x_2678_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2679_; 
lean_dec_ref(v___x_2571_);
v___x_2679_ = lean_box(0);
v_val_2650_ = v___x_2679_;
goto v___jp_2649_;
}
v___jp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2576_, 0, v___y_2574_);
lean_ctor_set(v___x_2576_, 1, v_dir_2566_);
lean_ctor_set(v___x_2576_, 2, v___x_2572_);
lean_ctor_set(v___x_2576_, 3, v_a_2575_);
lean_ctor_set(v___x_2576_, 4, v_manifestEntry_2516_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2576_);
v___x_2578_ = v___x_2568_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
v___jp_2580_:
{
lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2585_ = lean_array_get_size(v___y_2582_);
v___x_2586_ = lean_nat_dec_lt(v___y_2583_, v___x_2585_);
if (v___x_2586_ == 0)
{
v___y_2574_ = v___y_2581_;
v_a_2575_ = v_val_2584_;
goto v___jp_2573_;
}
else
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_nat_dec_le(v___x_2585_, v___x_2585_);
if (v___x_2588_ == 0)
{
if (v___x_2586_ == 0)
{
v___y_2574_ = v___y_2581_;
v_a_2575_ = v_val_2584_;
goto v___jp_2573_;
}
else
{
size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = lean_usize_of_nat(v___x_2585_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2582_, v___x_2589_, v___x_2590_, v___x_2587_, v_a_2520_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref(v___x_2591_);
v___y_2574_ = v___y_2581_;
v_a_2575_ = v_val_2584_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_val_2584_);
lean_dec_ref(v___y_2581_);
lean_del_object(v___x_2568_);
lean_dec_ref(v_dir_2566_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
else
{
size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = ((size_t)0ULL);
v___x_2601_ = lean_usize_of_nat(v___x_2585_);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2582_, v___x_2600_, v___x_2601_, v___x_2587_, v_a_2520_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_dec_ref(v___x_2602_);
v___y_2574_ = v___y_2581_;
v_a_2575_ = v_val_2584_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_val_2584_);
lean_dec_ref(v___y_2581_);
lean_del_object(v___x_2568_);
lean_dec_ref(v_dir_2566_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
v___jp_2611_:
{
if (lean_obj_tag(v_a_2612_) == 1)
{
lean_dec_ref(v_pkgDir_2570_);
if (lean_obj_tag(v_manifestFile_x3f_2565_) == 1)
{
lean_object* v_val_2613_; lean_object* v_val_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_val_2613_ = lean_ctor_get(v_a_2612_, 0);
lean_inc_n(v_val_2613_, 2);
lean_dec_ref(v_a_2612_);
v_val_2614_ = lean_ctor_get(v_manifestFile_x3f_2565_, 0);
lean_inc(v_val_2614_);
v___x_2615_ = l_Lake_joinRelative(v_val_2613_, v_val_2614_);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2618_ = l_Lake_Manifest_load(v___x_2615_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 1);
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
v___y_2581_ = v_val_2613_;
v___y_2582_ = v___x_2617_;
v___y_2583_ = v___x_2616_;
v_val_2584_ = v___x_2624_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
v_a_2627_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2618_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2618_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 0);
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
v___y_2581_ = v_val_2613_;
v___y_2582_ = v___x_2617_;
v___y_2583_ = v___x_2616_;
v_val_2584_ = v___x_2632_;
goto v___jp_2580_;
}
}
}
}
else
{
lean_object* v_val_2635_; lean_object* v___x_2636_; 
v_val_2635_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_val_2635_);
lean_dec_ref(v_a_2612_);
v___x_2636_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2574_ = v_val_2635_;
v_a_2575_ = v___x_2636_;
goto v___jp_2573_;
}
}
else
{
uint8_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_inc(v_name_2564_);
lean_dec(v_a_2612_);
lean_del_object(v___x_2568_);
lean_dec_ref(v_dir_2566_);
lean_dec_ref(v_manifestEntry_2516_);
v___x_2637_ = 0;
v___x_2638_ = l_Lean_Name_toString(v_name_2564_, v___x_2637_);
v___x_2639_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2640_ = lean_string_append(v___x_2638_, v___x_2639_);
v___x_2641_ = lean_string_append(v___x_2640_, v_pkgDir_2570_);
lean_dec_ref(v_pkgDir_2570_);
v___x_2642_ = 3;
v___x_2643_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*1, v___x_2642_);
lean_inc_ref(v_a_2520_);
v___x_2644_ = lean_apply_2(v_a_2520_, v___x_2643_, lean_box(0));
v___x_2645_ = lean_box(0);
v___x_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
}
v___jp_2649_:
{
uint8_t v___x_2651_; 
v___x_2651_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2651_ == 0)
{
v_a_2612_ = v_val_2650_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = lean_box(0);
v___x_2653_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2653_ == 0)
{
if (v___x_2651_ == 0)
{
v_a_2612_ = v_val_2650_;
goto v___jp_2611_;
}
else
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2648_, v___x_2654_, v___x_2655_, v___x_2652_, v_a_2520_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_dec_ref(v___x_2656_);
v_a_2612_ = v_val_2650_;
goto v___jp_2611_;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_val_2650_);
lean_dec_ref(v_pkgDir_2570_);
lean_del_object(v___x_2568_);
lean_dec_ref(v_dir_2566_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
else
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2648_, v___x_2665_, v___x_2666_, v___x_2652_, v_a_2520_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_dec_ref(v___x_2667_);
v_a_2612_ = v_val_2650_;
goto v___jp_2611_;
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_val_2650_);
lean_dec_ref(v_pkgDir_2570_);
lean_del_object(v___x_2568_);
lean_dec_ref(v_dir_2566_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
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
lean_object* v_name_2681_; lean_object* v_manifestFile_x3f_2682_; lean_object* v_url_2683_; lean_object* v_rev_2684_; lean_object* v_subDir_x3f_2685_; uint8_t v___x_2686_; lean_object* v_sname_2687_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v_a_2693_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v_val_2733_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v_relGitDir_2778_; lean_object* v___y_2780_; lean_object* v_gitDir_2783_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2797_; uint8_t v_a_2809_; lean_object* v___y_2819_; lean_object* v___y_2820_; uint8_t v_val_2821_; uint8_t v___y_2849_; lean_object* v_a_2850_; uint8_t v___x_2860_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v_name_2681_ = lean_ctor_get(v_manifestEntry_2516_, 0);
v_manifestFile_x3f_2682_ = lean_ctor_get(v_manifestEntry_2516_, 3);
v_url_2683_ = lean_ctor_get(v_src_2563_, 0);
lean_inc_ref(v_url_2683_);
v_rev_2684_ = lean_ctor_get(v_src_2563_, 1);
lean_inc_ref(v_rev_2684_);
v_subDir_x3f_2685_ = lean_ctor_get(v_src_2563_, 3);
lean_inc(v_subDir_x3f_2685_);
lean_dec_ref(v_src_2563_);
v___x_2686_ = 0;
lean_inc(v_name_2681_);
v_sname_2687_ = l_Lean_Name_toString(v_name_2681_, v___x_2686_);
lean_inc_ref(v_sname_2687_);
v_relGitDir_2778_ = l_Lake_joinRelative(v_relPkgsDir_2519_, v_sname_2687_);
lean_inc_ref(v_relGitDir_2778_);
lean_inc_ref(v_wsDir_2518_);
v_gitDir_2783_ = l_Lake_joinRelative(v_wsDir_2518_, v_relGitDir_2778_);
v___x_2860_ = l_System_FilePath_isDir(v_gitDir_2783_);
v___x_2893_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2894_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2894_ == 0)
{
goto v___jp_2861_;
}
else
{
lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2896_ == 0)
{
if (v___x_2894_ == 0)
{
goto v___jp_2861_;
}
else
{
size_t v___x_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = ((size_t)0ULL);
v___x_2898_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2893_, v___x_2897_, v___x_2898_, v___x_2895_, v_a_2520_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_dec_ref(v___x_2899_);
goto v___jp_2861_;
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v_gitDir_2783_);
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_rev_2684_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2893_, v___x_2908_, v___x_2909_, v___x_2895_, v_a_2520_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_dec_ref(v___x_2910_);
goto v___jp_2861_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v_gitDir_2783_);
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_rev_2684_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
v___jp_2688_:
{
if (lean_obj_tag(v_a_2693_) == 1)
{
lean_dec_ref(v___y_2690_);
lean_dec_ref(v_sname_2687_);
if (lean_obj_tag(v_manifestFile_x3f_2682_) == 1)
{
lean_object* v_val_2694_; lean_object* v_val_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v_val_2694_ = lean_ctor_get(v_a_2693_, 0);
lean_inc_n(v_val_2694_, 2);
lean_dec_ref(v_a_2693_);
v_val_2695_ = lean_ctor_get(v_manifestFile_x3f_2682_, 0);
lean_inc(v_val_2695_);
v___x_2696_ = l_Lake_joinRelative(v_val_2694_, v_val_2695_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2699_ = l_Lake_Manifest_load(v___x_2696_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set_tag(v___x_2702_, 1);
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
v___y_2530_ = v___y_2689_;
v___y_2531_ = v___y_2691_;
v___y_2532_ = v_val_2694_;
v___y_2533_ = v___x_2697_;
v___y_2534_ = v___x_2698_;
v___y_2535_ = v___y_2692_;
v_val_2536_ = v___x_2705_;
goto v___jp_2529_;
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2699_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2699_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 0);
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
v___y_2530_ = v___y_2689_;
v___y_2531_ = v___y_2691_;
v___y_2532_ = v_val_2694_;
v___y_2533_ = v___x_2697_;
v___y_2534_ = v___x_2698_;
v___y_2535_ = v___y_2692_;
v_val_2536_ = v___x_2713_;
goto v___jp_2529_;
}
}
}
}
else
{
lean_object* v_val_2716_; lean_object* v___x_2717_; 
v_val_2716_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_val_2716_);
lean_dec_ref(v_a_2693_);
v___x_2717_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2523_ = v___y_2689_;
v___y_2524_ = v_val_2716_;
v___y_2525_ = v___y_2692_;
v_a_2526_ = v___x_2717_;
goto v___jp_2522_;
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec(v_a_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v___y_2689_);
lean_dec_ref(v_manifestEntry_2516_);
v___x_2718_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2719_ = lean_string_append(v_sname_2687_, v___x_2718_);
v___x_2720_ = lean_string_append(v___x_2719_, v___y_2690_);
lean_dec_ref(v___y_2690_);
v___x_2721_ = 3;
v___x_2722_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*1, v___x_2721_);
lean_inc_ref(v___y_2691_);
v___x_2723_ = lean_apply_2(v___y_2691_, v___x_2722_, lean_box(0));
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
}
v___jp_2726_:
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = lean_array_get_size(v___y_2731_);
v___x_2735_ = lean_nat_dec_lt(v___y_2729_, v___x_2734_);
if (v___x_2735_ == 0)
{
v___y_2689_ = v___y_2727_;
v___y_2690_ = v___y_2728_;
v___y_2691_ = v___y_2730_;
v___y_2692_ = v___y_2732_;
v_a_2693_ = v_val_2733_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_nat_dec_le(v___x_2734_, v___x_2734_);
if (v___x_2737_ == 0)
{
if (v___x_2735_ == 0)
{
v___y_2689_ = v___y_2727_;
v___y_2690_ = v___y_2728_;
v___y_2691_ = v___y_2730_;
v___y_2692_ = v___y_2732_;
v_a_2693_ = v_val_2733_;
goto v___jp_2688_;
}
else
{
size_t v___x_2738_; size_t v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = lean_usize_of_nat(v___x_2734_);
v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2731_, v___x_2738_, v___x_2739_, v___x_2736_, v___y_2730_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_dec_ref(v___x_2740_);
v___y_2689_ = v___y_2727_;
v___y_2690_ = v___y_2728_;
v___y_2691_ = v___y_2730_;
v___y_2692_ = v___y_2732_;
v_a_2693_ = v_val_2733_;
goto v___jp_2688_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_val_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v_sname_2687_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
else
{
size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = lean_usize_of_nat(v___x_2734_);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2731_, v___x_2749_, v___x_2750_, v___x_2736_, v___y_2730_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_dec_ref(v___x_2751_);
v___y_2689_ = v___y_2727_;
v___y_2690_ = v___y_2728_;
v___y_2691_ = v___y_2730_;
v___y_2692_ = v___y_2732_;
v_a_2693_ = v_val_2733_;
goto v___jp_2688_;
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_val_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v_sname_2687_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
v___jp_2760_:
{
lean_object* v_pkgDir_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
lean_inc_ref(v___y_2761_);
v_pkgDir_2764_ = l_Lake_joinRelative(v_wsDir_2518_, v___y_2761_);
lean_inc_ref(v_pkgDir_2764_);
v___x_2765_ = l_Lake_resolvePath(v_pkgDir_2764_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2768_ = lean_string_utf8_byte_size(v___x_2765_);
v___x_2769_ = lean_nat_dec_eq(v___x_2768_, v___x_2766_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2765_);
v___y_2727_ = v___y_2761_;
v___y_2728_ = v_pkgDir_2764_;
v___y_2729_ = v___x_2766_;
v___y_2730_ = v___y_2762_;
v___y_2731_ = v___x_2767_;
v___y_2732_ = v___y_2763_;
v_val_2733_ = v___x_2770_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2771_; 
lean_dec_ref(v___x_2765_);
v___x_2771_ = lean_box(0);
v___y_2727_ = v___y_2761_;
v___y_2728_ = v_pkgDir_2764_;
v___y_2729_ = v___x_2766_;
v___y_2730_ = v___y_2762_;
v___y_2731_ = v___x_2767_;
v___y_2732_ = v___y_2763_;
v_val_2733_ = v___x_2771_;
goto v___jp_2726_;
}
}
v___jp_2772_:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lake_Git_filterUrl_x3f(v_url_2683_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v___x_2776_; 
v___x_2776_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2761_ = v___y_2774_;
v___y_2762_ = v___y_2773_;
v___y_2763_ = v___x_2776_;
goto v___jp_2760_;
}
else
{
lean_object* v_val_2777_; 
v_val_2777_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_val_2777_);
lean_dec_ref(v___x_2775_);
v___y_2761_ = v___y_2774_;
v___y_2762_ = v___y_2773_;
v___y_2763_ = v_val_2777_;
goto v___jp_2760_;
}
}
v___jp_2779_:
{
if (lean_obj_tag(v_subDir_x3f_2685_) == 0)
{
v___y_2773_ = v___y_2780_;
v___y_2774_ = v_relGitDir_2778_;
goto v___jp_2772_;
}
else
{
lean_object* v_val_2781_; lean_object* v___x_2782_; 
v_val_2781_ = lean_ctor_get(v_subDir_x3f_2685_, 0);
lean_inc(v_val_2781_);
lean_dec_ref(v_subDir_x3f_2685_);
v___x_2782_ = l_Lake_joinRelative(v_relGitDir_2778_, v_val_2781_);
v___y_2773_ = v___y_2780_;
v___y_2774_ = v___x_2782_;
goto v___jp_2772_;
}
}
v___jp_2784_:
{
lean_object* v___x_2787_; 
lean_inc_ref(v_sname_2687_);
v___x_2787_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2520_, v_sname_2687_, v_gitDir_2783_, v___y_2786_, v___y_2785_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_dec_ref(v___x_2787_);
v___y_2780_ = v_a_2520_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
v___jp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_rev_2684_);
lean_inc_ref(v_sname_2687_);
v___x_2799_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_2520_, v_sname_2687_, v_gitDir_2783_, v___y_2797_, v___x_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_dec_ref(v___x_2799_);
v___y_2780_ = v_a_2520_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
v___jp_2808_:
{
if (v_a_2809_ == 0)
{
lean_dec_ref(v_gitDir_2783_);
v___y_2780_ = v_a_2520_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2810_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_sname_2687_);
v___x_2811_ = lean_string_append(v_sname_2687_, v___x_2810_);
v___x_2812_ = lean_string_append(v___x_2811_, v_gitDir_2783_);
lean_dec_ref(v_gitDir_2783_);
v___x_2813_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_2814_ = lean_string_append(v___x_2812_, v___x_2813_);
v___x_2815_ = 2;
v___x_2816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set_uint8(v___x_2816_, sizeof(void*)*1, v___x_2815_);
lean_inc_ref(v_a_2520_);
v___x_2817_ = lean_apply_2(v_a_2520_, v___x_2816_, lean_box(0));
v___y_2780_ = v_a_2520_;
goto v___jp_2779_;
}
}
v___jp_2818_:
{
lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2822_ = lean_array_get_size(v___y_2820_);
v___x_2823_ = lean_nat_dec_lt(v___y_2819_, v___x_2822_);
if (v___x_2823_ == 0)
{
v_a_2809_ = v_val_2821_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_nat_dec_le(v___x_2822_, v___x_2822_);
if (v___x_2825_ == 0)
{
if (v___x_2823_ == 0)
{
v_a_2809_ = v_val_2821_;
goto v___jp_2808_;
}
else
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = lean_usize_of_nat(v___x_2822_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2820_, v___x_2826_, v___x_2827_, v___x_2824_, v_a_2520_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_dec_ref(v___x_2828_);
v_a_2809_ = v_val_2821_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v_gitDir_2783_);
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
else
{
size_t v___x_2837_; size_t v___x_2838_; lean_object* v___x_2839_; 
v___x_2837_ = ((size_t)0ULL);
v___x_2838_ = lean_usize_of_nat(v___x_2822_);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2820_, v___x_2837_, v___x_2838_, v___x_2824_, v_a_2520_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_dec_ref(v___x_2839_);
v_a_2809_ = v_val_2821_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_gitDir_2783_);
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
}
v___jp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2851_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_rev_2684_);
lean_inc_ref(v___x_2852_);
v___x_2853_ = l_Option_instDecidableEq___redArg(v___x_2851_, v_a_2850_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v_pkgUrlMap_2854_; lean_object* v___x_2855_; 
v_pkgUrlMap_2854_ = lean_ctor_get(v_lakeEnv_2517_, 5);
v___x_2855_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2854_, v_name_2681_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_inc_ref(v_url_2683_);
v___y_2785_ = v___x_2852_;
v___y_2786_ = v_url_2683_;
goto v___jp_2784_;
}
else
{
lean_object* v_val_2856_; 
v_val_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_val_2856_);
lean_dec_ref(v___x_2855_);
v___y_2785_ = v___x_2852_;
v___y_2786_ = v_val_2856_;
goto v___jp_2784_;
}
}
else
{
uint8_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec_ref(v___x_2852_);
lean_inc_ref(v_gitDir_2783_);
v___x_2857_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_2783_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_2857_ == 0)
{
v___y_2819_ = v___x_2858_;
v___y_2820_ = v___x_2859_;
v_val_2821_ = v___y_2849_;
goto v___jp_2818_;
}
else
{
v___y_2819_ = v___x_2858_;
v___y_2820_ = v___x_2859_;
v_val_2821_ = v___x_2686_;
goto v___jp_2818_;
}
}
}
v___jp_2861_:
{
if (v___x_2860_ == 0)
{
lean_object* v_pkgUrlMap_2862_; lean_object* v___x_2863_; 
v_pkgUrlMap_2862_ = lean_ctor_get(v_lakeEnv_2517_, 5);
v___x_2863_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2862_, v_name_2681_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_inc_ref(v_url_2683_);
v___y_2797_ = v_url_2683_;
goto v___jp_2796_;
}
else
{
lean_object* v_val_2864_; 
v_val_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_val_2864_);
lean_dec_ref(v___x_2863_);
v___y_2797_ = v_val_2864_;
goto v___jp_2796_;
}
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2865_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_2783_);
v___x_2866_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2865_, v_gitDir_2783_);
v___x_2867_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2868_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2868_ == 0)
{
v___y_2849_ = v___x_2860_;
v_a_2850_ = v___x_2866_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2870_ == 0)
{
if (v___x_2868_ == 0)
{
v___y_2849_ = v___x_2860_;
v_a_2850_ = v___x_2866_;
goto v___jp_2848_;
}
else
{
size_t v___x_2871_; size_t v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = ((size_t)0ULL);
v___x_2872_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2867_, v___x_2871_, v___x_2872_, v___x_2869_, v_a_2520_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_dec_ref(v___x_2873_);
v___y_2849_ = v___x_2860_;
v_a_2850_ = v___x_2866_;
goto v___jp_2848_;
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v___x_2866_);
lean_dec_ref(v_gitDir_2783_);
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_rev_2684_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
else
{
size_t v___x_2882_; size_t v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2867_, v___x_2882_, v___x_2883_, v___x_2869_, v_a_2520_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_dec_ref(v___x_2884_);
v___y_2849_ = v___x_2860_;
v_a_2850_ = v___x_2866_;
goto v___jp_2848_;
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v___x_2866_);
lean_dec_ref(v_gitDir_2783_);
lean_dec_ref(v_relGitDir_2778_);
lean_dec_ref(v_sname_2687_);
lean_dec(v_subDir_x3f_2685_);
lean_dec_ref(v_rev_2684_);
lean_dec_ref(v_url_2683_);
lean_dec_ref(v_wsDir_2518_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
}
}
}
v___jp_2522_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2527_, 0, v___y_2524_);
lean_ctor_set(v___x_2527_, 1, v___y_2523_);
lean_ctor_set(v___x_2527_, 2, v___y_2525_);
lean_ctor_set(v___x_2527_, 3, v_a_2526_);
lean_ctor_set(v___x_2527_, 4, v_manifestEntry_2516_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
v___jp_2529_:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = lean_array_get_size(v___y_2534_);
v___x_2538_ = lean_nat_dec_lt(v___y_2533_, v___x_2537_);
if (v___x_2538_ == 0)
{
v___y_2523_ = v___y_2530_;
v___y_2524_ = v___y_2532_;
v___y_2525_ = v___y_2535_;
v_a_2526_ = v_val_2536_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_nat_dec_le(v___x_2537_, v___x_2537_);
if (v___x_2540_ == 0)
{
if (v___x_2538_ == 0)
{
v___y_2523_ = v___y_2530_;
v___y_2524_ = v___y_2532_;
v___y_2525_ = v___y_2535_;
v_a_2526_ = v_val_2536_;
goto v___jp_2522_;
}
else
{
size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2537_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2534_, v___x_2541_, v___x_2542_, v___x_2539_, v___y_2531_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_dec_ref(v___x_2543_);
v___y_2523_ = v___y_2530_;
v___y_2524_ = v___y_2532_;
v___y_2525_ = v___y_2535_;
v_a_2526_ = v_val_2536_;
goto v___jp_2522_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v_val_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2532_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
else
{
size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = lean_usize_of_nat(v___x_2537_);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2534_, v___x_2552_, v___x_2553_, v___x_2539_, v___y_2531_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_dec_ref(v___x_2554_);
v___y_2523_ = v___y_2530_;
v___y_2524_ = v___y_2532_;
v___y_2525_ = v___y_2535_;
v_a_2526_ = v_val_2536_;
goto v___jp_2522_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_val_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2532_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_manifestEntry_2516_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_2919_, lean_object* v_lakeEnv_2920_, lean_object* v_wsDir_2921_, lean_object* v_relPkgsDir_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lake_PackageEntry_materialize(v_manifestEntry_2919_, v_lakeEnv_2920_, v_wsDir_2921_, v_relPkgsDir_2922_, v_a_2923_);
lean_dec_ref(v_a_2923_);
lean_dec_ref(v_lakeEnv_2920_);
return v_res_2925_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
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
res = runtime_initialize_Lake_Util_IO(builtin);
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
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
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
res = initialize_Lake_Util_IO(builtin);
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
