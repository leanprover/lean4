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
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = l_Lake_instInhabitedPackageEntry_default;
v___x_919_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_920_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
lean_ctor_set(v___x_921_, 3, v___x_919_);
lean_ctor_set(v___x_921_, 4, v___x_918_);
return v___x_921_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_922_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_924_){
_start:
{
lean_object* v_manifestEntry_925_; lean_object* v_name_926_; 
v_manifestEntry_925_ = lean_ctor_get(v_self_924_, 4);
v_name_926_ = lean_ctor_get(v_manifestEntry_925_, 0);
lean_inc(v_name_926_);
return v_name_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lake_MaterializedDep_name(v_self_927_);
lean_dec_ref(v_self_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_929_){
_start:
{
lean_object* v_manifestEntry_930_; lean_object* v_name_931_; uint8_t v___x_932_; lean_object* v___x_933_; 
v_manifestEntry_930_ = lean_ctor_get(v_self_929_, 4);
lean_inc_ref(v_manifestEntry_930_);
lean_dec_ref(v_self_929_);
v_name_931_ = lean_ctor_get(v_manifestEntry_930_, 0);
lean_inc(v_name_931_);
lean_dec_ref(v_manifestEntry_930_);
v___x_932_ = 0;
v___x_933_ = l_Lean_Name_toString(v_name_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_934_){
_start:
{
lean_object* v_manifestEntry_935_; lean_object* v_scope_936_; 
v_manifestEntry_935_ = lean_ctor_get(v_self_934_, 4);
v_scope_936_ = lean_ctor_get(v_manifestEntry_935_, 1);
lean_inc_ref(v_scope_936_);
return v_scope_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lake_MaterializedDep_scope(v_self_937_);
lean_dec_ref(v_self_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_939_){
_start:
{
lean_object* v_manifestEntry_940_; lean_object* v_manifestFile_x3f_941_; 
v_manifestEntry_940_ = lean_ctor_get(v_self_939_, 4);
v_manifestFile_x3f_941_ = lean_ctor_get(v_manifestEntry_940_, 3);
lean_inc(v_manifestFile_x3f_941_);
return v_manifestFile_x3f_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_942_);
lean_dec_ref(v_self_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_944_){
_start:
{
lean_object* v_manifestEntry_945_; lean_object* v_manifestFile_x3f_946_; 
v_manifestEntry_945_ = lean_ctor_get(v_self_944_, 4);
v_manifestFile_x3f_946_ = lean_ctor_get(v_manifestEntry_945_, 3);
if (lean_obj_tag(v_manifestFile_x3f_946_) == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_Lake_defaultManifestFile;
return v___x_947_;
}
else
{
lean_object* v_val_948_; 
v_val_948_ = lean_ctor_get(v_manifestFile_x3f_946_, 0);
lean_inc(v_val_948_);
return v_val_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lake_MaterializedDep_relManifestFile(v_self_949_);
lean_dec_ref(v_self_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_951_){
_start:
{
lean_object* v_manifestEntry_952_; lean_object* v_manifestFile_x3f_953_; 
v_manifestEntry_952_ = lean_ctor_get(v_self_951_, 4);
v_manifestFile_x3f_953_ = lean_ctor_get(v_manifestEntry_952_, 3);
if (lean_obj_tag(v_manifestFile_x3f_953_) == 0)
{
lean_object* v_pkgDir_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_pkgDir_954_ = lean_ctor_get(v_self_951_, 0);
lean_inc_ref(v_pkgDir_954_);
lean_dec_ref(v_self_951_);
v___x_955_ = l_Lake_defaultManifestFile;
v___x_956_ = l_Lake_joinRelative(v_pkgDir_954_, v___x_955_);
return v___x_956_;
}
else
{
lean_object* v_pkgDir_957_; lean_object* v_val_958_; lean_object* v___x_959_; 
lean_inc_ref(v_manifestFile_x3f_953_);
v_pkgDir_957_ = lean_ctor_get(v_self_951_, 0);
lean_inc_ref(v_pkgDir_957_);
lean_dec_ref(v_self_951_);
v_val_958_ = lean_ctor_get(v_manifestFile_x3f_953_, 0);
lean_inc(v_val_958_);
lean_dec_ref(v_manifestFile_x3f_953_);
v___x_959_ = l_Lake_joinRelative(v_pkgDir_957_, v_val_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_960_){
_start:
{
lean_object* v_manifestEntry_961_; lean_object* v_configFile_962_; 
v_manifestEntry_961_ = lean_ctor_get(v_self_960_, 4);
v_configFile_962_ = lean_ctor_get(v_manifestEntry_961_, 2);
lean_inc_ref(v_configFile_962_);
return v_configFile_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_MaterializedDep_relConfigFile(v_self_963_);
lean_dec_ref(v_self_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_965_){
_start:
{
lean_object* v_manifestEntry_966_; lean_object* v_pkgDir_967_; lean_object* v_configFile_968_; lean_object* v___x_969_; 
v_manifestEntry_966_ = lean_ctor_get(v_self_965_, 4);
lean_inc_ref(v_manifestEntry_966_);
v_pkgDir_967_ = lean_ctor_get(v_self_965_, 0);
lean_inc_ref(v_pkgDir_967_);
lean_dec_ref(v_self_965_);
v_configFile_968_ = lean_ctor_get(v_manifestEntry_966_, 2);
lean_inc_ref(v_configFile_968_);
lean_dec_ref(v_manifestEntry_966_);
v___x_969_ = l_Lake_joinRelative(v_pkgDir_967_, v_configFile_968_);
return v___x_969_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_970_){
_start:
{
lean_object* v_manifest_x3f_971_; 
v_manifest_x3f_971_ = lean_ctor_get(v_self_970_, 3);
if (lean_obj_tag(v_manifest_x3f_971_) == 1)
{
lean_object* v_a_972_; uint8_t v_fixedToolchain_973_; 
v_a_972_ = lean_ctor_get(v_manifest_x3f_971_, 0);
v_fixedToolchain_973_ = lean_ctor_get_uint8(v_a_972_, sizeof(void*)*4);
return v_fixedToolchain_973_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = 0;
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lake_MaterializedDep_fixedToolchain(v_self_975_);
lean_dec_ref(v_self_975_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object* v_x_978_){
_start:
{
switch(lean_obj_tag(v_x_978_))
{
case 0:
{
lean_object* v___x_979_; 
v___x_979_ = lean_unsigned_to_nat(0u);
return v___x_979_;
}
case 1:
{
lean_object* v___x_980_; 
v___x_980_ = lean_unsigned_to_nat(1u);
return v___x_980_;
}
default: 
{
lean_object* v___x_981_; 
v___x_981_ = lean_unsigned_to_nat(2u);
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object* v_x_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_982_);
lean_dec(v_x_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object* v_t_984_, lean_object* v_k_985_){
_start:
{
if (lean_obj_tag(v_t_984_) == 0)
{
return v_k_985_;
}
else
{
lean_object* v_rev_986_; lean_object* v___x_987_; 
v_rev_986_ = lean_ctor_get(v_t_984_, 0);
lean_inc_ref(v_rev_986_);
lean_dec(v_t_984_);
v___x_987_ = lean_apply_1(v_k_985_, v_rev_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object* v_motive_988_, lean_object* v_ctorIdx_989_, lean_object* v_t_990_, lean_object* v_h_991_, lean_object* v_k_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_990_, v_k_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object* v_motive_994_, lean_object* v_ctorIdx_995_, lean_object* v_t_996_, lean_object* v_h_997_, lean_object* v_k_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(v_motive_994_, v_ctorIdx_995_, v_t_996_, v_h_997_, v_k_998_);
lean_dec(v_ctorIdx_995_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object* v_t_1000_, lean_object* v_none_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1000_, v_none_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object* v_motive_1003_, lean_object* v_t_1004_, lean_object* v_h_1005_, lean_object* v_none_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1004_, v_none_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object* v_t_1008_, lean_object* v_git_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1008_, v_git_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object* v_motive_1011_, lean_object* v_t_1012_, lean_object* v_h_1013_, lean_object* v_git_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1012_, v_git_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object* v_t_1016_, lean_object* v_ver_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1016_, v_ver_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object* v_motive_1019_, lean_object* v_t_1020_, lean_object* v_h_1021_, lean_object* v_ver_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_1020_, v_ver_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_scope_1032_, lean_object* v_name_1033_, lean_object* v_ver_1034_){
_start:
{
lean_object* v_fst_1036_; lean_object* v_snd_1037_; 
switch(lean_obj_tag(v_ver_1034_))
{
case 0:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1036_ = v___x_1058_;
v_snd_1037_ = v___x_1058_;
goto v___jp_1035_;
}
case 1:
{
lean_object* v_rev_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1074_; 
v_rev_1059_ = lean_ctor_get(v_ver_1034_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_ver_1034_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1061_ = v_ver_1034_;
v_isShared_1062_ = v_isSharedCheck_1074_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_rev_1059_);
lean_dec(v_ver_1034_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1074_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1063_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1064_ = l_String_quote(v_rev_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 3);
lean_ctor_set(v___x_1061_, 0, v___x_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1067_ = l_Std_Format_defWidth;
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = l_Std_Format_pretty(v___x_1066_, v___x_1067_, v___x_1068_, v___x_1068_);
v___x_1070_ = lean_string_append(v___x_1063_, v___x_1069_);
v___x_1071_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1072_ = lean_string_append(v___x_1071_, v___x_1069_);
lean_dec_ref(v___x_1069_);
v_fst_1036_ = v___x_1070_;
v_snd_1037_ = v___x_1072_;
goto v___jp_1035_;
}
}
}
default: 
{
lean_object* v_ver_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1091_; 
v_ver_1075_ = lean_ctor_get(v_ver_1034_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_ver_1034_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1077_ = v_ver_1034_;
v_isShared_1078_ = v_isSharedCheck_1091_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_ver_1075_);
lean_dec(v_ver_1034_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1091_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_toString_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v_toString_1079_ = lean_ctor_get(v_ver_1075_, 0);
lean_inc_ref(v_toString_1079_);
lean_dec_ref(v_ver_1075_);
v___x_1080_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1081_ = l_String_quote(v_toString_1079_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 3);
lean_ctor_set(v___x_1077_, 0, v___x_1081_);
v___x_1083_ = v___x_1077_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1084_ = l_Std_Format_defWidth;
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = l_Std_Format_pretty(v___x_1083_, v___x_1084_, v___x_1085_, v___x_1085_);
v___x_1087_ = lean_string_append(v___x_1080_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1089_ = lean_string_append(v___x_1088_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v_fst_1036_ = v___x_1087_;
v_snd_1037_ = v___x_1089_;
goto v___jp_1035_;
}
}
}
}
v___jp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1038_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1032_);
v___x_1039_ = lean_string_append(v_scope_1032_, v___x_1038_);
v___x_1040_ = lean_string_append(v___x_1039_, v_name_1033_);
v___x_1041_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_string_append(v___x_1042_, v_scope_1032_);
v___x_1044_ = lean_string_append(v___x_1043_, v___x_1038_);
v___x_1045_ = lean_string_append(v___x_1044_, v_name_1033_);
v___x_1046_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1047_, v_fst_1036_);
lean_dec_ref(v_fst_1036_);
v___x_1049_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___x_1051_ = lean_string_append(v___x_1050_, v_scope_1032_);
lean_dec_ref(v_scope_1032_);
v___x_1052_ = lean_string_append(v___x_1051_, v___x_1038_);
v___x_1053_ = lean_string_append(v___x_1052_, v_name_1033_);
v___x_1054_ = lean_string_append(v___x_1053_, v___x_1046_);
v___x_1055_ = lean_string_append(v___x_1054_, v_snd_1037_);
lean_dec_ref(v_snd_1037_);
v___x_1056_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1057_ = lean_string_append(v___x_1055_, v___x_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object* v_scope_1092_, lean_object* v_name_1093_, lean_object* v_ver_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1092_, v_name_1093_, v_ver_1094_);
lean_dec_ref(v_name_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_inc_ref(v___y_1098_);
v___x_1100_ = lean_apply_2(v___y_1098_, v___y_1097_, lean_box(0));
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(lean_object* v_x_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(v_x_1102_, v___y_1103_, v___y_1104_);
lean_dec_ref(v___y_1104_);
return v_res_1106_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_instMonadEIO(lean_box(0));
return v___x_1107_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0);
v___x_1109_ = l_ReaderT_instMonad___redArg(v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1112_, uint8_t v_inherited_1113_, lean_object* v_wsDir_1114_, lean_object* v_name_1115_, lean_object* v_relPkgDir_1116_, lean_object* v_remoteUrl_1117_, lean_object* v_src_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___y_1122_; lean_object* v_a_1123_; lean_object* v_pkgDir_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___f_1143_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v_val_1149_; lean_object* v_a_1179_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_val_1213_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
lean_inc_ref(v_relPkgDir_1116_);
v_pkgDir_1140_ = l_Lake_joinRelative(v_wsDir_1114_, v_relPkgDir_1116_);
v___x_1141_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_1140_);
v___x_1142_ = l_Lake_resolvePath(v_pkgDir_1140_);
v___f_1143_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1241_ = lean_string_utf8_byte_size(v___x_1142_);
v___x_1242_ = lean_nat_dec_eq(v___x_1241_, v___x_1210_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1142_);
v_val_1213_ = v___x_1243_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1244_; 
lean_dec_ref(v___x_1142_);
v___x_1244_ = lean_box(0);
v_val_1213_ = v___x_1244_;
goto v___jp_1212_;
}
v___jp_1121_:
{
lean_object* v_name_1124_; lean_object* v_scope_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1136_; 
v_name_1124_ = lean_ctor_get(v_dep_1112_, 0);
v_scope_1125_ = lean_ctor_get(v_dep_1112_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_dep_1112_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; 
v_unused_1137_ = lean_ctor_get(v_dep_1112_, 4);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_dep_1112_, 3);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_dep_1112_, 2);
lean_dec(v_unused_1139_);
v___x_1127_ = v_dep_1112_;
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_scope_1125_);
lean_inc(v_name_1124_);
lean_dec(v_dep_1112_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1129_ = l_Lake_defaultConfigFile;
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1131_, 0, v_name_1124_);
lean_ctor_set(v___x_1131_, 1, v_scope_1125_);
lean_ctor_set(v___x_1131_, 2, v___x_1129_);
lean_ctor_set(v___x_1131_, 3, v___x_1130_);
lean_ctor_set(v___x_1131_, 4, v_src_1118_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*5, v_inherited_1113_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 4, v___x_1131_);
lean_ctor_set(v___x_1127_, 3, v_a_1123_);
lean_ctor_set(v___x_1127_, 2, v_remoteUrl_1117_);
lean_ctor_set(v___x_1127_, 1, v_relPkgDir_1116_);
lean_ctor_set(v___x_1127_, 0, v___y_1122_);
v___x_1133_ = v___x_1127_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___y_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_relPkgDir_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_remoteUrl_1117_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_a_1123_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
}
v___jp_1144_:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_array_get_size(v___y_1148_);
v___x_1151_ = lean_nat_dec_lt(v___y_1145_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_dec_ref(v___y_1146_);
v___y_1122_ = v___y_1147_;
v_a_1123_ = v_val_1149_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_nat_dec_le(v___x_1150_, v___x_1150_);
if (v___x_1153_ == 0)
{
if (v___x_1151_ == 0)
{
lean_dec_ref(v___y_1146_);
v___y_1122_ = v___y_1147_;
v_a_1123_ = v_val_1149_;
goto v___jp_1121_;
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_2388__overap_1156_; lean_object* v___x_1157_; 
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_of_nat(v___x_1150_);
lean_inc_ref(v___y_1148_);
v___x_2388__overap_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1146_, v___f_1143_, v___y_1148_, v___x_1154_, v___x_1155_, v___x_1152_);
lean_inc_ref(v_a_1119_);
v___x_1157_ = lean_apply_2(v___x_2388__overap_1156_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_dec_ref(v___x_1157_);
v___y_1122_ = v___y_1147_;
v_a_1123_ = v_val_1149_;
goto v___jp_1121_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_val_1149_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_src_1118_);
lean_dec_ref(v_remoteUrl_1117_);
lean_dec_ref(v_relPkgDir_1116_);
lean_dec_ref(v_dep_1112_);
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
else
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_2398__overap_1168_; lean_object* v___x_1169_; 
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = lean_usize_of_nat(v___x_1150_);
lean_inc_ref(v___y_1148_);
v___x_2398__overap_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1146_, v___f_1143_, v___y_1148_, v___x_1166_, v___x_1167_, v___x_1152_);
lean_inc_ref(v_a_1119_);
v___x_1169_ = lean_apply_2(v___x_2398__overap_1168_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_dec_ref(v___x_1169_);
v___y_1122_ = v___y_1147_;
v_a_1123_ = v_val_1149_;
goto v___jp_1121_;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v_val_1149_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_src_1118_);
lean_dec_ref(v_remoteUrl_1117_);
lean_dec_ref(v_relPkgDir_1116_);
lean_dec_ref(v_dep_1112_);
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
v___jp_1178_:
{
if (lean_obj_tag(v_a_1179_) == 1)
{
lean_object* v_val_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_pkgDir_1140_);
lean_dec_ref(v_name_1115_);
v_val_1180_ = lean_ctor_get(v_a_1179_, 0);
lean_inc_n(v_val_1180_, 2);
lean_dec_ref(v_a_1179_);
v___x_1181_ = l_Lake_defaultManifestFile;
v___x_1182_ = l_Lake_joinRelative(v_val_1180_, v___x_1181_);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1185_ = l_Lake_Manifest_load(v___x_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 1);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v___y_1145_ = v___x_1183_;
v___y_1146_ = v___x_1141_;
v___y_1147_ = v_val_1180_;
v___y_1148_ = v___x_1184_;
v_val_1149_ = v___x_1191_;
goto v___jp_1144_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1185_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1185_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 0);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v___y_1145_ = v___x_1183_;
v___y_1146_ = v___x_1141_;
v___y_1147_ = v_val_1180_;
v___y_1148_ = v___x_1184_;
v_val_1149_ = v___x_1199_;
goto v___jp_1144_;
}
}
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_a_1179_);
lean_dec_ref(v_src_1118_);
lean_dec_ref(v_remoteUrl_1117_);
lean_dec_ref(v_relPkgDir_1116_);
lean_dec_ref(v_dep_1112_);
v___x_1202_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1203_ = lean_string_append(v_name_1115_, v___x_1202_);
v___x_1204_ = lean_string_append(v___x_1203_, v_pkgDir_1140_);
lean_dec_ref(v_pkgDir_1140_);
v___x_1205_ = 3;
v___x_1206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*1, v___x_1205_);
lean_inc_ref(v_a_1119_);
v___x_1207_ = lean_apply_2(v_a_1119_, v___x_1206_, lean_box(0));
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
v___jp_1212_:
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1214_ == 0)
{
v_a_1179_ = v_val_1213_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1216_ == 0)
{
if (v___x_1214_ == 0)
{
v_a_1179_ = v_val_1213_;
goto v___jp_1178_;
}
else
{
size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_2450__overap_1219_; lean_object* v___x_1220_; 
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2450__overap_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1141_, v___f_1143_, v___x_1211_, v___x_1217_, v___x_1218_, v___x_1215_);
lean_inc_ref(v_a_1119_);
v___x_1220_ = lean_apply_2(v___x_2450__overap_1219_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_dec_ref(v___x_1220_);
v_a_1179_ = v_val_1213_;
goto v___jp_1178_;
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_val_1213_);
lean_dec_ref(v_pkgDir_1140_);
lean_dec_ref(v_src_1118_);
lean_dec_ref(v_remoteUrl_1117_);
lean_dec_ref(v_relPkgDir_1116_);
lean_dec_ref(v_name_1115_);
lean_dec_ref(v_dep_1112_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
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
}
else
{
size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_2460__overap_1231_; lean_object* v___x_1232_; 
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2460__overap_1231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1141_, v___f_1143_, v___x_1211_, v___x_1229_, v___x_1230_, v___x_1215_);
lean_inc_ref(v_a_1119_);
v___x_1232_ = lean_apply_2(v___x_2460__overap_1231_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_dec_ref(v___x_1232_);
v_a_1179_ = v_val_1213_;
goto v___jp_1178_;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_val_1213_);
lean_dec_ref(v_pkgDir_1140_);
lean_dec_ref(v_src_1118_);
lean_dec_ref(v_remoteUrl_1117_);
lean_dec_ref(v_relPkgDir_1116_);
lean_dec_ref(v_name_1115_);
lean_dec_ref(v_dep_1112_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1245_, lean_object* v_inherited_1246_, lean_object* v_wsDir_1247_, lean_object* v_name_1248_, lean_object* v_relPkgDir_1249_, lean_object* v_remoteUrl_1250_, lean_object* v_src_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
uint8_t v_inherited_boxed_1254_; lean_object* v_res_1255_; 
v_inherited_boxed_1254_ = lean_unbox(v_inherited_1246_);
v_res_1255_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1245_, v_inherited_boxed_1254_, v_wsDir_1247_, v_name_1248_, v_relPkgDir_1249_, v_remoteUrl_1250_, v_src_1251_, v_a_1252_);
lean_dec_ref(v_a_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1256_, lean_object* v_name_1257_, lean_object* v_repo_1258_, lean_object* v_url_1259_, lean_object* v_rev_x3f_1260_){
_start:
{
uint8_t v___x_1262_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1262_ = l_System_FilePath_isDir(v_repo_1258_);
v___x_1266_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1267_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_1267_ == 0)
{
goto v___jp_1263_;
}
else
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_1269_ == 0)
{
if (v___x_1267_ == 0)
{
goto v___jp_1263_;
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = ((size_t)0ULL);
v___x_1271_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1266_, v___x_1270_, v___x_1271_, v___x_1268_, v_a_1256_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_dec_ref(v___x_1272_);
goto v___jp_1263_;
}
else
{
lean_dec(v_rev_x3f_1260_);
lean_dec_ref(v_url_1259_);
lean_dec_ref(v_repo_1258_);
lean_dec_ref(v_name_1257_);
return v___x_1272_;
}
}
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_1266_, v___x_1273_, v___x_1274_, v___x_1268_, v_a_1256_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_dec_ref(v___x_1275_);
goto v___jp_1263_;
}
else
{
lean_dec(v_rev_x3f_1260_);
lean_dec_ref(v_url_1259_);
lean_dec_ref(v_repo_1258_);
lean_dec_ref(v_name_1257_);
return v___x_1275_;
}
}
}
v___jp_1263_:
{
if (v___x_1262_ == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_1256_, v_name_1257_, v_repo_1258_, v_url_1259_, v_rev_x3f_1260_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; 
v___x_1265_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1256_, v_name_1257_, v_repo_1258_, v_url_1259_, v_rev_x3f_1260_);
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1276_, lean_object* v_name_1277_, lean_object* v_repo_1278_, lean_object* v_url_1279_, lean_object* v_rev_x3f_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1276_, v_name_1277_, v_repo_1278_, v_url_1279_, v_rev_x3f_1280_);
lean_dec_ref(v_a_1276_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1283_, uint8_t v_inherited_1284_, lean_object* v_lakeEnv_1285_, lean_object* v_wsDir_1286_, lean_object* v_name_1287_, lean_object* v_relPkgDir_1288_, lean_object* v_gitUrl_1289_, lean_object* v_remoteUrl_1290_, lean_object* v_inputRev_x3f_1291_, lean_object* v_subDir_x3f_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_pkgUrlMap_1298_; lean_object* v_name_1299_; lean_object* v_scope_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1516_; 
v_pkgUrlMap_1298_ = lean_ctor_get(v_lakeEnv_1285_, 5);
v_name_1299_ = lean_ctor_get(v_dep_1283_, 0);
v_scope_1300_ = lean_ctor_get(v_dep_1283_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_dep_1283_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1517_ = lean_ctor_get(v_dep_1283_, 4);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_dep_1283_, 3);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_dep_1283_, 2);
lean_dec(v_unused_1519_);
v___x_1302_ = v_dep_1283_;
v_isShared_1303_ = v_isSharedCheck_1516_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_scope_1300_);
lean_inc(v_name_1299_);
lean_dec(v_dep_1283_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1516_;
goto v_resetjp_1301_;
}
v___jp_1295_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
v_resetjp_1301_:
{
lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v_a_1308_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v_val_1322_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v_a_1353_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v_val_1390_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1431_; lean_object* v_a_1432_; lean_object* v_gitDir_1435_; lean_object* v___y_1437_; lean_object* v___x_1514_; 
lean_inc_ref(v_relPkgDir_1288_);
lean_inc_ref(v_wsDir_1286_);
v_gitDir_1435_ = l_Lake_joinRelative(v_wsDir_1286_, v_relPkgDir_1288_);
v___x_1514_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1298_, v_name_1299_);
if (lean_obj_tag(v___x_1514_) == 0)
{
v___y_1437_ = v_gitUrl_1289_;
goto v___jp_1436_;
}
else
{
lean_object* v_val_1515_; 
lean_dec_ref(v_gitUrl_1289_);
v_val_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_val_1515_);
lean_dec_ref(v___x_1514_);
v___y_1437_ = v_val_1515_;
goto v___jp_1436_;
}
v___jp_1304_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1309_ = l_Lake_defaultConfigFile;
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1311_, 0, v_name_1299_);
lean_ctor_set(v___x_1311_, 1, v_scope_1300_);
lean_ctor_set(v___x_1311_, 2, v___x_1309_);
lean_ctor_set(v___x_1311_, 3, v___x_1310_);
lean_ctor_set(v___x_1311_, 4, v___y_1307_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5, v_inherited_1284_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v___x_1311_);
lean_ctor_set(v___x_1302_, 3, v_a_1308_);
lean_ctor_set(v___x_1302_, 2, v_remoteUrl_1290_);
lean_ctor_set(v___x_1302_, 1, v___y_1305_);
lean_ctor_set(v___x_1302_, 0, v___y_1306_);
v___x_1313_ = v___x_1302_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___y_1306_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___y_1305_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_remoteUrl_1290_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_a_1308_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
v___jp_1316_:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_array_get_size(v___y_1317_);
v___x_1324_ = lean_nat_dec_lt(v___y_1318_, v___x_1323_);
if (v___x_1324_ == 0)
{
v___y_1305_ = v___y_1319_;
v___y_1306_ = v___y_1320_;
v___y_1307_ = v___y_1321_;
v_a_1308_ = v_val_1322_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = lean_nat_dec_le(v___x_1323_, v___x_1323_);
if (v___x_1326_ == 0)
{
if (v___x_1324_ == 0)
{
v___y_1305_ = v___y_1319_;
v___y_1306_ = v___y_1320_;
v___y_1307_ = v___y_1321_;
v_a_1308_ = v_val_1322_;
goto v___jp_1304_;
}
else
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1323_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1317_, v___x_1327_, v___x_1328_, v___x_1325_, v_a_1293_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_dec_ref(v___x_1329_);
v___y_1305_ = v___y_1319_;
v___y_1306_ = v___y_1320_;
v___y_1307_ = v___y_1321_;
v_a_1308_ = v_val_1322_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_val_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec_ref(v_remoteUrl_1290_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
else
{
size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = ((size_t)0ULL);
v___x_1339_ = lean_usize_of_nat(v___x_1323_);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1317_, v___x_1338_, v___x_1339_, v___x_1325_, v_a_1293_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_dec_ref(v___x_1340_);
v___y_1305_ = v___y_1319_;
v___y_1306_ = v___y_1320_;
v___y_1307_ = v___y_1321_;
v_a_1308_ = v_val_1322_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_val_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec_ref(v_remoteUrl_1290_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
}
v___jp_1349_:
{
if (lean_obj_tag(v_a_1353_) == 1)
{
lean_object* v_val_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec_ref(v___y_1350_);
lean_dec_ref(v_name_1287_);
v_val_1354_ = lean_ctor_get(v_a_1353_, 0);
lean_inc_n(v_val_1354_, 2);
lean_dec_ref(v_a_1353_);
v___x_1355_ = l_Lake_defaultManifestFile;
v___x_1356_ = l_Lake_joinRelative(v_val_1354_, v___x_1355_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1359_ = l_Lake_Manifest_load(v___x_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 1);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v___y_1317_ = v___x_1358_;
v___y_1318_ = v___x_1357_;
v___y_1319_ = v___y_1351_;
v___y_1320_ = v_val_1354_;
v___y_1321_ = v___y_1352_;
v_val_1322_ = v___x_1365_;
goto v___jp_1316_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 0);
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v___y_1317_ = v___x_1358_;
v___y_1318_ = v___x_1357_;
v___y_1319_ = v___y_1351_;
v___y_1320_ = v_val_1354_;
v___y_1321_ = v___y_1352_;
v_val_1322_ = v___x_1373_;
goto v___jp_1316_;
}
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v_a_1353_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec_ref(v_remoteUrl_1290_);
v___x_1376_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1377_ = lean_string_append(v_name_1287_, v___x_1376_);
v___x_1378_ = lean_string_append(v___x_1377_, v___y_1350_);
lean_dec_ref(v___y_1350_);
v___x_1379_ = 3;
v___x_1380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*1, v___x_1379_);
lean_inc_ref(v_a_1293_);
v___x_1381_ = lean_apply_2(v_a_1293_, v___x_1380_, lean_box(0));
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
v___jp_1384_:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_array_get_size(v___y_1385_);
v___x_1392_ = lean_nat_dec_lt(v___y_1386_, v___x_1391_);
if (v___x_1392_ == 0)
{
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___y_1388_;
v___y_1352_ = v___y_1389_;
v_a_1353_ = v_val_1390_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_nat_dec_le(v___x_1391_, v___x_1391_);
if (v___x_1394_ == 0)
{
if (v___x_1392_ == 0)
{
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___y_1388_;
v___y_1352_ = v___y_1389_;
v_a_1353_ = v_val_1390_;
goto v___jp_1349_;
}
else
{
size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = lean_usize_of_nat(v___x_1391_);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1385_, v___x_1395_, v___x_1396_, v___x_1393_, v_a_1293_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_dec_ref(v___x_1397_);
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___y_1388_;
v___y_1352_ = v___y_1389_;
v_a_1353_ = v_val_1390_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_val_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec_ref(v_remoteUrl_1290_);
lean_dec_ref(v_name_1287_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
else
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = lean_usize_of_nat(v___x_1391_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1385_, v___x_1406_, v___x_1407_, v___x_1393_, v_a_1293_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_dec_ref(v___x_1408_);
v___y_1350_ = v___y_1387_;
v___y_1351_ = v___y_1388_;
v___y_1352_ = v___y_1389_;
v_a_1353_ = v_val_1390_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_val_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec_ref(v_remoteUrl_1290_);
lean_dec_ref(v_name_1287_);
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
v___jp_1417_:
{
lean_object* v_pkgDir_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
lean_inc_ref(v___y_1420_);
v_pkgDir_1421_ = l_Lake_joinRelative(v_wsDir_1286_, v___y_1420_);
lean_inc_ref(v_pkgDir_1421_);
v___x_1422_ = l_Lake_resolvePath(v_pkgDir_1421_);
v___x_1423_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1423_, 0, v___y_1419_);
lean_ctor_set(v___x_1423_, 1, v___y_1418_);
lean_ctor_set(v___x_1423_, 2, v_inputRev_x3f_1291_);
lean_ctor_set(v___x_1423_, 3, v_subDir_x3f_1292_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1426_ = lean_string_utf8_byte_size(v___x_1422_);
v___x_1427_ = lean_nat_dec_eq(v___x_1426_, v___x_1424_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1422_);
v___y_1385_ = v___x_1425_;
v___y_1386_ = v___x_1424_;
v___y_1387_ = v_pkgDir_1421_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v___x_1423_;
v_val_1390_ = v___x_1428_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1429_; 
lean_dec_ref(v___x_1422_);
v___x_1429_ = lean_box(0);
v___y_1385_ = v___x_1425_;
v___y_1386_ = v___x_1424_;
v___y_1387_ = v_pkgDir_1421_;
v___y_1388_ = v___y_1420_;
v___y_1389_ = v___x_1423_;
v_val_1390_ = v___x_1429_;
goto v___jp_1384_;
}
}
v___jp_1430_:
{
if (lean_obj_tag(v_subDir_x3f_1292_) == 1)
{
lean_object* v_val_1433_; lean_object* v___x_1434_; 
v_val_1433_ = lean_ctor_get(v_subDir_x3f_1292_, 0);
lean_inc(v_val_1433_);
v___x_1434_ = l_Lake_joinRelative(v_relPkgDir_1288_, v_val_1433_);
v___y_1418_ = v_a_1432_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v___x_1434_;
goto v___jp_1417_;
}
else
{
v___y_1418_ = v_a_1432_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v_relPkgDir_1288_;
goto v___jp_1417_;
}
}
v___jp_1436_:
{
lean_object* v___x_1438_; 
lean_inc(v_inputRev_x3f_1291_);
lean_inc_ref(v___y_1437_);
lean_inc_ref(v_gitDir_1435_);
lean_inc_ref(v_name_1287_);
v___x_1438_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1293_, v_name_1287_, v_gitDir_1435_, v___y_1437_, v_inputRev_x3f_1291_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1504_; 
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1505_);
v___x_1440_ = v___x_1438_;
v_isShared_1441_ = v_isSharedCheck_1504_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v___x_1438_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1504_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1444_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1435_, v___x_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_a_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
lean_del_object(v___x_1440_);
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
v_a_1446_ = lean_ctor_get(v___x_1444_, 1);
lean_inc(v_a_1446_);
lean_dec_ref(v___x_1444_);
v___x_1447_ = lean_array_get_size(v_a_1446_);
v___x_1448_ = lean_nat_dec_lt(v___x_1442_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_dec(v_a_1446_);
v___y_1431_ = v___y_1437_;
v_a_1432_ = v_a_1445_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_nat_dec_le(v___x_1447_, v___x_1447_);
if (v___x_1450_ == 0)
{
if (v___x_1448_ == 0)
{
lean_dec(v_a_1446_);
v___y_1431_ = v___y_1437_;
v_a_1432_ = v_a_1445_;
goto v___jp_1430_;
}
else
{
size_t v___x_1451_; size_t v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = ((size_t)0ULL);
v___x_1452_ = lean_usize_of_nat(v___x_1447_);
v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1446_, v___x_1451_, v___x_1452_, v___x_1449_, v_a_1293_);
lean_dec(v_a_1446_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_dec_ref(v___x_1453_);
v___y_1431_ = v___y_1437_;
v_a_1432_ = v_a_1445_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_a_1445_);
lean_dec_ref(v___y_1437_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec(v_subDir_x3f_1292_);
lean_dec(v_inputRev_x3f_1291_);
lean_dec_ref(v_remoteUrl_1290_);
lean_dec_ref(v_relPkgDir_1288_);
lean_dec_ref(v_name_1287_);
lean_dec_ref(v_wsDir_1286_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = lean_usize_of_nat(v___x_1447_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1446_, v___x_1462_, v___x_1463_, v___x_1449_, v_a_1293_);
lean_dec(v_a_1446_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_dec_ref(v___x_1464_);
v___y_1431_ = v___y_1437_;
v_a_1432_ = v_a_1445_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_a_1445_);
lean_dec_ref(v___y_1437_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec(v_subDir_x3f_1292_);
lean_dec(v_inputRev_x3f_1291_);
lean_dec_ref(v_remoteUrl_1290_);
lean_dec_ref(v_relPkgDir_1288_);
lean_dec_ref(v_name_1287_);
lean_dec_ref(v_wsDir_1286_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
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
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
lean_dec_ref(v___y_1437_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec(v_subDir_x3f_1292_);
lean_dec(v_inputRev_x3f_1291_);
lean_dec_ref(v_remoteUrl_1290_);
lean_dec_ref(v_relPkgDir_1288_);
lean_dec_ref(v_name_1287_);
lean_dec_ref(v_wsDir_1286_);
v_a_1473_ = lean_ctor_get(v___x_1444_, 1);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1444_);
v___x_1474_ = lean_array_get_size(v_a_1473_);
v___x_1475_ = lean_nat_dec_lt(v___x_1442_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
lean_dec(v_a_1473_);
v___x_1476_ = lean_box(0);
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 1);
lean_ctor_set(v___x_1440_, 0, v___x_1476_);
v___x_1478_ = v___x_1440_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
else
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
lean_del_object(v___x_1440_);
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_nat_dec_le(v___x_1474_, v___x_1474_);
if (v___x_1481_ == 0)
{
if (v___x_1475_ == 0)
{
lean_dec(v_a_1473_);
goto v___jp_1295_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1474_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1473_, v___x_1482_, v___x_1483_, v___x_1480_, v_a_1293_);
lean_dec(v_a_1473_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec_ref(v___x_1484_);
goto v___jp_1295_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
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
v___x_1494_ = lean_usize_of_nat(v___x_1474_);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1473_, v___x_1493_, v___x_1494_, v___x_1480_, v_a_1293_);
lean_dec(v_a_1473_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_dec_ref(v___x_1495_);
goto v___jp_1295_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
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
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v___y_1437_);
lean_dec_ref(v_gitDir_1435_);
lean_del_object(v___x_1302_);
lean_dec_ref(v_scope_1300_);
lean_dec(v_name_1299_);
lean_dec(v_subDir_x3f_1292_);
lean_dec(v_inputRev_x3f_1291_);
lean_dec_ref(v_remoteUrl_1290_);
lean_dec_ref(v_relPkgDir_1288_);
lean_dec_ref(v_name_1287_);
lean_dec_ref(v_wsDir_1286_);
v_a_1506_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1438_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1438_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_1520_, lean_object* v_inherited_1521_, lean_object* v_lakeEnv_1522_, lean_object* v_wsDir_1523_, lean_object* v_name_1524_, lean_object* v_relPkgDir_1525_, lean_object* v_gitUrl_1526_, lean_object* v_remoteUrl_1527_, lean_object* v_inputRev_x3f_1528_, lean_object* v_subDir_x3f_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
uint8_t v_inherited_boxed_1532_; lean_object* v_res_1533_; 
v_inherited_boxed_1532_ = lean_unbox(v_inherited_1521_);
v_res_1533_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1520_, v_inherited_boxed_1532_, v_lakeEnv_1522_, v_wsDir_1523_, v_name_1524_, v_relPkgDir_1525_, v_gitUrl_1526_, v_remoteUrl_1527_, v_inputRev_x3f_1528_, v_subDir_x3f_1529_, v_a_1530_);
lean_dec_ref(v_a_1530_);
lean_dec_ref(v_lakeEnv_1522_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_1534_, lean_object* v_dep_1535_, uint8_t v_inherited_1536_, lean_object* v_lakeEnv_1537_, lean_object* v_wsDir_1538_, lean_object* v_name_1539_, lean_object* v_relPkgDir_1540_, lean_object* v_gitUrl_1541_, lean_object* v_remoteUrl_1542_, lean_object* v_inputRev_x3f_1543_, lean_object* v_subDir_x3f_1544_){
_start:
{
lean_object* v_pkgUrlMap_1549_; lean_object* v_name_1550_; lean_object* v_scope_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1767_; 
v_pkgUrlMap_1549_ = lean_ctor_get(v_lakeEnv_1537_, 5);
v_name_1550_ = lean_ctor_get(v_dep_1535_, 0);
v_scope_1551_ = lean_ctor_get(v_dep_1535_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_dep_1535_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; lean_object* v_unused_1769_; lean_object* v_unused_1770_; 
v_unused_1768_ = lean_ctor_get(v_dep_1535_, 4);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_dep_1535_, 3);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_dep_1535_, 2);
lean_dec(v_unused_1770_);
v___x_1553_ = v_dep_1535_;
v_isShared_1554_ = v_isSharedCheck_1767_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_scope_1551_);
lean_inc(v_name_1550_);
lean_dec(v_dep_1535_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1767_;
goto v_resetjp_1552_;
}
v___jp_1546_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_box(0);
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
v_resetjp_1552_:
{
lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v_a_1559_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v_val_1573_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v_a_1604_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v_val_1641_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1682_; lean_object* v_a_1683_; lean_object* v_gitDir_1686_; lean_object* v___y_1688_; lean_object* v___x_1765_; 
lean_inc_ref(v_relPkgDir_1540_);
lean_inc_ref(v_wsDir_1538_);
v_gitDir_1686_ = l_Lake_joinRelative(v_wsDir_1538_, v_relPkgDir_1540_);
v___x_1765_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1549_, v_name_1550_);
if (lean_obj_tag(v___x_1765_) == 0)
{
v___y_1688_ = v_gitUrl_1541_;
goto v___jp_1687_;
}
else
{
lean_object* v_val_1766_; 
lean_dec_ref(v_gitUrl_1541_);
v_val_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_val_1766_);
lean_dec_ref(v___x_1765_);
v___y_1688_ = v_val_1766_;
goto v___jp_1687_;
}
v___jp_1555_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1560_ = l_Lake_defaultConfigFile;
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1562_, 0, v_name_1550_);
lean_ctor_set(v___x_1562_, 1, v_scope_1551_);
lean_ctor_set(v___x_1562_, 2, v___x_1560_);
lean_ctor_set(v___x_1562_, 3, v___x_1561_);
lean_ctor_set(v___x_1562_, 4, v___y_1558_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*5, v_inherited_1536_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v___x_1562_);
lean_ctor_set(v___x_1553_, 3, v_a_1559_);
lean_ctor_set(v___x_1553_, 2, v_remoteUrl_1542_);
lean_ctor_set(v___x_1553_, 1, v___y_1557_);
lean_ctor_set(v___x_1553_, 0, v___y_1556_);
v___x_1564_ = v___x_1553_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___y_1556_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___y_1557_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_remoteUrl_1542_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v_a_1559_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
v___jp_1567_:
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = lean_array_get_size(v___y_1571_);
v___x_1575_ = lean_nat_dec_lt(v___y_1572_, v___x_1574_);
if (v___x_1575_ == 0)
{
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1569_;
v_a_1559_ = v_val_1573_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_nat_dec_le(v___x_1574_, v___x_1574_);
if (v___x_1577_ == 0)
{
if (v___x_1575_ == 0)
{
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1569_;
v_a_1559_ = v_val_1573_;
goto v___jp_1555_;
}
else
{
size_t v___x_1578_; size_t v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = ((size_t)0ULL);
v___x_1579_ = lean_usize_of_nat(v___x_1574_);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1571_, v___x_1578_, v___x_1579_, v___x_1576_, v_a_1534_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_dec_ref(v___x_1580_);
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1569_;
v_a_1559_ = v_val_1573_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_val_1573_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec_ref(v_remoteUrl_1542_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
else
{
size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = lean_usize_of_nat(v___x_1574_);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1571_, v___x_1589_, v___x_1590_, v___x_1576_, v_a_1534_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_dec_ref(v___x_1591_);
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1569_;
v_a_1559_ = v_val_1573_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_val_1573_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec_ref(v_remoteUrl_1542_);
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
v___jp_1600_:
{
if (lean_obj_tag(v_a_1604_) == 1)
{
lean_object* v_val_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref(v___y_1601_);
lean_dec_ref(v_name_1539_);
v_val_1605_ = lean_ctor_get(v_a_1604_, 0);
lean_inc_n(v_val_1605_, 2);
lean_dec_ref(v_a_1604_);
v___x_1606_ = l_Lake_defaultManifestFile;
v___x_1607_ = l_Lake_joinRelative(v_val_1605_, v___x_1606_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1610_ = l_Lake_Manifest_load(v___x_1607_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 1);
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
v___y_1568_ = v_val_1605_;
v___y_1569_ = v___y_1602_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v___x_1609_;
v___y_1572_ = v___x_1608_;
v_val_1573_ = v___x_1616_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1610_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1610_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 0);
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
v___y_1568_ = v_val_1605_;
v___y_1569_ = v___y_1602_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v___x_1609_;
v___y_1572_ = v___x_1608_;
v_val_1573_ = v___x_1624_;
goto v___jp_1567_;
}
}
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec(v_a_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec_ref(v_remoteUrl_1542_);
v___x_1627_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_1628_ = lean_string_append(v_name_1539_, v___x_1627_);
v___x_1629_ = lean_string_append(v___x_1628_, v___y_1601_);
lean_dec_ref(v___y_1601_);
v___x_1630_ = 3;
v___x_1631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*1, v___x_1630_);
lean_inc_ref(v_a_1534_);
v___x_1632_ = lean_apply_2(v_a_1534_, v___x_1631_, lean_box(0));
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
}
v___jp_1635_:
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = lean_array_get_size(v___y_1636_);
v___x_1643_ = lean_nat_dec_lt(v___y_1638_, v___x_1642_);
if (v___x_1643_ == 0)
{
v___y_1601_ = v___y_1637_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1639_;
v_a_1604_ = v_val_1641_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_nat_dec_le(v___x_1642_, v___x_1642_);
if (v___x_1645_ == 0)
{
if (v___x_1643_ == 0)
{
v___y_1601_ = v___y_1637_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1639_;
v_a_1604_ = v_val_1641_;
goto v___jp_1600_;
}
else
{
size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = lean_usize_of_nat(v___x_1642_);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1636_, v___x_1646_, v___x_1647_, v___x_1644_, v_a_1534_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_dec_ref(v___x_1648_);
v___y_1601_ = v___y_1637_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1639_;
v_a_1604_ = v_val_1641_;
goto v___jp_1600_;
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_val_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1637_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec_ref(v_remoteUrl_1542_);
lean_dec_ref(v_name_1539_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
size_t v___x_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = ((size_t)0ULL);
v___x_1658_ = lean_usize_of_nat(v___x_1642_);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1636_, v___x_1657_, v___x_1658_, v___x_1644_, v_a_1534_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_dec_ref(v___x_1659_);
v___y_1601_ = v___y_1637_;
v___y_1602_ = v___y_1640_;
v___y_1603_ = v___y_1639_;
v_a_1604_ = v_val_1641_;
goto v___jp_1600_;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_val_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1637_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec_ref(v_remoteUrl_1542_);
lean_dec_ref(v_name_1539_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
v___jp_1668_:
{
lean_object* v_pkgDir_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
lean_inc_ref(v___y_1671_);
v_pkgDir_1672_ = l_Lake_joinRelative(v_wsDir_1538_, v___y_1671_);
lean_inc_ref(v_pkgDir_1672_);
v___x_1673_ = l_Lake_resolvePath(v_pkgDir_1672_);
v___x_1674_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1670_);
lean_ctor_set(v___x_1674_, 1, v___y_1669_);
lean_ctor_set(v___x_1674_, 2, v_inputRev_x3f_1543_);
lean_ctor_set(v___x_1674_, 3, v_subDir_x3f_1544_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1677_ = lean_string_utf8_byte_size(v___x_1673_);
v___x_1678_ = lean_nat_dec_eq(v___x_1677_, v___x_1675_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1673_);
v___y_1636_ = v___x_1676_;
v___y_1637_ = v_pkgDir_1672_;
v___y_1638_ = v___x_1675_;
v___y_1639_ = v___y_1671_;
v___y_1640_ = v___x_1674_;
v_val_1641_ = v___x_1679_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1680_; 
lean_dec_ref(v___x_1673_);
v___x_1680_ = lean_box(0);
v___y_1636_ = v___x_1676_;
v___y_1637_ = v_pkgDir_1672_;
v___y_1638_ = v___x_1675_;
v___y_1639_ = v___y_1671_;
v___y_1640_ = v___x_1674_;
v_val_1641_ = v___x_1680_;
goto v___jp_1635_;
}
}
v___jp_1681_:
{
if (lean_obj_tag(v_subDir_x3f_1544_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; 
v_val_1684_ = lean_ctor_get(v_subDir_x3f_1544_, 0);
lean_inc(v_val_1684_);
v___x_1685_ = l_Lake_joinRelative(v_relPkgDir_1540_, v_val_1684_);
v___y_1669_ = v_a_1683_;
v___y_1670_ = v___y_1682_;
v___y_1671_ = v___x_1685_;
goto v___jp_1668_;
}
else
{
v___y_1669_ = v_a_1683_;
v___y_1670_ = v___y_1682_;
v___y_1671_ = v_relPkgDir_1540_;
goto v___jp_1668_;
}
}
v___jp_1687_:
{
lean_object* v___x_1689_; 
lean_inc(v_inputRev_x3f_1543_);
lean_inc_ref(v___y_1688_);
lean_inc_ref(v_gitDir_1686_);
lean_inc_ref(v_name_1539_);
v___x_1689_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1534_, v_name_1539_, v_gitDir_1686_, v___y_1688_, v_inputRev_x3f_1543_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1755_; 
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v___x_1689_, 0);
lean_dec(v_unused_1756_);
v___x_1691_ = v___x_1689_;
v_isShared_1692_ = v_isSharedCheck_1755_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v___x_1689_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1755_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_1695_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_1686_, v___x_1694_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_a_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
lean_del_object(v___x_1691_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
v_a_1697_ = lean_ctor_get(v___x_1695_, 1);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1695_);
v___x_1698_ = lean_array_get_size(v_a_1697_);
v___x_1699_ = lean_nat_dec_lt(v___x_1693_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec(v_a_1697_);
v___y_1682_ = v___y_1688_;
v_a_1683_ = v_a_1696_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_nat_dec_le(v___x_1698_, v___x_1698_);
if (v___x_1701_ == 0)
{
if (v___x_1699_ == 0)
{
lean_dec(v_a_1697_);
v___y_1682_ = v___y_1688_;
v_a_1683_ = v_a_1696_;
goto v___jp_1681_;
}
else
{
size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = lean_usize_of_nat(v___x_1698_);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1697_, v___x_1702_, v___x_1703_, v___x_1700_, v_a_1534_);
lean_dec(v_a_1697_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_dec_ref(v___x_1704_);
v___y_1682_ = v___y_1688_;
v_a_1683_ = v_a_1696_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_a_1696_);
lean_dec_ref(v___y_1688_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec(v_subDir_x3f_1544_);
lean_dec(v_inputRev_x3f_1543_);
lean_dec_ref(v_remoteUrl_1542_);
lean_dec_ref(v_relPkgDir_1540_);
lean_dec_ref(v_name_1539_);
lean_dec_ref(v_wsDir_1538_);
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
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
}
else
{
size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = lean_usize_of_nat(v___x_1698_);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1697_, v___x_1713_, v___x_1714_, v___x_1700_, v_a_1534_);
lean_dec(v_a_1697_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_dec_ref(v___x_1715_);
v___y_1682_ = v___y_1688_;
v_a_1683_ = v_a_1696_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1696_);
lean_dec_ref(v___y_1688_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec(v_subDir_x3f_1544_);
lean_dec(v_inputRev_x3f_1543_);
lean_dec_ref(v_remoteUrl_1542_);
lean_dec_ref(v_relPkgDir_1540_);
lean_dec_ref(v_name_1539_);
lean_dec_ref(v_wsDir_1538_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
lean_dec_ref(v___y_1688_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec(v_subDir_x3f_1544_);
lean_dec(v_inputRev_x3f_1543_);
lean_dec_ref(v_remoteUrl_1542_);
lean_dec_ref(v_relPkgDir_1540_);
lean_dec_ref(v_name_1539_);
lean_dec_ref(v_wsDir_1538_);
v_a_1724_ = lean_ctor_get(v___x_1695_, 1);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1695_);
v___x_1725_ = lean_array_get_size(v_a_1724_);
v___x_1726_ = lean_nat_dec_lt(v___x_1693_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_dec(v_a_1724_);
v___x_1727_ = lean_box(0);
if (v_isShared_1692_ == 0)
{
lean_ctor_set_tag(v___x_1691_, 1);
lean_ctor_set(v___x_1691_, 0, v___x_1727_);
v___x_1729_ = v___x_1691_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
lean_del_object(v___x_1691_);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_nat_dec_le(v___x_1725_, v___x_1725_);
if (v___x_1732_ == 0)
{
if (v___x_1726_ == 0)
{
lean_dec(v_a_1724_);
goto v___jp_1546_;
}
else
{
size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = lean_usize_of_nat(v___x_1725_);
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1724_, v___x_1733_, v___x_1734_, v___x_1731_, v_a_1534_);
lean_dec(v_a_1724_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_dec_ref(v___x_1735_);
goto v___jp_1546_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = lean_usize_of_nat(v___x_1725_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_1724_, v___x_1744_, v___x_1745_, v___x_1731_, v_a_1534_);
lean_dec(v_a_1724_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_dec_ref(v___x_1746_);
goto v___jp_1546_;
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
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
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v___y_1688_);
lean_dec_ref(v_gitDir_1686_);
lean_del_object(v___x_1553_);
lean_dec_ref(v_scope_1551_);
lean_dec(v_name_1550_);
lean_dec(v_subDir_x3f_1544_);
lean_dec(v_inputRev_x3f_1543_);
lean_dec_ref(v_remoteUrl_1542_);
lean_dec_ref(v_relPkgDir_1540_);
lean_dec_ref(v_name_1539_);
lean_dec_ref(v_wsDir_1538_);
v_a_1757_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1689_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1689_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_1771_, lean_object* v_dep_1772_, lean_object* v_inherited_1773_, lean_object* v_lakeEnv_1774_, lean_object* v_wsDir_1775_, lean_object* v_name_1776_, lean_object* v_relPkgDir_1777_, lean_object* v_gitUrl_1778_, lean_object* v_remoteUrl_1779_, lean_object* v_inputRev_x3f_1780_, lean_object* v_subDir_x3f_1781_, lean_object* v_a_1782_){
_start:
{
uint8_t v_inherited_boxed_1783_; lean_object* v_res_1784_; 
v_inherited_boxed_1783_ = lean_unbox(v_inherited_1773_);
v_res_1784_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1771_, v_dep_1772_, v_inherited_boxed_1783_, v_lakeEnv_1774_, v_wsDir_1775_, v_name_1776_, v_relPkgDir_1777_, v_gitUrl_1778_, v_remoteUrl_1779_, v_inputRev_x3f_1780_, v_subDir_x3f_1781_);
lean_dec_ref(v_lakeEnv_1774_);
lean_dec_ref(v_a_1771_);
return v_res_1784_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1787_ = lean_string_utf8_byte_size(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(lean_object* v_s_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1789_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0));
v___x_1790_ = lean_string_utf8_byte_size(v_s_1788_);
v___x_1791_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
v___x_1792_ = lean_nat_dec_le(v___x_1791_, v___x_1790_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; 
lean_dec_ref(v_s_1788_);
v___x_1793_ = lean_box(0);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_string_memcmp(v_s_1788_, v___x_1789_, v___x_1794_, v___x_1794_, v___x_1791_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
lean_dec_ref(v_s_1788_);
v___x_1796_ = lean_box(0);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_inc_ref(v_s_1788_);
v___x_1797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1797_, 0, v_s_1788_);
lean_ctor_set(v___x_1797_, 1, v___x_1794_);
lean_ctor_set(v___x_1797_, 2, v___x_1790_);
v___x_1798_ = l_String_Slice_pos_x21(v___x_1797_, v___x_1791_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1799_, 0, v_s_1788_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
lean_ctor_set(v___x_1799_, 2, v___x_1790_);
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(lean_object* v_s_1801_, lean_object* v_pat_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(lean_object* v_s_1804_, lean_object* v_pat_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(v_s_1804_, v_pat_1805_);
lean_dec_ref(v_pat_1805_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_1810_, lean_object* v_as_1811_, size_t v_sz_1812_, size_t v_i_1813_, lean_object* v_b_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_usize_dec_lt(v_i_1813_, v_sz_1812_);
if (v___x_1815_ == 0)
{
lean_inc_ref(v_b_1814_);
return v_b_1814_;
}
else
{
lean_object* v_a_1816_; lean_object* v_version_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_a_1816_ = lean_array_uget_borrowed(v_as_1811_, v_i_1813_);
v_version_1817_ = lean_ctor_get(v_a_1816_, 0);
v___x_1818_ = lean_box(0);
v___x_1819_ = l_Lake_VerRange_test(v_ver_1810_, v_version_1817_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; 
v___x_1820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_i_1813_, v___x_1821_);
v_i_1813_ = v___x_1822_;
v_b_1814_ = v___x_1820_;
goto _start;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_inc(v_a_1816_);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1816_);
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1818_);
return v___x_1826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_1827_, lean_object* v_as_1828_, lean_object* v_sz_1829_, lean_object* v_i_1830_, lean_object* v_b_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1829_);
lean_dec(v_sz_1829_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1830_);
lean_dec(v_i_1830_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_1827_, v_as_1828_, v_sz_boxed_1832_, v_i_boxed_1833_, v_b_1831_);
lean_dec_ref(v_b_1831_);
lean_dec_ref(v_as_1828_);
lean_dec_ref(v_ver_1827_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_1846_, uint8_t v_inherited_1847_, lean_object* v_lakeEnv_1848_, lean_object* v_wsDir_1849_, lean_object* v_relPkgsDir_1850_, lean_object* v_relParentDir_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v_rev_x3f_1884_; lean_object* v___y_1885_; lean_object* v_name_1888_; lean_object* v_scope_1889_; lean_object* v_version_x3f_1890_; lean_object* v_src_x3f_1891_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v_a_1917_; 
v_name_1888_ = lean_ctor_get(v_dep_1846_, 0);
v_scope_1889_ = lean_ctor_get(v_dep_1846_, 1);
v_version_x3f_1890_ = lean_ctor_get(v_dep_1846_, 2);
v_src_x3f_1891_ = lean_ctor_get(v_dep_1846_, 3);
lean_inc(v_src_x3f_1891_);
if (lean_obj_tag(v_src_x3f_1891_) == 1)
{
lean_object* v_val_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2105_; 
v_val_1960_ = lean_ctor_get(v_src_x3f_1891_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_src_x3f_1891_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_1962_ = v_src_x3f_1891_;
v_isShared_1963_ = v_isSharedCheck_2105_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_val_1960_);
lean_dec(v_src_x3f_1891_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2105_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
uint8_t v___x_1964_; lean_object* v_sname_1965_; 
v___x_1964_ = 0;
lean_inc(v_name_1888_);
v_sname_1965_ = l_Lean_Name_toString(v_name_1888_, v___x_1964_);
if (lean_obj_tag(v_val_1960_) == 0)
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2089_; 
lean_inc_ref(v_scope_1889_);
lean_inc(v_name_1888_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_lakeEnv_1848_);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_dep_1846_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; 
v_unused_2090_ = lean_ctor_get(v_dep_1846_, 4);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_dep_1846_, 3);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_dep_1846_, 2);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_dep_1846_, 1);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_dep_1846_, 0);
lean_dec(v_unused_2094_);
v___x_1967_ = v_dep_1846_;
v_isShared_1968_ = v_isSharedCheck_2089_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_dep_1846_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2089_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_dir_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2088_; 
v_dir_1969_ = lean_ctor_get(v_val_1960_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_val_1960_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_1971_ = v_val_1960_;
v_isShared_1972_ = v_isSharedCheck_2088_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_dir_1969_);
lean_dec(v_val_1960_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2088_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_relPkgDir_1973_; lean_object* v___x_1975_; 
v_relPkgDir_1973_ = l_Lake_joinRelative(v_relParentDir_1851_, v_dir_1969_);
lean_inc_ref(v_relPkgDir_1973_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v_relPkgDir_1973_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_relPkgDir_1973_);
v___x_1975_ = v_reuseFailAlloc_2087_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v_pkgDir_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___y_1980_; lean_object* v_a_1981_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v_val_1993_; lean_object* v_a_2021_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_val_2055_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
lean_inc_ref(v_relPkgDir_1973_);
v_pkgDir_1976_ = l_Lake_joinRelative(v_wsDir_1849_, v_relPkgDir_1973_);
lean_inc_ref(v_pkgDir_1976_);
v___x_1977_ = l_Lake_resolvePath(v_pkgDir_1976_);
v___x_1978_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2081_ = lean_string_utf8_byte_size(v___x_1977_);
v___x_2082_ = lean_nat_dec_eq(v___x_2081_, v___x_2052_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2084_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1977_);
v___x_2084_ = v___x_1962_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_1977_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v_val_2055_ = v___x_2084_;
goto v___jp_2054_;
}
}
else
{
lean_object* v___x_2086_; 
lean_dec_ref(v___x_1977_);
lean_del_object(v___x_1962_);
v___x_2086_ = lean_box(0);
v_val_2055_ = v___x_2086_;
goto v___jp_2054_;
}
v___jp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1982_ = l_Lake_defaultConfigFile;
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1984_, 0, v_name_1888_);
lean_ctor_set(v___x_1984_, 1, v_scope_1889_);
lean_ctor_set(v___x_1984_, 2, v___x_1982_);
lean_ctor_set(v___x_1984_, 3, v___x_1983_);
lean_ctor_set(v___x_1984_, 4, v___x_1975_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*5, v_inherited_1847_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v___x_1984_);
lean_ctor_set(v___x_1967_, 3, v_a_1981_);
lean_ctor_set(v___x_1967_, 2, v___x_1978_);
lean_ctor_set(v___x_1967_, 1, v_relPkgDir_1973_);
lean_ctor_set(v___x_1967_, 0, v___y_1980_);
v___x_1986_ = v___x_1967_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___y_1980_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_relPkgDir_1973_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_a_1981_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
}
v___jp_1989_:
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = lean_array_get_size(v___y_1990_);
v___x_1995_ = lean_nat_dec_lt(v___y_1991_, v___x_1994_);
if (v___x_1995_ == 0)
{
v___y_1980_ = v___y_1992_;
v_a_1981_ = v_val_1993_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_nat_dec_le(v___x_1994_, v___x_1994_);
if (v___x_1997_ == 0)
{
if (v___x_1995_ == 0)
{
v___y_1980_ = v___y_1992_;
v_a_1981_ = v_val_1993_;
goto v___jp_1979_;
}
else
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = lean_usize_of_nat(v___x_1994_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1990_, v___x_1998_, v___x_1999_, v___x_1996_, v_a_1852_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref(v___x_2000_);
v___y_1980_ = v___y_1992_;
v_a_1981_ = v_val_1993_;
goto v___jp_1979_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_val_1993_);
lean_dec_ref(v___y_1992_);
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_relPkgDir_1973_);
lean_del_object(v___x_1967_);
lean_dec_ref(v_scope_1889_);
lean_dec(v_name_1888_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
else
{
size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_of_nat(v___x_1994_);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_1990_, v___x_2009_, v___x_2010_, v___x_1996_, v_a_1852_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref(v___x_2011_);
v___y_1980_ = v___y_1992_;
v_a_1981_ = v_val_1993_;
goto v___jp_1979_;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_val_1993_);
lean_dec_ref(v___y_1992_);
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_relPkgDir_1973_);
lean_del_object(v___x_1967_);
lean_dec_ref(v_scope_1889_);
lean_dec(v_name_1888_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
}
v___jp_2020_:
{
if (lean_obj_tag(v_a_2021_) == 1)
{
lean_object* v_val_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec_ref(v_pkgDir_1976_);
lean_dec_ref(v_sname_1965_);
v_val_2022_ = lean_ctor_get(v_a_2021_, 0);
lean_inc_n(v_val_2022_, 2);
lean_dec_ref(v_a_2021_);
v___x_2023_ = l_Lake_defaultManifestFile;
v___x_2024_ = l_Lake_joinRelative(v_val_2022_, v___x_2023_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2027_ = l_Lake_Manifest_load(v___x_2024_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 1);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
v___y_1990_ = v___x_2026_;
v___y_1991_ = v___x_2025_;
v___y_1992_ = v_val_2022_;
v_val_1993_ = v___x_2033_;
goto v___jp_1989_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_a_2036_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2027_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2027_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 0);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
v___y_1990_ = v___x_2026_;
v___y_1991_ = v___x_2025_;
v___y_1992_ = v_val_2022_;
v_val_1993_ = v___x_2041_;
goto v___jp_1989_;
}
}
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v_a_2021_);
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_relPkgDir_1973_);
lean_del_object(v___x_1967_);
lean_dec_ref(v_scope_1889_);
lean_dec(v_name_1888_);
v___x_2044_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2045_ = lean_string_append(v_sname_1965_, v___x_2044_);
v___x_2046_ = lean_string_append(v___x_2045_, v_pkgDir_1976_);
lean_dec_ref(v_pkgDir_1976_);
v___x_2047_ = 3;
v___x_2048_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*1, v___x_2047_);
lean_inc_ref(v_a_1852_);
v___x_2049_ = lean_apply_2(v_a_1852_, v___x_2048_, lean_box(0));
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
v___jp_2054_:
{
uint8_t v___x_2056_; 
v___x_2056_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2056_ == 0)
{
v_a_2021_ = v_val_2055_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2058_ == 0)
{
if (v___x_2056_ == 0)
{
v_a_2021_ = v_val_2055_;
goto v___jp_2020_;
}
else
{
size_t v___x_2059_; size_t v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = ((size_t)0ULL);
v___x_2060_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2053_, v___x_2059_, v___x_2060_, v___x_2057_, v_a_1852_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_dec_ref(v___x_2061_);
v_a_2021_ = v_val_2055_;
goto v___jp_2020_;
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_val_2055_);
lean_dec_ref(v_pkgDir_1976_);
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_relPkgDir_1973_);
lean_del_object(v___x_1967_);
lean_dec_ref(v_sname_1965_);
lean_dec_ref(v_scope_1889_);
lean_dec(v_name_1888_);
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
else
{
size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2053_, v___x_2070_, v___x_2071_, v___x_2057_, v_a_1852_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_dec_ref(v___x_2072_);
v_a_2021_ = v_val_2055_;
goto v___jp_2020_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_val_2055_);
lean_dec_ref(v_pkgDir_1976_);
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_relPkgDir_1973_);
lean_del_object(v___x_1967_);
lean_dec_ref(v_sname_1965_);
lean_dec_ref(v_scope_1889_);
lean_dec(v_name_1888_);
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
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
lean_object* v_url_2095_; lean_object* v_rev_2096_; lean_object* v_subDir_2097_; lean_object* v___y_2099_; lean_object* v___x_2102_; 
lean_del_object(v___x_1962_);
lean_dec_ref(v_relParentDir_1851_);
v_url_2095_ = lean_ctor_get(v_val_1960_, 0);
lean_inc_ref_n(v_url_2095_, 2);
v_rev_2096_ = lean_ctor_get(v_val_1960_, 1);
lean_inc(v_rev_2096_);
v_subDir_2097_ = lean_ctor_get(v_val_1960_, 2);
lean_inc(v_subDir_2097_);
lean_dec_ref(v_val_1960_);
v___x_2102_ = l_Lake_Git_filterUrl_x3f(v_url_2095_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v___x_2103_; 
v___x_2103_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2099_ = v___x_2103_;
goto v___jp_2098_;
}
else
{
lean_object* v_val_2104_; 
v_val_2104_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_val_2104_);
lean_dec_ref(v___x_2102_);
v___y_2099_ = v_val_2104_;
goto v___jp_2098_;
}
v___jp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_inc_ref(v_sname_1965_);
v___x_2100_ = l_Lake_joinRelative(v_relPkgsDir_1850_, v_sname_1965_);
v___x_2101_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_1852_, v_dep_1846_, v_inherited_1847_, v_lakeEnv_1848_, v_wsDir_1849_, v_sname_1965_, v___x_2100_, v_url_2095_, v___y_2099_, v_rev_2096_, v_subDir_2097_);
lean_dec_ref(v_lakeEnv_1848_);
return v___x_2101_;
}
}
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v_fst_2116_; lean_object* v_snd_2117_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v_a_2147_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v_fst_2282_; lean_object* v_snd_2283_; uint8_t v___x_2310_; lean_object* v_a_2312_; 
lean_dec(v_src_x3f_1891_);
lean_dec_ref(v_relParentDir_1851_);
v___x_2106_ = lean_string_utf8_byte_size(v_scope_1889_);
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_nat_dec_eq(v___x_2106_, v___x_2107_);
if (v___x_2310_ == 0)
{
if (lean_obj_tag(v_version_x3f_1890_) == 1)
{
lean_object* v_val_2322_; lean_object* v___x_2323_; 
v_val_2322_ = lean_ctor_get(v_version_x3f_1890_, 0);
lean_inc(v_val_2322_);
v___x_2323_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_2322_);
if (lean_obj_tag(v___x_2323_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2332_; 
v_val_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2332_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2332_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2328_ = l_String_Slice_toString(v_val_2324_);
lean_dec(v_val_2324_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2328_);
v___x_2330_ = v___x_2326_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v_a_2312_ = v___x_2330_;
goto v___jp_2311_;
}
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec(v___x_2323_);
v___x_2333_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2334_ = lean_string_utf8_byte_size(v_val_2322_);
lean_inc(v_val_2322_);
v___x_2335_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_val_2322_, v___x_2333_, v___x_2107_, v___x_2334_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2352_; 
lean_inc(v_name_1888_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2352_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2352_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2340_ = 1;
v___x_2341_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1888_, v___x_2340_);
v___x_2342_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__9));
v___x_2343_ = lean_string_append(v___x_2341_, v___x_2342_);
v___x_2344_ = lean_string_append(v___x_2343_, v_a_2336_);
lean_dec(v_a_2336_);
v___x_2345_ = 3;
v___x_2346_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*1, v___x_2345_);
lean_inc_ref(v_a_1852_);
v___x_2347_ = lean_apply_2(v_a_1852_, v___x_2346_, lean_box(0));
v___x_2348_ = lean_box(0);
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 1);
lean_ctor_set(v___x_2338_, 0, v___x_2348_);
v___x_2350_ = v___x_2338_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2335_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2335_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 2);
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
v_a_2312_ = v___x_2358_;
goto v___jp_2311_;
}
}
}
}
}
else
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_box(0);
v_a_2312_ = v___x_2361_;
goto v___jp_2311_;
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_inc(v_name_1888_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___x_2362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1888_, v___x_2310_);
v___x_2363_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__10));
v___x_2364_ = lean_string_append(v___x_2362_, v___x_2363_);
v___x_2365_ = 3;
v___x_2366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set_uint8(v___x_2366_, sizeof(void*)*1, v___x_2365_);
lean_inc_ref(v_a_1852_);
v___x_2367_ = lean_apply_2(v_a_1852_, v___x_2366_, lean_box(0));
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
v___jp_2108_:
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_array_get_size(v_snd_2117_);
v___x_2119_ = lean_nat_dec_lt(v___x_2107_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_dec_ref(v_snd_2117_);
v___y_1910_ = v___y_2109_;
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2112_;
v___y_1914_ = v___y_2113_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2115_;
v_a_1917_ = v_fst_2116_;
goto v___jp_1909_;
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
lean_dec_ref(v_snd_2117_);
v___y_1910_ = v___y_2109_;
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2112_;
v___y_1914_ = v___y_2113_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2115_;
v_a_1917_ = v_fst_2116_;
goto v___jp_1909_;
}
else
{
size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2118_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2117_, v___x_2122_, v___x_2123_, v___x_2120_, v_a_1852_);
lean_dec_ref(v_snd_2117_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_dec_ref(v___x_2124_);
v___y_1910_ = v___y_2109_;
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2112_;
v___y_1914_ = v___y_2113_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2115_;
v_a_1917_ = v_fst_2116_;
goto v___jp_1909_;
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_fst_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
else
{
size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = ((size_t)0ULL);
v___x_2134_ = lean_usize_of_nat(v___x_2118_);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2117_, v___x_2133_, v___x_2134_, v___x_2120_, v_a_1852_);
lean_dec_ref(v_snd_2117_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref(v___x_2135_);
v___y_1910_ = v___y_2109_;
v___y_1911_ = v___y_2110_;
v___y_1912_ = v___y_2111_;
v___y_1913_ = v___y_2112_;
v___y_1914_ = v___y_2113_;
v___y_1915_ = v___y_2114_;
v___y_1916_ = v___y_2115_;
v_a_1917_ = v_fst_2116_;
goto v___jp_1909_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_fst_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
v___jp_2144_:
{
if (lean_obj_tag(v_a_2147_) == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_inc_ref(v_scope_1889_);
lean_dec_ref(v_a_2147_);
lean_dec(v___y_2145_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___x_2148_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2149_ = lean_string_append(v_scope_1889_, v___x_2148_);
v___x_2150_ = lean_string_append(v___x_2149_, v___y_2146_);
lean_dec_ref(v___y_2146_);
v___x_2151_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2152_ = lean_string_append(v___x_2150_, v___x_2151_);
v___x_2153_ = 3;
v___x_2154_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*1, v___x_2153_);
lean_inc_ref(v_a_1852_);
v___x_2155_ = lean_apply_2(v_a_1852_, v___x_2154_, lean_box(0));
v___x_2156_ = lean_box(0);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2278_; 
v_a_2158_ = lean_ctor_get(v_a_2147_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2147_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2160_ = v_a_2147_;
v_isShared_2161_ = v_isSharedCheck_2278_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v_a_2147_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2278_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
if (lean_obj_tag(v_a_2158_) == 0)
{
lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_inc_ref(v_scope_1889_);
lean_del_object(v___x_2160_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___x_2162_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_scope_1889_, v___y_2146_, v___y_2145_);
lean_dec_ref(v___y_2146_);
v___x_2163_ = 3;
v___x_2164_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*1, v___x_2163_);
lean_inc_ref(v_a_1852_);
v___x_2165_ = lean_apply_2(v_a_1852_, v___x_2164_, lean_box(0));
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
else
{
lean_object* v_val_2168_; lean_object* v___x_2169_; 
v_val_2168_ = lean_ctor_get(v_a_2158_, 0);
lean_inc(v_val_2168_);
lean_dec_ref(v_a_2158_);
v___x_2169_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2168_);
if (lean_obj_tag(v___x_2169_) == 1)
{
lean_object* v_val_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2277_; 
v_val_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2277_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_val_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2277_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
if (lean_obj_tag(v_val_2170_) == 0)
{
lean_object* v_url_2174_; lean_object* v_githubUrl_x3f_2175_; lean_object* v_defaultBranch_x3f_2176_; lean_object* v_subDir_x3f_2177_; lean_object* v_name_2178_; lean_object* v_fullName_2179_; lean_object* v___x_2180_; 
v_url_2174_ = lean_ctor_get(v_val_2170_, 1);
lean_inc_ref(v_url_2174_);
v_githubUrl_x3f_2175_ = lean_ctor_get(v_val_2170_, 2);
lean_inc(v_githubUrl_x3f_2175_);
v_defaultBranch_x3f_2176_ = lean_ctor_get(v_val_2170_, 3);
lean_inc(v_defaultBranch_x3f_2176_);
v_subDir_x3f_2177_ = lean_ctor_get(v_val_2170_, 4);
lean_inc(v_subDir_x3f_2177_);
lean_dec_ref(v_val_2170_);
v_name_2178_ = lean_ctor_get(v_val_2168_, 0);
lean_inc_ref(v_name_2178_);
v_fullName_2179_ = lean_ctor_get(v_val_2168_, 1);
lean_inc_ref(v_fullName_2179_);
lean_dec(v_val_2168_);
v___x_2180_ = l_Lake_joinRelative(v_relPkgsDir_1850_, v_name_2178_);
switch(lean_obj_tag(v___y_2145_))
{
case 0:
{
lean_object* v___x_2181_; 
lean_del_object(v___x_2160_);
lean_dec_ref(v___y_2146_);
v___x_2181_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (lean_obj_tag(v_defaultBranch_x3f_2176_) == 0)
{
uint8_t v___x_2182_; 
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_fullName_2179_);
lean_dec(v_subDir_x3f_2177_);
lean_dec(v_githubUrl_x3f_2175_);
lean_dec_ref(v_url_2174_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___x_2182_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2183_);
v___x_2185_ = v___x_2172_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v___x_2187_; uint8_t v___x_2188_; 
lean_del_object(v___x_2172_);
v___x_2187_ = lean_box(0);
v___x_2188_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2188_ == 0)
{
if (v___x_2182_ == 0)
{
goto v___jp_1854_;
}
else
{
size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2181_, v___x_2189_, v___x_2190_, v___x_2187_, v_a_1852_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_dec_ref(v___x_2191_);
goto v___jp_1854_;
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = ((size_t)0ULL);
v___x_2201_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2181_, v___x_2200_, v___x_2201_, v___x_2187_, v_a_1852_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_dec_ref(v___x_2202_);
goto v___jp_1854_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
}
else
{
lean_object* v_val_2211_; uint8_t v___x_2212_; 
lean_del_object(v___x_2172_);
v_val_2211_ = lean_ctor_get(v_defaultBranch_x3f_2176_, 0);
lean_inc(v_val_2211_);
lean_dec_ref(v_defaultBranch_x3f_2176_);
v___x_2212_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2212_ == 0)
{
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_val_2211_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2214_ == 0)
{
if (v___x_2212_ == 0)
{
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_val_2211_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2181_, v___x_2215_, v___x_2216_, v___x_2213_, v_a_1852_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref(v___x_2217_);
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_val_2211_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_val_2211_);
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_fullName_2179_);
lean_dec(v_subDir_x3f_2177_);
lean_dec(v_githubUrl_x3f_2175_);
lean_dec_ref(v_url_2174_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
size_t v___x_2226_; size_t v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2181_, v___x_2226_, v___x_2227_, v___x_2213_, v_a_1852_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_dec_ref(v___x_2228_);
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_val_2211_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_val_2211_);
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_fullName_2179_);
lean_dec(v_subDir_x3f_2177_);
lean_dec(v_githubUrl_x3f_2175_);
lean_dec_ref(v_url_2174_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
lean_dec(v_defaultBranch_x3f_2176_);
lean_del_object(v___x_2172_);
lean_del_object(v___x_2160_);
lean_dec_ref(v___y_2146_);
v_rev_2237_ = lean_ctor_get(v___y_2145_, 0);
lean_inc_ref(v_rev_2237_);
lean_dec_ref(v___y_2145_);
v___x_2238_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2239_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2239_ == 0)
{
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_rev_2237_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_box(0);
v___x_2241_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2241_ == 0)
{
if (v___x_2239_ == 0)
{
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_rev_2237_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2238_, v___x_2242_, v___x_2243_, v___x_2240_, v_a_1852_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_dec_ref(v___x_2244_);
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_rev_2237_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v_rev_2237_);
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_fullName_2179_);
lean_dec(v_subDir_x3f_2177_);
lean_dec(v_githubUrl_x3f_2175_);
lean_dec_ref(v_url_2174_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
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
v___x_2254_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2238_, v___x_2253_, v___x_2254_, v___x_2240_, v_a_1852_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_dec_ref(v___x_2255_);
v___y_1879_ = v_url_2174_;
v___y_1880_ = v_fullName_2179_;
v___y_1881_ = v___x_2180_;
v___y_1882_ = v_githubUrl_x3f_2175_;
v___y_1883_ = v_subDir_x3f_2177_;
v_rev_x3f_1884_ = v_rev_2237_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_rev_2237_);
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_fullName_2179_);
lean_dec(v_subDir_x3f_2177_);
lean_dec(v_githubUrl_x3f_2175_);
lean_dec_ref(v_url_2174_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
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
default: 
{
lean_object* v_ver_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec(v_defaultBranch_x3f_2176_);
lean_del_object(v___x_2172_);
v_ver_2264_ = lean_ctor_get(v___y_2145_, 0);
lean_inc_ref(v_ver_2264_);
lean_dec_ref(v___y_2145_);
v___x_2265_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___y_2146_);
lean_inc_ref(v_scope_1889_);
lean_inc_ref(v_lakeEnv_1848_);
v___x_2266_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1848_, v_scope_1889_, v___y_2146_, v___x_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v_a_2268_; lean_object* v___x_2270_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
v_a_2268_ = lean_ctor_get(v___x_2266_, 1);
lean_inc(v_a_2268_);
lean_dec_ref(v___x_2266_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v_a_2267_);
v___x_2270_ = v___x_2160_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2267_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
v___y_2109_ = v_url_2174_;
v___y_2110_ = v_fullName_2179_;
v___y_2111_ = v___x_2180_;
v___y_2112_ = v_githubUrl_x3f_2175_;
v___y_2113_ = v_ver_2264_;
v___y_2114_ = v_subDir_x3f_2177_;
v___y_2115_ = v___y_2146_;
v_fst_2116_ = v___x_2270_;
v_snd_2117_ = v_a_2268_;
goto v___jp_2108_;
}
}
else
{
lean_object* v_a_2272_; lean_object* v_a_2273_; lean_object* v___x_2275_; 
v_a_2272_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2272_);
v_a_2273_ = lean_ctor_get(v___x_2266_, 1);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2266_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 0);
lean_ctor_set(v___x_2160_, 0, v_a_2272_);
v___x_2275_ = v___x_2160_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2272_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
v___y_2109_ = v_url_2174_;
v___y_2110_ = v_fullName_2179_;
v___y_2111_ = v___x_2180_;
v___y_2112_ = v_githubUrl_x3f_2175_;
v___y_2113_ = v_ver_2264_;
v___y_2114_ = v_subDir_x3f_2177_;
v___y_2115_ = v___y_2146_;
v_fst_2116_ = v___x_2275_;
v_snd_2117_ = v_a_2273_;
goto v___jp_2108_;
}
}
}
}
}
else
{
lean_del_object(v___x_2172_);
lean_dec(v_val_2170_);
lean_del_object(v___x_2160_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___y_1858_ = v_val_2168_;
v___y_1859_ = v_a_1852_;
goto v___jp_1857_;
}
}
}
else
{
lean_dec(v___x_2169_);
lean_del_object(v___x_2160_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___y_1858_ = v_val_2168_;
v___y_1859_ = v_a_1852_;
goto v___jp_1857_;
}
}
}
}
}
v___jp_2279_:
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = lean_array_get_size(v_snd_2283_);
v___x_2285_ = lean_nat_dec_lt(v___x_2107_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_dec_ref(v_snd_2283_);
v___y_2145_ = v___y_2281_;
v___y_2146_ = v___y_2280_;
v_a_2147_ = v_fst_2282_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_nat_dec_le(v___x_2284_, v___x_2284_);
if (v___x_2287_ == 0)
{
if (v___x_2285_ == 0)
{
lean_dec_ref(v_snd_2283_);
v___y_2145_ = v___y_2281_;
v___y_2146_ = v___y_2280_;
v_a_2147_ = v_fst_2282_;
goto v___jp_2144_;
}
else
{
size_t v___x_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = lean_usize_of_nat(v___x_2284_);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2283_, v___x_2288_, v___x_2289_, v___x_2286_, v_a_1852_);
lean_dec_ref(v_snd_2283_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_dec_ref(v___x_2290_);
v___y_2145_ = v___y_2281_;
v___y_2146_ = v___y_2280_;
v_a_2147_ = v_fst_2282_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_fst_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
else
{
size_t v___x_2299_; size_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = lean_usize_of_nat(v___x_2284_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_2283_, v___x_2299_, v___x_2300_, v___x_2286_, v_a_1852_);
lean_dec_ref(v_snd_2283_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_dec_ref(v___x_2301_);
v___y_2145_ = v___y_2281_;
v___y_2146_ = v___y_2280_;
v_a_2147_ = v_fst_2282_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_fst_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_relPkgsDir_1850_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
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
return v___x_2307_;
}
}
}
}
}
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_inc(v_name_1888_);
v___x_2313_ = l_Lean_Name_toString(v_name_1888_, v___x_2310_);
v___x_2314_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
lean_inc_ref(v___x_2313_);
lean_inc_ref(v_scope_1889_);
lean_inc_ref(v_lakeEnv_1848_);
v___x_2315_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1848_, v_scope_1889_, v___x_2313_, v___x_2314_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
v_a_2317_ = lean_ctor_get(v___x_2315_, 1);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2315_);
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_a_2316_);
v___y_2280_ = v___x_2313_;
v___y_2281_ = v_a_2312_;
v_fst_2282_ = v___x_2318_;
v_snd_2283_ = v_a_2317_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2319_; lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2319_);
v_a_2320_ = lean_ctor_get(v___x_2315_, 1);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2315_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_a_2319_);
v___y_2280_ = v___x_2313_;
v___y_2281_ = v_a_2312_;
v_fst_2282_ = v___x_2321_;
v_snd_2283_ = v_a_2320_;
goto v___jp_2279_;
}
}
}
v___jp_1854_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
v___jp_1857_:
{
lean_object* v_fullName_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_fullName_1860_ = lean_ctor_get(v___y_1858_, 1);
lean_inc_ref(v_fullName_1860_);
lean_dec_ref(v___y_1858_);
v___x_1861_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_1862_ = lean_string_append(v_fullName_1860_, v___x_1861_);
v___x_1863_ = 3;
v___x_1864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set_uint8(v___x_1864_, sizeof(void*)*1, v___x_1863_);
lean_inc_ref(v___y_1859_);
v___x_1865_ = lean_apply_2(v___y_1859_, v___x_1864_, lean_box(0));
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
v___jp_1868_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___y_1872_);
v___x_1877_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_1846_, v_inherited_1847_, v_lakeEnv_1848_, v_wsDir_1849_, v___y_1870_, v___y_1871_, v___y_1869_, v___y_1875_, v___x_1876_, v___y_1873_, v___y_1874_);
lean_dec_ref(v_lakeEnv_1848_);
return v___x_1877_;
}
v___jp_1878_:
{
if (lean_obj_tag(v___y_1882_) == 0)
{
lean_object* v___x_1886_; 
v___x_1886_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_1869_ = v___y_1879_;
v___y_1870_ = v___y_1880_;
v___y_1871_ = v___y_1881_;
v___y_1872_ = v_rev_x3f_1884_;
v___y_1873_ = v___y_1883_;
v___y_1874_ = v___y_1885_;
v___y_1875_ = v___x_1886_;
goto v___jp_1868_;
}
else
{
lean_object* v_val_1887_; 
v_val_1887_ = lean_ctor_get(v___y_1882_, 0);
lean_inc(v_val_1887_);
lean_dec_ref(v___y_1882_);
v___y_1869_ = v___y_1879_;
v___y_1870_ = v___y_1880_;
v___y_1871_ = v___y_1881_;
v___y_1872_ = v_rev_x3f_1884_;
v___y_1873_ = v___y_1883_;
v___y_1874_ = v___y_1885_;
v___y_1875_ = v_val_1887_;
goto v___jp_1868_;
}
}
v___jp_1892_:
{
lean_object* v_toString_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_toString_1895_ = lean_ctor_get(v___y_1893_, 0);
lean_inc_ref(v_toString_1895_);
lean_dec_ref(v___y_1893_);
v___x_1896_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1897_ = lean_string_append(v_scope_1889_, v___x_1896_);
v___x_1898_ = lean_string_append(v___x_1897_, v___y_1894_);
lean_dec_ref(v___y_1894_);
v___x_1899_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_1900_ = lean_string_append(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_string_append(v___x_1900_, v_toString_1895_);
lean_dec_ref(v_toString_1895_);
v___x_1902_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_1903_ = lean_string_append(v___x_1901_, v___x_1902_);
v___x_1904_ = 3;
v___x_1905_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*1, v___x_1904_);
lean_inc_ref(v_a_1852_);
v___x_1906_ = lean_apply_2(v_a_1852_, v___x_1905_, lean_box(0));
v___x_1907_ = lean_box(0);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
v___jp_1909_:
{
if (lean_obj_tag(v_a_1917_) == 0)
{
lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1933_; 
lean_inc_ref(v_scope_1889_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_a_1917_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v_a_1917_, 0);
lean_dec(v_unused_1934_);
v___x_1919_ = v_a_1917_;
v_isShared_1920_ = v_isSharedCheck_1933_;
goto v_resetjp_1918_;
}
else
{
lean_dec(v_a_1917_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1933_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1921_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_1922_ = lean_string_append(v_scope_1889_, v___x_1921_);
v___x_1923_ = lean_string_append(v___x_1922_, v___y_1916_);
lean_dec_ref(v___y_1916_);
v___x_1924_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_1925_ = lean_string_append(v___x_1923_, v___x_1924_);
v___x_1926_ = 3;
v___x_1927_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*1, v___x_1926_);
lean_inc_ref(v_a_1852_);
v___x_1928_ = lean_apply_2(v_a_1852_, v___x_1927_, lean_box(0));
v___x_1929_ = lean_box(0);
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 1);
lean_ctor_set(v___x_1919_, 0, v___x_1929_);
v___x_1931_ = v___x_1919_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1936_; size_t v_sz_1937_; size_t v___x_1938_; lean_object* v___x_1939_; lean_object* v_fst_1940_; 
v_a_1935_ = lean_ctor_get(v_a_1917_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v_a_1917_);
v___x_1936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_1937_ = lean_array_size(v_a_1935_);
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_1914_, v_a_1935_, v_sz_1937_, v___x_1938_, v___x_1936_);
lean_dec(v_a_1935_);
v_fst_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_fst_1940_);
lean_dec_ref(v___x_1939_);
if (lean_obj_tag(v_fst_1940_) == 0)
{
lean_inc_ref(v_scope_1889_);
lean_dec(v___y_1915_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___y_1893_ = v___y_1914_;
v___y_1894_ = v___y_1916_;
goto v___jp_1892_;
}
else
{
lean_object* v_val_1941_; 
v_val_1941_ = lean_ctor_get(v_fst_1940_, 0);
lean_inc(v_val_1941_);
lean_dec_ref(v_fst_1940_);
if (lean_obj_tag(v_val_1941_) == 1)
{
lean_object* v_val_1942_; lean_object* v_version_1943_; lean_object* v_revision_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v___y_1914_);
v_val_1942_ = lean_ctor_get(v_val_1941_, 0);
lean_inc(v_val_1942_);
lean_dec_ref(v_val_1941_);
v_version_1943_ = lean_ctor_get(v_val_1942_, 0);
lean_inc_ref(v_version_1943_);
v_revision_1944_ = lean_ctor_get(v_val_1942_, 1);
lean_inc_ref(v_revision_1944_);
lean_dec(v_val_1942_);
v___x_1945_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1889_);
v___x_1946_ = lean_string_append(v_scope_1889_, v___x_1945_);
v___x_1947_ = lean_string_append(v___x_1946_, v___y_1916_);
lean_dec_ref(v___y_1916_);
v___x_1948_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_1949_ = lean_string_append(v___x_1947_, v___x_1948_);
v___x_1950_ = l_Lake_StdVer_toString(v_version_1943_);
v___x_1951_ = lean_string_append(v___x_1949_, v___x_1950_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_1953_ = lean_string_append(v___x_1951_, v___x_1952_);
v___x_1954_ = lean_string_append(v___x_1953_, v_revision_1944_);
v___x_1955_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_1956_ = lean_string_append(v___x_1954_, v___x_1955_);
v___x_1957_ = 1;
v___x_1958_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*1, v___x_1957_);
lean_inc_ref(v_a_1852_);
v___x_1959_ = lean_apply_2(v_a_1852_, v___x_1958_, lean_box(0));
v___y_1879_ = v___y_1910_;
v___y_1880_ = v___y_1911_;
v___y_1881_ = v___y_1912_;
v___y_1882_ = v___y_1913_;
v___y_1883_ = v___y_1915_;
v_rev_x3f_1884_ = v_revision_1944_;
v___y_1885_ = v_a_1852_;
goto v___jp_1878_;
}
else
{
lean_inc_ref(v_scope_1889_);
lean_dec(v_val_1941_);
lean_dec(v___y_1915_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v_wsDir_1849_);
lean_dec_ref(v_lakeEnv_1848_);
lean_dec_ref(v_dep_1846_);
v___y_1893_ = v___y_1914_;
v___y_1894_ = v___y_1916_;
goto v___jp_1892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2370_, lean_object* v_inherited_2371_, lean_object* v_lakeEnv_2372_, lean_object* v_wsDir_2373_, lean_object* v_relPkgsDir_2374_, lean_object* v_relParentDir_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
uint8_t v_inherited_boxed_2378_; lean_object* v_res_2379_; 
v_inherited_boxed_2378_ = lean_unbox(v_inherited_2371_);
v_res_2379_ = l_Lake_Dependency_materialize(v_dep_2370_, v_inherited_boxed_2378_, v_lakeEnv_2372_, v_wsDir_2373_, v_relPkgsDir_2374_, v_relParentDir_2375_, v_a_2376_);
lean_dec_ref(v_a_2376_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2385_, lean_object* v_wsDir_2386_, lean_object* v_relPkgDir_2387_, lean_object* v_remoteUrl_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___y_2392_; lean_object* v_a_2393_; lean_object* v_pkgDir_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___f_2399_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v_val_2405_; lean_object* v_a_2435_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_val_2475_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
lean_inc_ref(v_relPkgDir_2387_);
v_pkgDir_2396_ = l_Lake_joinRelative(v_wsDir_2386_, v_relPkgDir_2387_);
v___x_2397_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1, &l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once, _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
lean_inc_ref(v_pkgDir_2396_);
v___x_2398_ = l_Lake_resolvePath(v_pkgDir_2396_);
v___f_2399_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2));
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2503_ = lean_string_utf8_byte_size(v___x_2398_);
v___x_2504_ = lean_nat_dec_eq(v___x_2503_, v___x_2472_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2398_);
v_val_2475_ = v___x_2505_;
goto v___jp_2474_;
}
else
{
lean_object* v___x_2506_; 
lean_dec_ref(v___x_2398_);
v___x_2506_ = lean_box(0);
v_val_2475_ = v___x_2506_;
goto v___jp_2474_;
}
v___jp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2392_);
lean_ctor_set(v___x_2394_, 1, v_relPkgDir_2387_);
lean_ctor_set(v___x_2394_, 2, v_remoteUrl_2388_);
lean_ctor_set(v___x_2394_, 3, v_a_2393_);
lean_ctor_set(v___x_2394_, 4, v_manifestEntry_2385_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
return v___x_2395_;
}
v___jp_2400_:
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = lean_array_get_size(v___y_2403_);
v___x_2407_ = lean_nat_dec_lt(v___y_2402_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec_ref(v___y_2401_);
v___y_2392_ = v___y_2404_;
v_a_2393_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_nat_dec_le(v___x_2406_, v___x_2406_);
if (v___x_2409_ == 0)
{
if (v___x_2407_ == 0)
{
lean_dec_ref(v___y_2401_);
v___y_2392_ = v___y_2404_;
v_a_2393_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2400__overap_2412_; lean_object* v___x_2413_; 
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = lean_usize_of_nat(v___x_2406_);
lean_inc_ref(v___y_2403_);
v___x_2400__overap_2412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2401_, v___f_2399_, v___y_2403_, v___x_2410_, v___x_2411_, v___x_2408_);
lean_inc_ref(v_a_2389_);
v___x_2413_ = lean_apply_2(v___x_2400__overap_2412_, v_a_2389_, lean_box(0));
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_dec_ref(v___x_2413_);
v___y_2392_ = v___y_2404_;
v_a_2393_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_val_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_remoteUrl_2388_);
lean_dec_ref(v_relPkgDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2410__overap_2424_; lean_object* v___x_2425_; 
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2406_);
lean_inc_ref(v___y_2403_);
v___x_2410__overap_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2401_, v___f_2399_, v___y_2403_, v___x_2422_, v___x_2423_, v___x_2408_);
lean_inc_ref(v_a_2389_);
v___x_2425_ = lean_apply_2(v___x_2410__overap_2424_, v_a_2389_, lean_box(0));
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_dec_ref(v___x_2425_);
v___y_2392_ = v___y_2404_;
v_a_2393_ = v_val_2405_;
goto v___jp_2391_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v_val_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_remoteUrl_2388_);
lean_dec_ref(v_relPkgDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
}
v___jp_2434_:
{
if (lean_obj_tag(v_a_2435_) == 1)
{
lean_object* v_manifestFile_x3f_2436_; 
lean_dec_ref(v_pkgDir_2396_);
v_manifestFile_x3f_2436_ = lean_ctor_get(v_manifestEntry_2385_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2436_) == 1)
{
lean_object* v_val_2437_; lean_object* v_val_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_val_2437_ = lean_ctor_get(v_a_2435_, 0);
lean_inc_n(v_val_2437_, 2);
lean_dec_ref(v_a_2435_);
v_val_2438_ = lean_ctor_get(v_manifestFile_x3f_2436_, 0);
lean_inc(v_val_2438_);
v___x_2439_ = l_Lake_joinRelative(v_val_2437_, v_val_2438_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2442_ = l_Lake_Manifest_load(v___x_2439_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 1);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
v___y_2401_ = v___x_2397_;
v___y_2402_ = v___x_2440_;
v___y_2403_ = v___x_2441_;
v___y_2404_ = v_val_2437_;
v_val_2405_ = v___x_2448_;
goto v___jp_2400_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2451_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2442_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2442_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 0);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
v___y_2401_ = v___x_2397_;
v___y_2402_ = v___x_2440_;
v___y_2403_ = v___x_2441_;
v___y_2404_ = v_val_2437_;
v_val_2405_ = v___x_2456_;
goto v___jp_2400_;
}
}
}
}
else
{
lean_object* v_val_2459_; lean_object* v___x_2460_; 
v_val_2459_ = lean_ctor_get(v_a_2435_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v_a_2435_);
v___x_2460_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2392_ = v_val_2459_;
v_a_2393_ = v___x_2460_;
goto v___jp_2391_;
}
}
else
{
lean_object* v_name_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec(v_a_2435_);
lean_dec_ref(v_remoteUrl_2388_);
lean_dec_ref(v_relPkgDir_2387_);
v_name_2461_ = lean_ctor_get(v_manifestEntry_2385_, 0);
lean_inc(v_name_2461_);
lean_dec_ref(v_manifestEntry_2385_);
v___x_2462_ = 0;
v___x_2463_ = l_Lean_Name_toString(v_name_2461_, v___x_2462_);
v___x_2464_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2465_ = lean_string_append(v___x_2463_, v___x_2464_);
v___x_2466_ = lean_string_append(v___x_2465_, v_pkgDir_2396_);
lean_dec_ref(v_pkgDir_2396_);
v___x_2467_ = 3;
v___x_2468_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*1, v___x_2467_);
lean_inc_ref(v_a_2389_);
v___x_2469_ = lean_apply_2(v_a_2389_, v___x_2468_, lean_box(0));
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
}
v___jp_2474_:
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2476_ == 0)
{
v_a_2435_ = v_val_2475_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2478_ == 0)
{
if (v___x_2476_ == 0)
{
v_a_2435_ = v_val_2475_;
goto v___jp_2434_;
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2466__overap_2481_; lean_object* v___x_2482_; 
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2466__overap_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2397_, v___f_2399_, v___x_2473_, v___x_2479_, v___x_2480_, v___x_2477_);
lean_inc_ref(v_a_2389_);
v___x_2482_ = lean_apply_2(v___x_2466__overap_2481_, v_a_2389_, lean_box(0));
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_dec_ref(v___x_2482_);
v_a_2435_ = v_val_2475_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_val_2475_);
lean_dec_ref(v_pkgDir_2396_);
lean_dec_ref(v_remoteUrl_2388_);
lean_dec_ref(v_relPkgDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
else
{
size_t v___x_2491_; size_t v___x_2492_; lean_object* v___x_2476__overap_2493_; lean_object* v___x_2494_; 
v___x_2491_ = ((size_t)0ULL);
v___x_2492_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2476__overap_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2397_, v___f_2399_, v___x_2473_, v___x_2491_, v___x_2492_, v___x_2477_);
lean_inc_ref(v_a_2389_);
v___x_2494_ = lean_apply_2(v___x_2476__overap_2493_, v_a_2389_, lean_box(0));
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_dec_ref(v___x_2494_);
v_a_2435_ = v_val_2475_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_val_2475_);
lean_dec_ref(v_pkgDir_2396_);
lean_dec_ref(v_remoteUrl_2388_);
lean_dec_ref(v_relPkgDir_2387_);
lean_dec_ref(v_manifestEntry_2385_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2507_, lean_object* v_wsDir_2508_, lean_object* v_relPkgDir_2509_, lean_object* v_remoteUrl_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2507_, v_wsDir_2508_, v_relPkgDir_2509_, v_remoteUrl_2510_, v_a_2511_);
lean_dec_ref(v_a_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2515_, lean_object* v_lakeEnv_2516_, lean_object* v_wsDir_2517_, lean_object* v_relPkgsDir_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v_a_2525_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v_val_2535_; lean_object* v_src_2562_; 
v_src_2562_ = lean_ctor_get(v_manifestEntry_2515_, 4);
lean_inc_ref(v_src_2562_);
if (lean_obj_tag(v_src_2562_) == 0)
{
lean_object* v_name_2563_; lean_object* v_manifestFile_x3f_2564_; lean_object* v_dir_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v_relPkgsDir_2518_);
v_name_2563_ = lean_ctor_get(v_manifestEntry_2515_, 0);
v_manifestFile_x3f_2564_ = lean_ctor_get(v_manifestEntry_2515_, 3);
v_dir_2565_ = lean_ctor_get(v_src_2562_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_src_2562_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2567_ = v_src_2562_;
v_isShared_2568_ = v_isSharedCheck_2679_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_dir_2565_);
lean_dec(v_src_2562_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2679_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_pkgDir_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___y_2573_; lean_object* v_a_2574_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v_val_2583_; lean_object* v_a_2611_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_val_2649_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
lean_inc_ref(v_dir_2565_);
v_pkgDir_2569_ = l_Lake_joinRelative(v_wsDir_2517_, v_dir_2565_);
lean_inc_ref(v_pkgDir_2569_);
v___x_2570_ = l_Lake_resolvePath(v_pkgDir_2569_);
v___x_2571_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_2646_ = lean_unsigned_to_nat(0u);
v___x_2647_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2675_ = lean_string_utf8_byte_size(v___x_2570_);
v___x_2676_ = lean_nat_dec_eq(v___x_2675_, v___x_2646_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2570_);
v_val_2649_ = v___x_2677_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2678_; 
lean_dec_ref(v___x_2570_);
v___x_2678_ = lean_box(0);
v_val_2649_ = v___x_2678_;
goto v___jp_2648_;
}
v___jp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2575_, 0, v___y_2573_);
lean_ctor_set(v___x_2575_, 1, v_dir_2565_);
lean_ctor_set(v___x_2575_, 2, v___x_2571_);
lean_ctor_set(v___x_2575_, 3, v_a_2574_);
lean_ctor_set(v___x_2575_, 4, v_manifestEntry_2515_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2575_);
v___x_2577_ = v___x_2567_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
v___jp_2579_:
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = lean_array_get_size(v___y_2581_);
v___x_2585_ = lean_nat_dec_lt(v___y_2580_, v___x_2584_);
if (v___x_2585_ == 0)
{
v___y_2573_ = v___y_2582_;
v_a_2574_ = v_val_2583_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_nat_dec_le(v___x_2584_, v___x_2584_);
if (v___x_2587_ == 0)
{
if (v___x_2585_ == 0)
{
v___y_2573_ = v___y_2582_;
v_a_2574_ = v_val_2583_;
goto v___jp_2572_;
}
else
{
size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = ((size_t)0ULL);
v___x_2589_ = lean_usize_of_nat(v___x_2584_);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2581_, v___x_2588_, v___x_2589_, v___x_2586_, v_a_2519_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_dec_ref(v___x_2590_);
v___y_2573_ = v___y_2582_;
v_a_2574_ = v_val_2583_;
goto v___jp_2572_;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_val_2583_);
lean_dec_ref(v___y_2582_);
lean_del_object(v___x_2567_);
lean_dec_ref(v_dir_2565_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = lean_usize_of_nat(v___x_2584_);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2581_, v___x_2599_, v___x_2600_, v___x_2586_, v_a_2519_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec_ref(v___x_2601_);
v___y_2573_ = v___y_2582_;
v_a_2574_ = v_val_2583_;
goto v___jp_2572_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref(v_val_2583_);
lean_dec_ref(v___y_2582_);
lean_del_object(v___x_2567_);
lean_dec_ref(v_dir_2565_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
}
v___jp_2610_:
{
if (lean_obj_tag(v_a_2611_) == 1)
{
lean_dec_ref(v_pkgDir_2569_);
if (lean_obj_tag(v_manifestFile_x3f_2564_) == 1)
{
lean_object* v_val_2612_; lean_object* v_val_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_val_2612_ = lean_ctor_get(v_a_2611_, 0);
lean_inc_n(v_val_2612_, 2);
lean_dec_ref(v_a_2611_);
v_val_2613_ = lean_ctor_get(v_manifestFile_x3f_2564_, 0);
lean_inc(v_val_2613_);
v___x_2614_ = l_Lake_joinRelative(v_val_2612_, v_val_2613_);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2617_ = l_Lake_Manifest_load(v___x_2614_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 1);
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
v___y_2580_ = v___x_2615_;
v___y_2581_ = v___x_2616_;
v___y_2582_ = v_val_2612_;
v_val_2583_ = v___x_2623_;
goto v___jp_2579_;
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
v_a_2626_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2617_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2617_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 0);
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
v___y_2580_ = v___x_2615_;
v___y_2581_ = v___x_2616_;
v___y_2582_ = v_val_2612_;
v_val_2583_ = v___x_2631_;
goto v___jp_2579_;
}
}
}
}
else
{
lean_object* v_val_2634_; lean_object* v___x_2635_; 
v_val_2634_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_val_2634_);
lean_dec_ref(v_a_2611_);
v___x_2635_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2573_ = v_val_2634_;
v_a_2574_ = v___x_2635_;
goto v___jp_2572_;
}
}
else
{
uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_inc(v_name_2563_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2567_);
lean_dec_ref(v_dir_2565_);
lean_dec_ref(v_manifestEntry_2515_);
v___x_2636_ = 0;
v___x_2637_ = l_Lean_Name_toString(v_name_2563_, v___x_2636_);
v___x_2638_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2639_ = lean_string_append(v___x_2637_, v___x_2638_);
v___x_2640_ = lean_string_append(v___x_2639_, v_pkgDir_2569_);
lean_dec_ref(v_pkgDir_2569_);
v___x_2641_ = 3;
v___x_2642_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*1, v___x_2641_);
lean_inc_ref(v_a_2519_);
v___x_2643_ = lean_apply_2(v_a_2519_, v___x_2642_, lean_box(0));
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
}
v___jp_2648_:
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2650_ == 0)
{
v_a_2611_ = v_val_2649_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2652_ == 0)
{
if (v___x_2650_ == 0)
{
v_a_2611_ = v_val_2649_;
goto v___jp_2610_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2647_, v___x_2653_, v___x_2654_, v___x_2651_, v_a_2519_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_dec_ref(v___x_2655_);
v_a_2611_ = v_val_2649_;
goto v___jp_2610_;
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_val_2649_);
lean_dec_ref(v_pkgDir_2569_);
lean_del_object(v___x_2567_);
lean_dec_ref(v_dir_2565_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
else
{
size_t v___x_2664_; size_t v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = ((size_t)0ULL);
v___x_2665_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2647_, v___x_2664_, v___x_2665_, v___x_2651_, v_a_2519_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_dec_ref(v___x_2666_);
v_a_2611_ = v_val_2649_;
goto v___jp_2610_;
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_val_2649_);
lean_dec_ref(v_pkgDir_2569_);
lean_del_object(v___x_2567_);
lean_dec_ref(v_dir_2565_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
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
lean_object* v_name_2680_; lean_object* v_manifestFile_x3f_2681_; lean_object* v_url_2682_; lean_object* v_rev_2683_; lean_object* v_subDir_x3f_2684_; uint8_t v___x_2685_; lean_object* v_sname_2686_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v_a_2692_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v_val_2732_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v_relGitDir_2777_; lean_object* v___y_2779_; lean_object* v_gitDir_2782_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2796_; uint8_t v_a_2808_; lean_object* v___y_2818_; lean_object* v___y_2819_; uint8_t v_val_2820_; uint8_t v___y_2848_; lean_object* v_a_2849_; uint8_t v___x_2859_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v_name_2680_ = lean_ctor_get(v_manifestEntry_2515_, 0);
v_manifestFile_x3f_2681_ = lean_ctor_get(v_manifestEntry_2515_, 3);
v_url_2682_ = lean_ctor_get(v_src_2562_, 0);
lean_inc_ref(v_url_2682_);
v_rev_2683_ = lean_ctor_get(v_src_2562_, 1);
lean_inc_ref(v_rev_2683_);
v_subDir_x3f_2684_ = lean_ctor_get(v_src_2562_, 3);
lean_inc(v_subDir_x3f_2684_);
lean_dec_ref(v_src_2562_);
v___x_2685_ = 0;
lean_inc(v_name_2680_);
v_sname_2686_ = l_Lean_Name_toString(v_name_2680_, v___x_2685_);
lean_inc_ref(v_sname_2686_);
v_relGitDir_2777_ = l_Lake_joinRelative(v_relPkgsDir_2518_, v_sname_2686_);
lean_inc_ref(v_relGitDir_2777_);
lean_inc_ref(v_wsDir_2517_);
v_gitDir_2782_ = l_Lake_joinRelative(v_wsDir_2517_, v_relGitDir_2777_);
v___x_2859_ = l_System_FilePath_isDir(v_gitDir_2782_);
v___x_2892_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2893_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2893_ == 0)
{
goto v___jp_2860_;
}
else
{
lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = lean_box(0);
v___x_2895_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2895_ == 0)
{
if (v___x_2893_ == 0)
{
goto v___jp_2860_;
}
else
{
size_t v___x_2896_; size_t v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = ((size_t)0ULL);
v___x_2897_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2892_, v___x_2896_, v___x_2897_, v___x_2894_, v_a_2519_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_dec_ref(v___x_2898_);
goto v___jp_2860_;
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v_gitDir_2782_);
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_rev_2683_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
else
{
size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2892_, v___x_2907_, v___x_2908_, v___x_2894_, v_a_2519_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_dec_ref(v___x_2909_);
goto v___jp_2860_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v_gitDir_2782_);
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_rev_2683_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
v___jp_2687_:
{
if (lean_obj_tag(v_a_2692_) == 1)
{
lean_dec_ref(v___y_2689_);
lean_dec_ref(v_sname_2686_);
if (lean_obj_tag(v_manifestFile_x3f_2681_) == 1)
{
lean_object* v_val_2693_; lean_object* v_val_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_val_2693_ = lean_ctor_get(v_a_2692_, 0);
lean_inc_n(v_val_2693_, 2);
lean_dec_ref(v_a_2692_);
v_val_2694_ = lean_ctor_get(v_manifestFile_x3f_2681_, 0);
lean_inc(v_val_2694_);
v___x_2695_ = l_Lake_joinRelative(v_val_2693_, v_val_2694_);
v___x_2696_ = lean_unsigned_to_nat(0u);
v___x_2697_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2698_ = l_Lake_Manifest_load(v___x_2695_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set_tag(v___x_2701_, 1);
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
v___y_2529_ = v___y_2688_;
v___y_2530_ = v___y_2690_;
v___y_2531_ = v___y_2691_;
v___y_2532_ = v___x_2696_;
v___y_2533_ = v___x_2697_;
v___y_2534_ = v_val_2693_;
v_val_2535_ = v___x_2704_;
goto v___jp_2528_;
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_a_2707_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2698_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2698_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 0);
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
v___y_2529_ = v___y_2688_;
v___y_2530_ = v___y_2690_;
v___y_2531_ = v___y_2691_;
v___y_2532_ = v___x_2696_;
v___y_2533_ = v___x_2697_;
v___y_2534_ = v_val_2693_;
v_val_2535_ = v___x_2712_;
goto v___jp_2528_;
}
}
}
}
else
{
lean_object* v_val_2715_; lean_object* v___x_2716_; 
v_val_2715_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_val_2715_);
lean_dec_ref(v_a_2692_);
v___x_2716_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2522_ = v___y_2688_;
v___y_2523_ = v___y_2691_;
v___y_2524_ = v_val_2715_;
v_a_2525_ = v___x_2716_;
goto v___jp_2521_;
}
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
lean_dec(v_a_2692_);
lean_dec_ref(v___y_2691_);
lean_dec_ref(v___y_2688_);
lean_dec_ref(v_manifestEntry_2515_);
v___x_2717_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3));
v___x_2718_ = lean_string_append(v_sname_2686_, v___x_2717_);
v___x_2719_ = lean_string_append(v___x_2718_, v___y_2689_);
lean_dec_ref(v___y_2689_);
v___x_2720_ = 3;
v___x_2721_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*1, v___x_2720_);
lean_inc_ref(v___y_2690_);
v___x_2722_ = lean_apply_2(v___y_2690_, v___x_2721_, lean_box(0));
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
v___jp_2725_:
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = lean_array_get_size(v___y_2727_);
v___x_2734_ = lean_nat_dec_lt(v___y_2731_, v___x_2733_);
if (v___x_2734_ == 0)
{
v___y_2688_ = v___y_2726_;
v___y_2689_ = v___y_2730_;
v___y_2690_ = v___y_2729_;
v___y_2691_ = v___y_2728_;
v_a_2692_ = v_val_2732_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_nat_dec_le(v___x_2733_, v___x_2733_);
if (v___x_2736_ == 0)
{
if (v___x_2734_ == 0)
{
v___y_2688_ = v___y_2726_;
v___y_2689_ = v___y_2730_;
v___y_2690_ = v___y_2729_;
v___y_2691_ = v___y_2728_;
v_a_2692_ = v_val_2732_;
goto v___jp_2687_;
}
else
{
size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = ((size_t)0ULL);
v___x_2738_ = lean_usize_of_nat(v___x_2733_);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2727_, v___x_2737_, v___x_2738_, v___x_2735_, v___y_2729_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_dec_ref(v___x_2739_);
v___y_2688_ = v___y_2726_;
v___y_2689_ = v___y_2730_;
v___y_2690_ = v___y_2729_;
v___y_2691_ = v___y_2728_;
v_a_2692_ = v_val_2732_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_val_2732_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v___y_2728_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v_sname_2686_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
else
{
size_t v___x_2748_; size_t v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = ((size_t)0ULL);
v___x_2749_ = lean_usize_of_nat(v___x_2733_);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2727_, v___x_2748_, v___x_2749_, v___x_2735_, v___y_2729_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_dec_ref(v___x_2750_);
v___y_2688_ = v___y_2726_;
v___y_2689_ = v___y_2730_;
v___y_2690_ = v___y_2729_;
v___y_2691_ = v___y_2728_;
v_a_2692_ = v_val_2732_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_val_2732_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v___y_2728_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v_sname_2686_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
}
v___jp_2759_:
{
lean_object* v_pkgDir_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
lean_inc_ref(v___y_2760_);
v_pkgDir_2763_ = l_Lake_joinRelative(v_wsDir_2517_, v___y_2760_);
lean_inc_ref(v_pkgDir_2763_);
v___x_2764_ = l_Lake_resolvePath(v_pkgDir_2763_);
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2767_ = lean_string_utf8_byte_size(v___x_2764_);
v___x_2768_ = lean_nat_dec_eq(v___x_2767_, v___x_2765_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2764_);
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___x_2766_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2761_;
v___y_2730_ = v_pkgDir_2763_;
v___y_2731_ = v___x_2765_;
v_val_2732_ = v___x_2769_;
goto v___jp_2725_;
}
else
{
lean_object* v___x_2770_; 
lean_dec_ref(v___x_2764_);
v___x_2770_ = lean_box(0);
v___y_2726_ = v___y_2760_;
v___y_2727_ = v___x_2766_;
v___y_2728_ = v___y_2762_;
v___y_2729_ = v___y_2761_;
v___y_2730_ = v_pkgDir_2763_;
v___y_2731_ = v___x_2765_;
v_val_2732_ = v___x_2770_;
goto v___jp_2725_;
}
}
v___jp_2771_:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lake_Git_filterUrl_x3f(v_url_2682_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2775_; 
v___x_2775_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2760_ = v___y_2773_;
v___y_2761_ = v___y_2772_;
v___y_2762_ = v___x_2775_;
goto v___jp_2759_;
}
else
{
lean_object* v_val_2776_; 
v_val_2776_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_val_2776_);
lean_dec_ref(v___x_2774_);
v___y_2760_ = v___y_2773_;
v___y_2761_ = v___y_2772_;
v___y_2762_ = v_val_2776_;
goto v___jp_2759_;
}
}
v___jp_2778_:
{
if (lean_obj_tag(v_subDir_x3f_2684_) == 0)
{
v___y_2772_ = v___y_2779_;
v___y_2773_ = v_relGitDir_2777_;
goto v___jp_2771_;
}
else
{
lean_object* v_val_2780_; lean_object* v___x_2781_; 
v_val_2780_ = lean_ctor_get(v_subDir_x3f_2684_, 0);
lean_inc(v_val_2780_);
lean_dec_ref(v_subDir_x3f_2684_);
v___x_2781_ = l_Lake_joinRelative(v_relGitDir_2777_, v_val_2780_);
v___y_2772_ = v___y_2779_;
v___y_2773_ = v___x_2781_;
goto v___jp_2771_;
}
}
v___jp_2783_:
{
lean_object* v___x_2786_; 
lean_inc_ref(v_sname_2686_);
v___x_2786_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2519_, v_sname_2686_, v_gitDir_2782_, v___y_2785_, v___y_2784_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2779_ = v_a_2519_;
goto v___jp_2778_;
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
v___jp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_rev_2683_);
lean_inc_ref(v_sname_2686_);
v___x_2798_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_2519_, v_sname_2686_, v_gitDir_2782_, v___y_2796_, v___x_2797_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_dec_ref(v___x_2798_);
v___y_2779_ = v_a_2519_;
goto v___jp_2778_;
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
v___jp_2807_:
{
if (v_a_2808_ == 0)
{
lean_dec_ref(v_gitDir_2782_);
v___y_2779_ = v_a_2519_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2809_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0));
lean_inc_ref(v_sname_2686_);
v___x_2810_ = lean_string_append(v_sname_2686_, v___x_2809_);
v___x_2811_ = lean_string_append(v___x_2810_, v_gitDir_2782_);
lean_dec_ref(v_gitDir_2782_);
v___x_2812_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1));
v___x_2813_ = lean_string_append(v___x_2811_, v___x_2812_);
v___x_2814_ = 2;
v___x_2815_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*1, v___x_2814_);
lean_inc_ref(v_a_2519_);
v___x_2816_ = lean_apply_2(v_a_2519_, v___x_2815_, lean_box(0));
v___y_2779_ = v_a_2519_;
goto v___jp_2778_;
}
}
v___jp_2817_:
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = lean_array_get_size(v___y_2818_);
v___x_2822_ = lean_nat_dec_lt(v___y_2819_, v___x_2821_);
if (v___x_2822_ == 0)
{
v_a_2808_ = v_val_2820_;
goto v___jp_2807_;
}
else
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_nat_dec_le(v___x_2821_, v___x_2821_);
if (v___x_2824_ == 0)
{
if (v___x_2822_ == 0)
{
v_a_2808_ = v_val_2820_;
goto v___jp_2807_;
}
else
{
size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = lean_usize_of_nat(v___x_2821_);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2818_, v___x_2825_, v___x_2826_, v___x_2823_, v_a_2519_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_dec_ref(v___x_2827_);
v_a_2808_ = v_val_2820_;
goto v___jp_2807_;
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v_gitDir_2782_);
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
else
{
size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = lean_usize_of_nat(v___x_2821_);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2818_, v___x_2836_, v___x_2837_, v___x_2823_, v_a_2519_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_dec_ref(v___x_2838_);
v_a_2808_ = v_val_2820_;
goto v___jp_2807_;
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref(v_gitDir_2782_);
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
}
v___jp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_rev_2683_);
lean_inc_ref(v___x_2851_);
v___x_2852_ = l_Option_instDecidableEq___redArg(v___x_2850_, v_a_2849_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v_pkgUrlMap_2853_; lean_object* v___x_2854_; 
v_pkgUrlMap_2853_ = lean_ctor_get(v_lakeEnv_2516_, 5);
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2853_, v_name_2680_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_inc_ref(v_url_2682_);
v___y_2784_ = v___x_2851_;
v___y_2785_ = v_url_2682_;
goto v___jp_2783_;
}
else
{
lean_object* v_val_2855_; 
v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_val_2855_);
lean_dec_ref(v___x_2854_);
v___y_2784_ = v___x_2851_;
v___y_2785_ = v_val_2855_;
goto v___jp_2783_;
}
}
else
{
uint8_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec_ref(v___x_2851_);
lean_inc_ref(v_gitDir_2782_);
v___x_2856_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_2782_);
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
if (v___x_2856_ == 0)
{
v___y_2818_ = v___x_2858_;
v___y_2819_ = v___x_2857_;
v_val_2820_ = v___y_2848_;
goto v___jp_2817_;
}
else
{
v___y_2818_ = v___x_2858_;
v___y_2819_ = v___x_2857_;
v_val_2820_ = v___x_2685_;
goto v___jp_2817_;
}
}
}
v___jp_2860_:
{
if (v___x_2859_ == 0)
{
lean_object* v_pkgUrlMap_2861_; lean_object* v___x_2862_; 
v_pkgUrlMap_2861_ = lean_ctor_get(v_lakeEnv_2516_, 5);
v___x_2862_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2861_, v_name_2680_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_inc_ref(v_url_2682_);
v___y_2796_ = v_url_2682_;
goto v___jp_2795_;
}
else
{
lean_object* v_val_2863_; 
v_val_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_val_2863_);
lean_dec_ref(v___x_2862_);
v___y_2796_ = v_val_2863_;
goto v___jp_2795_;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2864_ = ((lean_object*)(l_Lake_PackageEntry_materialize___closed__0));
lean_inc_ref(v_gitDir_2782_);
v___x_2865_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2864_, v_gitDir_2782_);
v___x_2866_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2));
v___x_2867_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
if (v___x_2867_ == 0)
{
v___y_2848_ = v___x_2859_;
v_a_2849_ = v___x_2865_;
goto v___jp_2847_;
}
else
{
lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2868_ = lean_box(0);
v___x_2869_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
if (v___x_2869_ == 0)
{
if (v___x_2867_ == 0)
{
v___y_2848_ = v___x_2859_;
v_a_2849_ = v___x_2865_;
goto v___jp_2847_;
}
else
{
size_t v___x_2870_; size_t v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = ((size_t)0ULL);
v___x_2871_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2866_, v___x_2870_, v___x_2871_, v___x_2868_, v_a_2519_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_dec_ref(v___x_2872_);
v___y_2848_ = v___x_2859_;
v_a_2849_ = v___x_2865_;
goto v___jp_2847_;
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v___x_2865_);
lean_dec_ref(v_gitDir_2782_);
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_rev_2683_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
size_t v___x_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = ((size_t)0ULL);
v___x_2882_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7, &l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_2866_, v___x_2881_, v___x_2882_, v___x_2868_, v_a_2519_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_dec_ref(v___x_2883_);
v___y_2848_ = v___x_2859_;
v_a_2849_ = v___x_2865_;
goto v___jp_2847_;
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v___x_2865_);
lean_dec_ref(v_gitDir_2782_);
lean_dec_ref(v_relGitDir_2777_);
lean_dec_ref(v_sname_2686_);
lean_dec(v_subDir_x3f_2684_);
lean_dec_ref(v_rev_2683_);
lean_dec_ref(v_url_2682_);
lean_dec_ref(v_wsDir_2517_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2883_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
}
}
}
v___jp_2521_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2526_, 0, v___y_2524_);
lean_ctor_set(v___x_2526_, 1, v___y_2522_);
lean_ctor_set(v___x_2526_, 2, v___y_2523_);
lean_ctor_set(v___x_2526_, 3, v_a_2525_);
lean_ctor_set(v___x_2526_, 4, v_manifestEntry_2515_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
v___jp_2528_:
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = lean_array_get_size(v___y_2533_);
v___x_2537_ = lean_nat_dec_lt(v___y_2532_, v___x_2536_);
if (v___x_2537_ == 0)
{
v___y_2522_ = v___y_2529_;
v___y_2523_ = v___y_2531_;
v___y_2524_ = v___y_2534_;
v_a_2525_ = v_val_2535_;
goto v___jp_2521_;
}
else
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_nat_dec_le(v___x_2536_, v___x_2536_);
if (v___x_2539_ == 0)
{
if (v___x_2537_ == 0)
{
v___y_2522_ = v___y_2529_;
v___y_2523_ = v___y_2531_;
v___y_2524_ = v___y_2534_;
v_a_2525_ = v_val_2535_;
goto v___jp_2521_;
}
else
{
size_t v___x_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = ((size_t)0ULL);
v___x_2541_ = lean_usize_of_nat(v___x_2536_);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2533_, v___x_2540_, v___x_2541_, v___x_2538_, v___y_2530_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_dec_ref(v___x_2542_);
v___y_2522_ = v___y_2529_;
v___y_2523_ = v___y_2531_;
v___y_2524_ = v___y_2534_;
v_a_2525_ = v_val_2535_;
goto v___jp_2521_;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_val_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
else
{
size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = lean_usize_of_nat(v___x_2536_);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2533_, v___x_2551_, v___x_2552_, v___x_2538_, v___y_2530_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_dec_ref(v___x_2553_);
v___y_2522_ = v___y_2529_;
v___y_2523_ = v___y_2531_;
v___y_2524_ = v___y_2534_;
v_a_2525_ = v_val_2535_;
goto v___jp_2521_;
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_val_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v_manifestEntry_2515_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_2918_, lean_object* v_lakeEnv_2919_, lean_object* v_wsDir_2920_, lean_object* v_relPkgsDir_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lake_PackageEntry_materialize(v_manifestEntry_2918_, v_lakeEnv_2919_, v_wsDir_2920_, v_relPkgsDir_2921_, v_a_2922_);
lean_dec_ref(v_a_2922_);
lean_dec_ref(v_lakeEnv_2919_);
return v_res_2924_;
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
