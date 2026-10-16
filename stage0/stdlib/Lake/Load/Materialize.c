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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_gcAuto(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_pruneRemote(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_addRemote(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRev_isFullSha1(lean_object*);
lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
extern lean_object* l_Lake_Git_upstreamBranch;
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_removeDirAllIfExists(lean_object*);
lean_object* l_Lake_copyDirAll(lean_object*, lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": failed to resolve path:\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0_value;
static const lean_closure_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3;
static const lean_array_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4_value;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6;
static lean_once_cell_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = ": repository has local changes:\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": checking out revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ": failed to fetch the package revision\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nfrom the Git repository at\n  "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ": fetching revision '"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' from "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": remote URL changed\n  old: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  new: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = ": materializing new dependency"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7_value;
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ": package directory not found: "};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Dependency_materialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = ": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir"};
static const lean_object* l_Lake_Dependency_materialize___closed__8 = (const lean_object*)&l_Lake_Dependency_materialize___closed__8_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedMaterializedDep_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value)}};
static const lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1 = (const lean_object*)&l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc_ref(v___y_3_);
v___x_5_ = lean_apply_2(v___y_3_, v___y_2_, lean_box(0));
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0___boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___lam__0(v_x_7_, v___y_8_, v___y_9_);
lean_dec_ref(v___y_9_);
return v_res_11_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_instMonadEIO___redArg();
return v___x_14_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__2);
v___x_16_ = l_ReaderT_instMonad___redArg(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_20_ = lean_array_get_size(v___x_19_);
return v___x_20_;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_21_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_nat_dec_lt(v___x_22_, v___x_21_);
return v___x_23_;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7(void){
_start:
{
lean_object* v___x_24_; size_t v___x_25_; 
v___x_24_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__5);
v___x_25_ = lean_usize_of_nat(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(lean_object* v_name_26_, lean_object* v_url_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_a_31_; lean_object* v___f_48_; lean_object* v___y_50_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v_val_53_; uint8_t v_a_70_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; uint8_t v___x_83_; 
v___f_48_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
v___x_80_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_81_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_82_ = l_System_FilePath_pathExists(v_url_27_);
v___x_83_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_83_ == 0)
{
v_a_70_ = v___x_82_;
goto v___jp_69_;
}
else
{
lean_object* v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v___x_1286__overap_87_; lean_object* v___x_88_; 
v___x_84_ = lean_box(0);
v___x_85_ = ((size_t)0ULL);
v___x_86_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1286__overap_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_80_, v___f_48_, v___x_81_, v___x_85_, v___x_86_, v___x_84_);
lean_inc_ref(v_a_28_);
v___x_88_ = lean_apply_2(v___x_1286__overap_87_, v_a_28_, lean_box(0));
if (lean_obj_tag(v___x_88_) == 0)
{
lean_dec_ref_known(v___x_88_, 1);
v_a_70_ = v___x_82_;
goto v___jp_69_;
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec_ref(v_url_27_);
lean_dec_ref(v_name_26_);
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
v___jp_30_:
{
if (lean_obj_tag(v_a_31_) == 1)
{
lean_object* v_val_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
lean_dec_ref(v_url_27_);
lean_dec_ref(v_name_26_);
v_val_32_ = lean_ctor_get(v_a_31_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v_a_31_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v_a_31_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_val_32_);
lean_dec(v_a_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 0);
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_val_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_a_31_);
v___x_40_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_41_ = lean_string_append(v_name_26_, v___x_40_);
v___x_42_ = lean_string_append(v___x_41_, v_url_27_);
lean_dec_ref(v_url_27_);
v___x_43_ = 3;
v___x_44_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_43_);
lean_inc_ref(v_a_28_);
v___x_45_ = lean_apply_2(v_a_28_, v___x_44_, lean_box(0));
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
v___jp_49_:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_array_get_size(v___y_52_);
v___x_55_ = lean_nat_dec_lt(v___y_51_, v___x_54_);
if (v___x_55_ == 0)
{
v_a_31_ = v_val_53_;
goto v___jp_30_;
}
else
{
lean_object* v___x_56_; size_t v___x_57_; size_t v___x_58_; lean_object* v___x_1563__overap_59_; lean_object* v___x_60_; 
v___x_56_ = lean_box(0);
v___x_57_ = ((size_t)0ULL);
v___x_58_ = lean_usize_of_nat(v___x_54_);
lean_inc_ref(v___y_52_);
lean_inc_ref(v___y_50_);
v___x_1563__overap_59_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_50_, v___f_48_, v___y_52_, v___x_57_, v___x_58_, v___x_56_);
lean_inc_ref(v_a_28_);
v___x_60_ = lean_apply_2(v___x_1563__overap_59_, v_a_28_, lean_box(0));
if (lean_obj_tag(v___x_60_) == 0)
{
lean_dec_ref_known(v___x_60_, 1);
v_a_31_ = v_val_53_;
goto v___jp_30_;
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec(v_val_53_);
lean_dec_ref(v_url_27_);
lean_dec_ref(v_name_26_);
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
v___jp_69_:
{
if (v_a_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec_ref(v_name_26_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v_url_27_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_72_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_27_);
v___x_75_ = l_Lake_resolvePath(v_url_27_);
v___x_76_ = lean_string_utf8_byte_size(v___x_75_);
v___x_77_ = lean_nat_dec_eq(v___x_76_, v___x_73_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_75_);
v___y_50_ = v___x_72_;
v___y_51_ = v___x_73_;
v___y_52_ = v___x_74_;
v_val_53_ = v___x_78_;
goto v___jp_49_;
}
else
{
lean_object* v___x_79_; 
lean_dec_ref(v___x_75_);
v___x_79_ = lean_box(0);
v___y_50_ = v___x_72_;
v___y_51_ = v___x_73_;
v___y_52_ = v___x_74_;
v_val_53_ = v___x_79_;
goto v___jp_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___boxed(lean_object* v_name_97_, lean_object* v_url_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl(v_name_97_, v_url_98_, v_a_99_);
lean_dec_ref(v_a_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(lean_object* v_name_103_, lean_object* v_repo_104_, lean_object* v_a_105_){
_start:
{
uint8_t v_a_108_; lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v_val_122_; uint8_t v___x_129_; 
v___f_118_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
v___x_119_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_120_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_104_);
v___x_129_ = l_Lake_GitRepo_hasNoDiff(v_repo_104_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 1;
v_val_122_ = v___x_130_;
goto v___jp_121_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
v_val_122_ = v___x_131_;
goto v___jp_121_;
}
v___jp_107_:
{
if (v_a_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec_ref(v_repo_104_);
lean_dec_ref(v_name_103_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_111_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_112_ = lean_string_append(v_name_103_, v___x_111_);
v___x_113_ = lean_string_append(v___x_112_, v_repo_104_);
lean_dec_ref(v_repo_104_);
v___x_114_ = 2;
v___x_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_114_);
lean_inc_ref(v_a_105_);
v___x_116_ = lean_apply_2(v_a_105_, v___x_115_, lean_box(0));
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
v___jp_121_:
{
uint8_t v___x_123_; 
v___x_123_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_123_ == 0)
{
v_a_108_ = v_val_122_;
goto v___jp_107_;
}
else
{
lean_object* v___x_124_; size_t v___x_125_; size_t v___x_126_; lean_object* v___x_786__overap_127_; lean_object* v___x_128_; 
v___x_124_ = lean_box(0);
v___x_125_ = ((size_t)0ULL);
v___x_126_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_786__overap_127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_119_, v___f_118_, v___x_120_, v___x_125_, v___x_126_, v___x_124_);
lean_inc_ref(v_a_105_);
v___x_128_ = lean_apply_2(v___x_786__overap_127_, v_a_105_, lean_box(0));
if (lean_obj_tag(v___x_128_) == 0)
{
lean_dec_ref_known(v___x_128_, 1);
v_a_108_ = v_val_122_;
goto v___jp_107_;
}
else
{
lean_dec_ref(v_repo_104_);
lean_dec_ref(v_name_103_);
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___boxed(lean_object* v_name_132_, lean_object* v_repo_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff(v_name_132_, v_repo_133_, v_a_134_);
lean_dec_ref(v_a_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(lean_object* v_name_139_, lean_object* v_repo_140_, lean_object* v_rev_141_, lean_object* v_a_142_){
_start:
{
uint8_t v_a_145_; lean_object* v___f_155_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; uint8_t v_val_160_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___f_155_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
v___x_206_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_139_);
v___x_207_ = lean_string_append(v_name_139_, v___x_206_);
v___x_208_ = lean_string_append(v___x_207_, v_rev_141_);
v___x_209_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
v___x_211_ = 1;
v___x_212_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_211_);
lean_inc_ref(v_a_142_);
v___x_213_ = lean_apply_2(v_a_142_, v___x_212_, lean_box(0));
v___x_214_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_140_);
v___x_217_ = l_Lake_GitRepo_checkoutDetach(v_rev_141_, v_repo_140_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_a_218_ = lean_ctor_get(v___x_217_, 1);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 2);
v___x_219_ = lean_array_get_size(v_a_218_);
v___x_220_ = lean_nat_dec_lt(v___x_215_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec(v_a_218_);
goto v___jp_175_;
}
else
{
lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v___x_2319__overap_224_; lean_object* v___x_225_; 
v___x_221_ = lean_box(0);
v___x_222_ = ((size_t)0ULL);
v___x_223_ = lean_usize_of_nat(v___x_219_);
v___x_2319__overap_224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_214_, v___f_155_, v_a_218_, v___x_222_, v___x_223_, v___x_221_);
lean_inc_ref(v_a_142_);
v___x_225_ = lean_apply_2(v___x_2319__overap_224_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_225_) == 0)
{
lean_dec_ref_known(v___x_225_, 1);
goto v___jp_175_;
}
else
{
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
return v___x_225_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
v_a_226_ = lean_ctor_get(v___x_217_, 1);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_217_, 2);
v___x_227_ = lean_array_get_size(v_a_226_);
v___x_228_ = lean_nat_dec_lt(v___x_215_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_a_226_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; size_t v___x_232_; size_t v___x_233_; lean_object* v___x_2336__overap_234_; lean_object* v___x_235_; 
v___x_231_ = lean_box(0);
v___x_232_ = ((size_t)0ULL);
v___x_233_ = lean_usize_of_nat(v___x_227_);
v___x_2336__overap_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_214_, v___f_155_, v_a_226_, v___x_232_, v___x_233_, v___x_231_);
lean_inc_ref(v_a_142_);
v___x_235_ = lean_apply_2(v___x_2336__overap_234_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v___x_235_, 0);
lean_dec(v_unused_243_);
v___x_237_ = v___x_235_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_dec(v___x_235_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 0, v___x_231_);
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_231_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
return v___x_235_;
}
}
}
v___jp_144_:
{
if (v_a_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_148_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_149_ = lean_string_append(v_name_139_, v___x_148_);
v___x_150_ = lean_string_append(v___x_149_, v_repo_140_);
lean_dec_ref(v_repo_140_);
v___x_151_ = 2;
v___x_152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_151_);
lean_inc_ref(v_a_142_);
v___x_153_ = lean_apply_2(v_a_142_, v___x_152_, lean_box(0));
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
v___jp_156_:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_array_get_size(v___y_157_);
v___x_162_ = lean_nat_dec_lt(v___y_159_, v___x_161_);
if (v___x_162_ == 0)
{
v_a_145_ = v_val_160_;
goto v___jp_144_;
}
else
{
lean_object* v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v___x_2656__overap_166_; lean_object* v___x_167_; 
v___x_163_ = lean_box(0);
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_161_);
lean_inc_ref(v___y_157_);
lean_inc_ref(v___y_158_);
v___x_2656__overap_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_158_, v___f_155_, v___y_157_, v___x_164_, v___x_165_, v___x_163_);
lean_inc_ref(v_a_142_);
v___x_167_ = lean_apply_2(v___x_2656__overap_166_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_167_) == 0)
{
lean_dec_ref_known(v___x_167_, 1);
v_a_145_ = v_val_160_;
goto v___jp_144_;
}
else
{
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
return v___x_167_;
}
}
}
v___jp_168_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_169_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_140_);
v___x_172_ = l_Lake_GitRepo_hasNoDiff(v_repo_140_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
v___x_173_ = 1;
v___y_157_ = v___x_171_;
v___y_158_ = v___x_169_;
v___y_159_ = v___x_170_;
v_val_160_ = v___x_173_;
goto v___jp_156_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = 0;
v___y_157_ = v___x_171_;
v___y_158_ = v___x_169_;
v___y_159_ = v___x_170_;
v_val_160_ = v___x_174_;
goto v___jp_156_;
}
}
v___jp_175_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_140_);
v___x_179_ = l_Lake_GitRepo_clean(v_repo_140_, v___x_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_a_180_ = lean_ctor_get(v___x_179_, 1);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 2);
v___x_181_ = lean_array_get_size(v_a_180_);
v___x_182_ = lean_nat_dec_lt(v___x_177_, v___x_181_);
if (v___x_182_ == 0)
{
lean_dec(v_a_180_);
goto v___jp_168_;
}
else
{
lean_object* v___x_183_; size_t v___x_184_; size_t v___x_185_; lean_object* v___x_2692__overap_186_; lean_object* v___x_187_; 
v___x_183_ = lean_box(0);
v___x_184_ = ((size_t)0ULL);
v___x_185_ = lean_usize_of_nat(v___x_181_);
v___x_2692__overap_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_176_, v___f_155_, v_a_180_, v___x_184_, v___x_185_, v___x_183_);
lean_inc_ref(v_a_142_);
v___x_187_ = lean_apply_2(v___x_2692__overap_186_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_187_) == 0)
{
lean_dec_ref_known(v___x_187_, 1);
goto v___jp_168_;
}
else
{
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
return v___x_187_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
v_a_188_ = lean_ctor_get(v___x_179_, 1);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_179_, 2);
v___x_189_ = lean_array_get_size(v_a_188_);
v___x_190_ = lean_nat_dec_lt(v___x_177_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_a_188_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_2709__overap_196_; lean_object* v___x_197_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((size_t)0ULL);
v___x_195_ = lean_usize_of_nat(v___x_189_);
v___x_2709__overap_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_176_, v___f_155_, v_a_188_, v___x_194_, v___x_195_, v___x_193_);
lean_inc_ref(v_a_142_);
v___x_197_ = lean_apply_2(v___x_2709__overap_196_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v___x_197_, 0);
lean_dec(v_unused_205_);
v___x_199_ = v___x_197_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_dec(v___x_197_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 1);
lean_ctor_set(v___x_199_, 0, v___x_193_);
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_193_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___boxed(lean_object* v_name_244_, lean_object* v_repo_245_, lean_object* v_rev_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(v_name_244_, v_repo_245_, v_rev_246_, v_a_247_);
lean_dec_ref(v_a_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_as_250_, size_t v_i_251_, size_t v_stop_252_, lean_object* v_b_253_, lean_object* v___y_254_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = lean_usize_dec_eq(v_i_251_, v_stop_252_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; size_t v___x_259_; size_t v___x_260_; 
v___x_257_ = lean_array_uget_borrowed(v_as_250_, v_i_251_);
lean_inc_ref(v___y_254_);
lean_inc(v___x_257_);
v___x_258_ = lean_apply_2(v___y_254_, v___x_257_, lean_box(0));
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_add(v_i_251_, v___x_259_);
v_i_251_ = v___x_260_;
v_b_253_ = v___x_258_;
goto _start;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_b_253_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_as_263_, lean_object* v_i_264_, lean_object* v_stop_265_, lean_object* v_b_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
size_t v_i_boxed_269_; size_t v_stop_boxed_270_; lean_object* v_res_271_; 
v_i_boxed_269_ = lean_unbox_usize(v_i_264_);
lean_dec(v_i_264_);
v_stop_boxed_270_ = lean_unbox_usize(v_stop_265_);
lean_dec(v_stop_265_);
v_res_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_as_263_, v_i_boxed_269_, v_stop_boxed_270_, v_b_266_, v___y_267_);
lean_dec_ref(v___y_267_);
lean_dec_ref(v_as_263_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_281_, lean_object* v_repo_282_, lean_object* v_url_283_, lean_object* v_rev_x3f_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___y_297_; uint8_t v_a_298_; lean_object* v___y_306_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_375_; lean_object* v___y_376_; uint8_t v_a_377_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; uint8_t v_val_389_; lean_object* v___y_397_; lean_object* v___y_398_; uint8_t v___y_399_; lean_object* v___y_405_; lean_object* v___y_406_; uint8_t v___y_407_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; uint8_t v_val_439_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v_a_451_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v_a_498_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_593_; uint8_t v_a_594_; lean_object* v___y_602_; uint8_t v_a_603_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; uint8_t v_val_614_; lean_object* v___y_622_; uint8_t v___y_623_; uint8_t v___y_624_; lean_object* v___y_629_; uint8_t v___y_630_; uint8_t v___y_631_; lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v_a_666_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; uint8_t v_val_713_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v_a_725_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v_a_758_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v_a_834_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v_a_898_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v_a_911_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v_val_926_; lean_object* v___y_934_; lean_object* v___y_935_; uint8_t v_a_936_; lean_object* v___y_945_; 
if (lean_obj_tag(v_rev_x3f_284_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = l_Lake_Git_upstreamBranch;
v___y_945_ = v___x_954_;
goto v___jp_944_;
}
else
{
lean_object* v_val_955_; 
v_val_955_ = lean_ctor_get(v_rev_x3f_284_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v_rev_x3f_284_, 1);
v___y_945_ = v_val_955_;
goto v___jp_944_;
}
v___jp_287_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_box(0);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
v___jp_290_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
v___jp_293_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
v___jp_296_:
{
if (v_a_298_ == 0)
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
goto v___jp_287_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_300_ = lean_string_append(v_name_281_, v___x_299_);
v___x_301_ = lean_string_append(v___x_300_, v_repo_282_);
lean_dec_ref(v_repo_282_);
v___x_302_ = 2;
v___x_303_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*1, v___x_302_);
lean_inc_ref(v___y_297_);
v___x_304_ = lean_apply_2(v___y_297_, v___x_303_, lean_box(0));
goto v___jp_287_;
}
}
v___jp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_309_ = l_Lake_GitRepo_gcAuto(v_repo_282_, v___x_308_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_a_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
v_a_311_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_309_, 2);
v___x_312_ = lean_array_get_size(v_a_311_);
v___x_313_ = lean_nat_dec_lt(v___x_307_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec(v_a_311_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v_a_310_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_box(0);
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_312_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_311_, v___x_316_, v___x_317_, v___x_315_, v___y_306_);
lean_dec(v_a_311_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v___x_318_, 0);
lean_dec(v_unused_326_);
v___x_320_ = v___x_318_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_dec(v___x_318_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v_a_310_);
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_310_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_dec(v_a_310_);
return v___x_318_;
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_a_327_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_309_, 2);
v___x_328_ = lean_array_get_size(v_a_327_);
v___x_329_ = lean_nat_dec_lt(v___x_307_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_a_327_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_box(0);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_328_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_327_, v___x_333_, v___x_334_, v___x_332_, v___y_306_);
lean_dec(v_a_327_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v___x_335_, 0);
lean_dec(v_unused_343_);
v___x_337_ = v___x_335_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_dec(v___x_335_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 1);
lean_ctor_set(v___x_337_, 0, v___x_332_);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_332_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
return v___x_335_;
}
}
}
}
v___jp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
lean_inc_ref(v___y_345_);
v___x_349_ = l_Lake_GitRepo_pruneRemote(v___y_345_, v_repo_282_, v___x_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_a_350_ = lean_ctor_get(v___x_349_, 1);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 2);
v___x_351_ = lean_array_get_size(v_a_350_);
v___x_352_ = lean_nat_dec_lt(v___x_347_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_a_350_);
v___y_306_ = v___y_346_;
goto v___jp_305_;
}
else
{
lean_object* v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_box(0);
v___x_354_ = ((size_t)0ULL);
v___x_355_ = lean_usize_of_nat(v___x_351_);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_350_, v___x_354_, v___x_355_, v___x_353_, v___y_346_);
lean_dec(v_a_350_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_dec_ref_known(v___x_356_, 1);
v___y_306_ = v___y_346_;
goto v___jp_305_;
}
else
{
lean_dec_ref(v_repo_282_);
return v___x_356_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
lean_dec_ref(v_repo_282_);
v_a_357_ = lean_ctor_get(v___x_349_, 1);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_349_, 2);
v___x_358_ = lean_array_get_size(v_a_357_);
v___x_359_ = lean_nat_dec_lt(v___x_347_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_a_357_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_box(0);
v___x_363_ = ((size_t)0ULL);
v___x_364_ = lean_usize_of_nat(v___x_358_);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_357_, v___x_363_, v___x_364_, v___x_362_, v___y_346_);
lean_dec(v_a_357_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_373_);
v___x_367_ = v___x_365_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_dec(v___x_365_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 1);
lean_ctor_set(v___x_367_, 0, v___x_362_);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_362_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
return v___x_365_;
}
}
}
}
v___jp_374_:
{
if (v_a_377_ == 0)
{
lean_dec_ref(v_name_281_);
v___y_345_ = v___y_375_;
v___y_346_ = v___y_376_;
goto v___jp_344_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_378_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_379_ = lean_string_append(v_name_281_, v___x_378_);
v___x_380_ = lean_string_append(v___x_379_, v_repo_282_);
v___x_381_ = 2;
v___x_382_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*1, v___x_381_);
lean_inc_ref(v___y_376_);
v___x_383_ = lean_apply_2(v___y_376_, v___x_382_, lean_box(0));
v___y_345_ = v___y_375_;
v___y_346_ = v___y_376_;
goto v___jp_344_;
}
}
v___jp_384_:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_array_get_size(v___y_387_);
v___x_391_ = lean_nat_dec_lt(v___y_386_, v___x_390_);
if (v___x_391_ == 0)
{
v___y_375_ = v___y_385_;
v___y_376_ = v___y_388_;
v_a_377_ = v_val_389_;
goto v___jp_374_;
}
else
{
lean_object* v___x_392_; size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_box(0);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = lean_usize_of_nat(v___x_390_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_387_, v___x_393_, v___x_394_, v___x_392_, v___y_388_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_dec_ref_known(v___x_395_, 1);
v___y_375_ = v___y_385_;
v___y_376_ = v___y_388_;
v_a_377_ = v_val_389_;
goto v___jp_374_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_395_;
}
}
}
v___jp_396_:
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_402_ = l_Lake_GitRepo_hasNoDiff(v_repo_282_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; 
v___x_403_ = 1;
v___y_385_ = v___y_397_;
v___y_386_ = v___x_400_;
v___y_387_ = v___x_401_;
v___y_388_ = v___y_398_;
v_val_389_ = v___x_403_;
goto v___jp_384_;
}
else
{
v___y_385_ = v___y_397_;
v___y_386_ = v___x_400_;
v___y_387_ = v___x_401_;
v___y_388_ = v___y_398_;
v_val_389_ = v___y_399_;
goto v___jp_384_;
}
}
v___jp_404_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_410_ = l_Lake_GitRepo_clean(v_repo_282_, v___x_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_a_411_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 2);
v___x_412_ = lean_array_get_size(v_a_411_);
v___x_413_ = lean_nat_dec_lt(v___x_408_, v___x_412_);
if (v___x_413_ == 0)
{
lean_dec(v_a_411_);
v___y_397_ = v___y_405_;
v___y_398_ = v___y_406_;
v___y_399_ = v___y_407_;
goto v___jp_396_;
}
else
{
lean_object* v___x_414_; size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_box(0);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = lean_usize_of_nat(v___x_412_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_411_, v___x_415_, v___x_416_, v___x_414_, v___y_406_);
lean_dec(v_a_411_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_dec_ref_known(v___x_417_, 1);
v___y_397_ = v___y_405_;
v___y_398_ = v___y_406_;
v___y_399_ = v___y_407_;
goto v___jp_396_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_417_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_418_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_410_, 2);
v___x_419_ = lean_array_get_size(v_a_418_);
v___x_420_ = lean_nat_dec_lt(v___x_408_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v_a_418_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_box(0);
v___x_424_ = ((size_t)0ULL);
v___x_425_ = lean_usize_of_nat(v___x_419_);
v___x_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_418_, v___x_424_, v___x_425_, v___x_423_, v___y_406_);
lean_dec(v_a_418_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v___x_426_, 0);
lean_dec(v_unused_434_);
v___x_428_ = v___x_426_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_dec(v___x_426_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 1);
lean_ctor_set(v___x_428_, 0, v___x_423_);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_423_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
return v___x_426_;
}
}
}
}
v___jp_435_:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_array_get_size(v___y_438_);
v___x_441_ = lean_nat_dec_lt(v___y_436_, v___x_440_);
if (v___x_441_ == 0)
{
v___y_297_ = v___y_437_;
v_a_298_ = v_val_439_;
goto v___jp_296_;
}
else
{
lean_object* v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
v___x_442_ = lean_box(0);
v___x_443_ = ((size_t)0ULL);
v___x_444_ = lean_usize_of_nat(v___x_440_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_438_, v___x_443_, v___x_444_, v___x_442_, v___y_437_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_dec_ref_known(v___x_445_, 1);
v___y_297_ = v___y_437_;
v_a_298_ = v_val_439_;
goto v___jp_296_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_445_;
}
}
}
v___jp_446_:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_453_ = l_Option_instDecidableEq___redArg(v___x_452_, v_a_451_, v___y_450_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_454_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_281_);
v___x_455_ = lean_string_append(v_name_281_, v___x_454_);
v___x_456_ = lean_string_append(v___x_455_, v___y_448_);
v___x_457_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_458_ = lean_string_append(v___x_456_, v___x_457_);
v___x_459_ = 1;
v___x_460_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*1, v___x_459_);
lean_inc_ref(v___y_449_);
v___x_461_ = lean_apply_2(v___y_449_, v___x_460_, lean_box(0));
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_464_ = l_Lake_GitRepo_checkoutDetach(v___y_448_, v_repo_282_, v___x_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_a_465_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 2);
v___x_466_ = lean_array_get_size(v_a_465_);
v___x_467_ = lean_nat_dec_lt(v___x_462_, v___x_466_);
if (v___x_467_ == 0)
{
lean_dec(v_a_465_);
v___y_405_ = v___y_447_;
v___y_406_ = v___y_449_;
v___y_407_ = v___x_453_;
goto v___jp_404_;
}
else
{
lean_object* v___x_468_; size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_468_ = lean_box(0);
v___x_469_ = ((size_t)0ULL);
v___x_470_ = lean_usize_of_nat(v___x_466_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_465_, v___x_469_, v___x_470_, v___x_468_, v___y_449_);
lean_dec(v_a_465_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_dec_ref_known(v___x_471_, 1);
v___y_405_ = v___y_447_;
v___y_406_ = v___y_449_;
v___y_407_ = v___x_453_;
goto v___jp_404_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_471_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_472_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_464_, 2);
v___x_473_ = lean_array_get_size(v_a_472_);
v___x_474_ = lean_nat_dec_lt(v___x_462_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_a_472_);
v___x_475_ = lean_box(0);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_box(0);
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_473_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_472_, v___x_478_, v___x_479_, v___x_477_, v___y_449_);
lean_dec(v_a_472_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v___x_480_, 0);
lean_dec(v_unused_488_);
v___x_482_ = v___x_480_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_dec(v___x_480_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 1);
lean_ctor_set(v___x_482_, 0, v___x_477_);
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_477_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
lean_dec_ref(v___y_448_);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_491_ = l_Lake_GitRepo_hasNoDiff(v_repo_282_);
if (v___x_491_ == 0)
{
v___y_436_ = v___x_489_;
v___y_437_ = v___y_449_;
v___y_438_ = v___x_490_;
v_val_439_ = v___x_453_;
goto v___jp_435_;
}
else
{
uint8_t v___x_492_; 
v___x_492_ = 0;
v___y_436_ = v___x_489_;
v___y_437_ = v___y_449_;
v___y_438_ = v___x_490_;
v_val_439_ = v___x_492_;
goto v___jp_435_;
}
}
}
v___jp_493_:
{
if (lean_obj_tag(v_a_498_) == 1)
{
lean_object* v_val_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
lean_dec_ref(v___y_497_);
lean_dec_ref(v___y_496_);
v_val_499_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_499_);
v___x_500_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_501_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_282_);
v___x_502_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_501_, v_repo_282_);
v___x_503_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_503_ == 0)
{
v___y_447_ = v___y_494_;
v___y_448_ = v_val_499_;
v___y_449_ = v___y_495_;
v___y_450_ = v_a_498_;
v_a_451_ = v___x_502_;
goto v___jp_446_;
}
else
{
lean_object* v___x_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v___x_504_ = lean_box(0);
v___x_505_ = ((size_t)0ULL);
v___x_506_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_500_, v___x_505_, v___x_506_, v___x_504_, v___y_495_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_dec_ref_known(v___x_507_, 1);
v___y_447_ = v___y_494_;
v___y_448_ = v_val_499_;
v___y_449_ = v___y_495_;
v___y_450_ = v_a_498_;
v_a_451_ = v___x_502_;
goto v___jp_446_;
}
else
{
lean_dec(v___x_502_);
lean_dec_ref_known(v_a_498_, 1);
lean_dec(v_val_499_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_507_;
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_a_498_);
lean_dec_ref(v_repo_282_);
v___x_508_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_509_ = lean_string_append(v_name_281_, v___x_508_);
v___x_510_ = lean_string_append(v___x_509_, v___y_496_);
lean_dec_ref(v___y_496_);
v___x_511_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_512_ = lean_string_append(v___x_510_, v___x_511_);
v___x_513_ = lean_string_append(v___x_512_, v___y_497_);
lean_dec_ref(v___y_497_);
v___x_514_ = 3;
v___x_515_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_514_);
lean_inc_ref(v___y_495_);
v___x_516_ = lean_apply_2(v___y_495_, v___x_515_, lean_box(0));
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
v___jp_519_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_524_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_281_);
v___x_525_ = lean_string_append(v_name_281_, v___x_524_);
v___x_526_ = lean_string_append(v___x_525_, v___y_521_);
v___x_527_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
v___x_529_ = lean_string_append(v___x_528_, v___y_522_);
v___x_530_ = 1;
v___x_531_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_530_);
lean_inc_ref(v___y_523_);
v___x_532_ = lean_apply_2(v___y_523_, v___x_531_, lean_box(0));
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_521_);
lean_inc_ref(v___y_520_);
lean_inc_ref(v_repo_282_);
v___x_535_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_282_, v___y_520_, v___y_521_, v___x_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_a_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
v_a_537_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_535_, 2);
v___x_538_ = lean_array_get_size(v_a_537_);
v___x_539_ = lean_nat_dec_lt(v___x_533_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v_a_537_);
v___y_494_ = v___y_520_;
v___y_495_ = v___y_523_;
v___y_496_ = v___y_521_;
v___y_497_ = v___y_522_;
v_a_498_ = v_a_536_;
goto v___jp_493_;
}
else
{
lean_object* v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v___x_540_ = lean_box(0);
v___x_541_ = ((size_t)0ULL);
v___x_542_ = lean_usize_of_nat(v___x_538_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_537_, v___x_541_, v___x_542_, v___x_540_, v___y_523_);
lean_dec(v_a_537_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_dec_ref_known(v___x_543_, 1);
v___y_494_ = v___y_520_;
v___y_495_ = v___y_523_;
v___y_496_ = v___y_521_;
v___y_497_ = v___y_522_;
v_a_498_ = v_a_536_;
goto v___jp_493_;
}
else
{
lean_dec(v_a_536_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_543_;
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_544_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_535_, 2);
v___x_545_ = lean_array_get_size(v_a_544_);
v___x_546_ = lean_nat_dec_lt(v___x_533_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_a_544_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_549_ = lean_box(0);
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_545_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_544_, v___x_550_, v___x_551_, v___x_549_, v___y_523_);
lean_dec(v_a_544_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_552_, 0);
lean_dec(v_unused_560_);
v___x_554_ = v___x_552_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_dec(v___x_552_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 0, v___x_549_);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_549_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
return v___x_552_;
}
}
}
}
v___jp_561_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
lean_inc_ref(v___y_564_);
lean_inc_ref(v___y_562_);
v___x_567_ = l_Lake_GitRepo_addRemote(v___y_562_, v___y_564_, v_repo_282_, v___x_566_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_a_568_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 2);
v___x_569_ = lean_array_get_size(v_a_568_);
v___x_570_ = lean_nat_dec_lt(v___x_565_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v_a_568_);
v___y_520_ = v___y_562_;
v___y_521_ = v___y_563_;
v___y_522_ = v___y_564_;
v___y_523_ = v_a_285_;
goto v___jp_519_;
}
else
{
lean_object* v___x_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
v___x_571_ = lean_box(0);
v___x_572_ = ((size_t)0ULL);
v___x_573_ = lean_usize_of_nat(v___x_569_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_568_, v___x_572_, v___x_573_, v___x_571_, v_a_285_);
lean_dec(v_a_568_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_dec_ref_known(v___x_574_, 1);
v___y_520_ = v___y_562_;
v___y_521_ = v___y_563_;
v___y_522_ = v___y_564_;
v___y_523_ = v_a_285_;
goto v___jp_519_;
}
else
{
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_574_;
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_575_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_567_, 2);
v___x_576_ = lean_array_get_size(v_a_575_);
v___x_577_ = lean_nat_dec_lt(v___x_565_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_a_575_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v___x_583_; 
v___x_580_ = lean_box(0);
v___x_581_ = ((size_t)0ULL);
v___x_582_ = lean_usize_of_nat(v___x_576_);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_575_, v___x_581_, v___x_582_, v___x_580_, v_a_285_);
lean_dec(v_a_575_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_591_);
v___x_585_ = v___x_583_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_dec(v___x_583_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 1);
lean_ctor_set(v___x_585_, 0, v___x_580_);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_580_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
return v___x_583_;
}
}
}
}
v___jp_592_:
{
if (v_a_594_ == 0)
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
goto v___jp_290_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_595_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_596_ = lean_string_append(v_name_281_, v___x_595_);
v___x_597_ = lean_string_append(v___x_596_, v_repo_282_);
lean_dec_ref(v_repo_282_);
v___x_598_ = 2;
v___x_599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*1, v___x_598_);
lean_inc_ref(v___y_593_);
v___x_600_ = lean_apply_2(v___y_593_, v___x_599_, lean_box(0));
goto v___jp_290_;
}
}
v___jp_601_:
{
if (v_a_603_ == 0)
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
goto v___jp_293_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_604_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_605_ = lean_string_append(v_name_281_, v___x_604_);
v___x_606_ = lean_string_append(v___x_605_, v_repo_282_);
lean_dec_ref(v_repo_282_);
v___x_607_ = 2;
v___x_608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*1, v___x_607_);
lean_inc_ref(v___y_602_);
v___x_609_ = lean_apply_2(v___y_602_, v___x_608_, lean_box(0));
goto v___jp_293_;
}
}
v___jp_610_:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_array_get_size(v___y_613_);
v___x_616_ = lean_nat_dec_lt(v___y_612_, v___x_615_);
if (v___x_616_ == 0)
{
v___y_593_ = v___y_611_;
v_a_594_ = v_val_614_;
goto v___jp_592_;
}
else
{
lean_object* v___x_617_; size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_box(0);
v___x_618_ = ((size_t)0ULL);
v___x_619_ = lean_usize_of_nat(v___x_615_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_613_, v___x_618_, v___x_619_, v___x_617_, v___y_611_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec_ref_known(v___x_620_, 1);
v___y_593_ = v___y_611_;
v_a_594_ = v_val_614_;
goto v___jp_592_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_620_;
}
}
}
v___jp_621_:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_627_ = l_Lake_GitRepo_hasNoDiff(v_repo_282_);
if (v___x_627_ == 0)
{
v___y_611_ = v___y_622_;
v___y_612_ = v___x_625_;
v___y_613_ = v___x_626_;
v_val_614_ = v___y_624_;
goto v___jp_610_;
}
else
{
v___y_611_ = v___y_622_;
v___y_612_ = v___x_625_;
v___y_613_ = v___x_626_;
v_val_614_ = v___y_623_;
goto v___jp_610_;
}
}
v___jp_628_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_634_ = l_Lake_GitRepo_clean(v_repo_282_, v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 1);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 2);
v___x_636_ = lean_array_get_size(v_a_635_);
v___x_637_ = lean_nat_dec_lt(v___x_632_, v___x_636_);
if (v___x_637_ == 0)
{
lean_dec(v_a_635_);
v___y_622_ = v___y_629_;
v___y_623_ = v___y_630_;
v___y_624_ = v___y_631_;
goto v___jp_621_;
}
else
{
lean_object* v___x_638_; size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_box(0);
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_636_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_635_, v___x_639_, v___x_640_, v___x_638_, v___y_629_);
lean_dec(v_a_635_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref_known(v___x_641_, 1);
v___y_622_ = v___y_629_;
v___y_623_ = v___y_630_;
v___y_624_ = v___y_631_;
goto v___jp_621_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_641_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_642_ = lean_ctor_get(v___x_634_, 1);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_634_, 2);
v___x_643_ = lean_array_get_size(v_a_642_);
v___x_644_ = lean_nat_dec_lt(v___x_632_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_a_642_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___x_647_ = lean_box(0);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_643_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_642_, v___x_648_, v___x_649_, v___x_647_, v___y_629_);
lean_dec(v_a_642_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_658_);
v___x_652_ = v___x_650_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_dec(v___x_650_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 1);
lean_ctor_set(v___x_652_, 0, v___x_647_);
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_647_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
return v___x_650_;
}
}
}
}
v___jp_659_:
{
if (lean_obj_tag(v_a_666_) == 0)
{
v___y_520_ = v___y_661_;
v___y_521_ = v___y_663_;
v___y_522_ = v___y_664_;
v___y_523_ = v___y_660_;
goto v___jp_519_;
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v___y_664_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_666_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_a_666_, 0);
lean_dec(v_unused_708_);
v___x_668_ = v_a_666_;
v_isShared_669_ = v_isSharedCheck_707_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_a_666_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_707_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_670_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_281_);
v___x_671_ = lean_string_append(v_name_281_, v___x_670_);
v___x_672_ = lean_string_append(v___x_671_, v___y_663_);
v___x_673_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
v___x_675_ = 1;
v___x_676_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*1, v___x_675_);
lean_inc_ref(v___y_660_);
v___x_677_ = lean_apply_2(v___y_660_, v___x_676_, lean_box(0));
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_680_ = l_Lake_GitRepo_checkoutDetach(v___y_663_, v_repo_282_, v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
lean_del_object(v___x_668_);
v_a_681_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 2);
v___x_682_ = lean_array_get_size(v_a_681_);
v___x_683_ = lean_nat_dec_lt(v___x_678_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec(v_a_681_);
v___y_629_ = v___y_660_;
v___y_630_ = v___y_662_;
v___y_631_ = v___y_665_;
goto v___jp_628_;
}
else
{
lean_object* v___x_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_box(0);
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_682_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_681_, v___x_685_, v___x_686_, v___x_684_, v___y_660_);
lean_dec(v_a_681_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec_ref_known(v___x_687_, 1);
v___y_629_ = v___y_660_;
v___y_630_ = v___y_662_;
v___y_631_ = v___y_665_;
goto v___jp_628_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_687_;
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_688_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_680_, 2);
v___x_689_ = lean_array_get_size(v_a_688_);
v___x_690_ = lean_nat_dec_lt(v___x_678_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_693_; 
lean_dec(v_a_688_);
v___x_691_ = lean_box(0);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_691_);
v___x_693_ = v___x_668_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
lean_object* v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
lean_del_object(v___x_668_);
v___x_695_ = lean_box(0);
v___x_696_ = ((size_t)0ULL);
v___x_697_ = lean_usize_of_nat(v___x_689_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_688_, v___x_696_, v___x_697_, v___x_695_, v___y_660_);
lean_dec(v_a_688_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_698_, 0);
lean_dec(v_unused_706_);
v___x_700_ = v___x_698_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_dec(v___x_698_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 1);
lean_ctor_set(v___x_700_, 0, v___x_695_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_695_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
return v___x_698_;
}
}
}
}
}
}
v___jp_709_:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_array_get_size(v___y_712_);
v___x_715_ = lean_nat_dec_lt(v___y_711_, v___x_714_);
if (v___x_715_ == 0)
{
v___y_602_ = v___y_710_;
v_a_603_ = v_val_713_;
goto v___jp_601_;
}
else
{
lean_object* v___x_716_; size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_box(0);
v___x_717_ = ((size_t)0ULL);
v___x_718_ = lean_usize_of_nat(v___x_714_);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_712_, v___x_717_, v___x_718_, v___x_716_, v___y_710_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_dec_ref_known(v___x_719_, 1);
v___y_602_ = v___y_710_;
v_a_603_ = v_val_713_;
goto v___jp_601_;
}
else
{
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_719_;
}
}
}
v___jp_720_:
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_723_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v___y_723_);
v___x_728_ = l_Option_instDecidableEq___redArg(v___x_726_, v_a_725_, v___x_727_);
if (v___x_728_ == 0)
{
uint8_t v___x_729_; 
v___x_729_ = l_Lake_GitRev_isFullSha1(v___y_723_);
if (v___x_729_ == 0)
{
v___y_520_ = v___y_722_;
v___y_521_ = v___y_723_;
v___y_522_ = v___y_724_;
v___y_523_ = v___y_721_;
goto v___jp_519_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
lean_inc_ref(v___y_723_);
v___x_731_ = l_Lake_GitRepo_findCommit_x3f(v___y_723_, v_repo_282_);
v___x_732_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_732_ == 0)
{
v___y_660_ = v___y_721_;
v___y_661_ = v___y_722_;
v___y_662_ = v___x_728_;
v___y_663_ = v___y_723_;
v___y_664_ = v___y_724_;
v___y_665_ = v___x_729_;
v_a_666_ = v___x_731_;
goto v___jp_659_;
}
else
{
lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v___x_733_ = lean_box(0);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_730_, v___x_734_, v___x_735_, v___x_733_, v___y_721_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_dec_ref_known(v___x_736_, 1);
v___y_660_ = v___y_721_;
v___y_661_ = v___y_722_;
v___y_662_ = v___x_728_;
v___y_663_ = v___y_723_;
v___y_664_ = v___y_724_;
v___y_665_ = v___x_729_;
v_a_666_ = v___x_731_;
goto v___jp_659_;
}
else
{
lean_dec(v___x_731_);
lean_dec_ref(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_736_;
}
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
lean_dec_ref(v___y_724_);
lean_dec_ref(v___y_723_);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_739_ = l_Lake_GitRepo_hasNoDiff(v_repo_282_);
if (v___x_739_ == 0)
{
v___y_710_ = v___y_721_;
v___y_711_ = v___x_737_;
v___y_712_ = v___x_738_;
v_val_713_ = v___x_728_;
goto v___jp_709_;
}
else
{
uint8_t v___x_740_; 
v___x_740_ = 0;
v___y_710_ = v___y_721_;
v___y_711_ = v___x_737_;
v___y_712_ = v___x_738_;
v_val_713_ = v___x_740_;
goto v___jp_709_;
}
}
}
v___jp_741_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_746_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_747_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_282_);
v___x_748_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_747_, v_repo_282_);
v___x_749_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_749_ == 0)
{
v___y_721_ = v___y_745_;
v___y_722_ = v___y_742_;
v___y_723_ = v___y_743_;
v___y_724_ = v___y_744_;
v_a_725_ = v___x_748_;
goto v___jp_720_;
}
else
{
lean_object* v___x_750_; size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_750_ = lean_box(0);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_746_, v___x_751_, v___x_752_, v___x_750_, v___y_745_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_dec_ref_known(v___x_753_, 1);
v___y_721_ = v___y_745_;
v___y_722_ = v___y_742_;
v___y_723_ = v___y_743_;
v___y_724_ = v___y_744_;
v_a_725_ = v___x_748_;
goto v___jp_720_;
}
else
{
lean_dec(v___x_748_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_753_;
}
}
}
v___jp_754_:
{
if (lean_obj_tag(v_a_758_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_802_; 
v_val_759_ = lean_ctor_get(v_a_758_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_802_ == 0)
{
v___x_761_ = v_a_758_;
v_isShared_762_ = v_isSharedCheck_802_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_val_759_);
lean_dec(v_a_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_802_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_string_dec_eq(v_val_759_, v___y_757_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_764_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_281_);
v___x_765_ = lean_string_append(v_name_281_, v___x_764_);
v___x_766_ = lean_string_append(v___x_765_, v_val_759_);
lean_dec(v_val_759_);
v___x_767_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_768_ = lean_string_append(v___x_766_, v___x_767_);
v___x_769_ = lean_string_append(v___x_768_, v___y_757_);
v___x_770_ = 1;
v___x_771_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*1, v___x_770_);
lean_inc_ref(v_a_285_);
v___x_772_ = lean_apply_2(v_a_285_, v___x_771_, lean_box(0));
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
lean_inc_ref(v___y_757_);
lean_inc_ref(v___y_755_);
v___x_775_ = l_Lake_GitRepo_setRemoteUrl(v___y_755_, v___y_757_, v_repo_282_, v___x_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
lean_del_object(v___x_761_);
v_a_776_ = lean_ctor_get(v___x_775_, 1);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 2);
v___x_777_ = lean_array_get_size(v_a_776_);
v___x_778_ = lean_nat_dec_lt(v___x_773_, v___x_777_);
if (v___x_778_ == 0)
{
lean_dec(v_a_776_);
v___y_742_ = v___y_755_;
v___y_743_ = v___y_756_;
v___y_744_ = v___y_757_;
v___y_745_ = v_a_285_;
goto v___jp_741_;
}
else
{
lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_779_ = lean_box(0);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_777_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_776_, v___x_780_, v___x_781_, v___x_779_, v_a_285_);
lean_dec(v_a_776_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_dec_ref_known(v___x_782_, 1);
v___y_742_ = v___y_755_;
v___y_743_ = v___y_756_;
v___y_744_ = v___y_757_;
v___y_745_ = v_a_285_;
goto v___jp_741_;
}
else
{
lean_dec_ref(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_782_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
lean_dec_ref(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_783_ = lean_ctor_get(v___x_775_, 1);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_775_, 2);
v___x_784_ = lean_array_get_size(v_a_783_);
v___x_785_ = lean_nat_dec_lt(v___x_773_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_dec(v_a_783_);
v___x_786_ = lean_box(0);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_786_);
v___x_788_ = v___x_761_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
else
{
lean_object* v___x_790_; size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
lean_del_object(v___x_761_);
v___x_790_ = lean_box(0);
v___x_791_ = ((size_t)0ULL);
v___x_792_ = lean_usize_of_nat(v___x_784_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_783_, v___x_791_, v___x_792_, v___x_790_, v_a_285_);
lean_dec(v_a_783_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_793_, 0);
lean_dec(v_unused_801_);
v___x_795_ = v___x_793_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_dec(v___x_793_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 1);
lean_ctor_set(v___x_795_, 0, v___x_790_);
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_790_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
return v___x_793_;
}
}
}
}
else
{
lean_del_object(v___x_761_);
lean_dec(v_val_759_);
v___y_742_ = v___y_755_;
v___y_743_ = v___y_756_;
v___y_744_ = v___y_757_;
v___y_745_ = v_a_285_;
goto v___jp_741_;
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v_a_758_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
lean_inc_ref(v___y_757_);
lean_inc_ref(v___y_755_);
v___x_805_ = l_Lake_GitRepo_addRemote(v___y_755_, v___y_757_, v_repo_282_, v___x_804_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_a_806_ = lean_ctor_get(v___x_805_, 1);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 2);
v___x_807_ = lean_array_get_size(v_a_806_);
v___x_808_ = lean_nat_dec_lt(v___x_803_, v___x_807_);
if (v___x_808_ == 0)
{
lean_dec(v_a_806_);
v___y_742_ = v___y_755_;
v___y_743_ = v___y_756_;
v___y_744_ = v___y_757_;
v___y_745_ = v_a_285_;
goto v___jp_741_;
}
else
{
lean_object* v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_box(0);
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_807_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_806_, v___x_810_, v___x_811_, v___x_809_, v_a_285_);
lean_dec(v_a_806_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_dec_ref_known(v___x_812_, 1);
v___y_742_ = v___y_755_;
v___y_743_ = v___y_756_;
v___y_744_ = v___y_757_;
v___y_745_ = v_a_285_;
goto v___jp_741_;
}
else
{
lean_dec_ref(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_812_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
lean_dec_ref(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_813_ = lean_ctor_get(v___x_805_, 1);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_805_, 2);
v___x_814_ = lean_array_get_size(v_a_813_);
v___x_815_ = lean_nat_dec_lt(v___x_803_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec(v_a_813_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
else
{
lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_818_ = lean_box(0);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = lean_usize_of_nat(v___x_814_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_813_, v___x_819_, v___x_820_, v___x_818_, v_a_285_);
lean_dec(v_a_813_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v___x_821_, 0);
lean_dec(v_unused_829_);
v___x_823_ = v___x_821_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_dec(v___x_821_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 1);
lean_ctor_set(v___x_823_, 0, v___x_818_);
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_818_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
return v___x_821_;
}
}
}
}
}
v___jp_830_:
{
if (v_a_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_835_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_281_);
v___x_836_ = lean_string_append(v_name_281_, v___x_835_);
v___x_837_ = 1;
v___x_838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*1, v___x_837_);
lean_inc_ref(v_a_285_);
v___x_839_ = lean_apply_2(v_a_285_, v___x_838_, lean_box(0));
lean_inc_ref(v_repo_282_);
v___x_840_ = l_IO_FS_createDirAll(v_repo_282_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_873_; 
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v___x_840_, 0);
lean_dec(v_unused_874_);
v___x_842_ = v___x_840_;
v_isShared_843_ = v_isSharedCheck_873_;
goto v_resetjp_841_;
}
else
{
lean_dec(v___x_840_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_873_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
v___x_846_ = l_Lake_GitRepo_quietInit(v_repo_282_, v___x_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
lean_del_object(v___x_842_);
v_a_847_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 2);
v___x_848_ = lean_array_get_size(v_a_847_);
v___x_849_ = lean_nat_dec_lt(v___x_844_, v___x_848_);
if (v___x_849_ == 0)
{
lean_dec(v_a_847_);
v___y_562_ = v___y_831_;
v___y_563_ = v___y_832_;
v___y_564_ = v___y_833_;
goto v___jp_561_;
}
else
{
lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v___x_850_ = lean_box(0);
v___x_851_ = ((size_t)0ULL);
v___x_852_ = lean_usize_of_nat(v___x_848_);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_847_, v___x_851_, v___x_852_, v___x_850_, v_a_285_);
lean_dec(v_a_847_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_dec_ref_known(v___x_853_, 1);
v___y_562_ = v___y_831_;
v___y_563_ = v___y_832_;
v___y_564_ = v___y_833_;
goto v___jp_561_;
}
else
{
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_853_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_854_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_846_, 2);
v___x_855_ = lean_array_get_size(v_a_854_);
v___x_856_ = lean_nat_dec_lt(v___x_844_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v_a_854_);
v___x_857_ = lean_box(0);
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 1);
lean_ctor_set(v___x_842_, 0, v___x_857_);
v___x_859_ = v___x_842_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
lean_del_object(v___x_842_);
v___x_861_ = lean_box(0);
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_855_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_854_, v___x_862_, v___x_863_, v___x_861_, v_a_285_);
lean_dec(v_a_854_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_872_);
v___x_866_ = v___x_864_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_dec(v___x_864_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 1);
lean_ctor_set(v___x_866_, 0, v___x_861_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_861_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
return v___x_864_;
}
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
v_a_875_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_887_ == 0)
{
v___x_877_ = v___x_840_;
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_840_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_879_ = lean_io_error_to_string(v_a_875_);
v___x_880_ = 3;
v___x_881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_880_);
lean_inc_ref(v_a_285_);
v___x_882_ = lean_apply_2(v_a_285_, v___x_881_, lean_box(0));
v___x_883_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_883_);
v___x_885_ = v___x_877_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_282_);
lean_inc_ref(v___y_831_);
v___x_889_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_831_, v_repo_282_);
v___x_890_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_890_ == 0)
{
v___y_755_ = v___y_831_;
v___y_756_ = v___y_832_;
v___y_757_ = v___y_833_;
v_a_758_ = v___x_889_;
goto v___jp_754_;
}
else
{
lean_object* v___x_891_; size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_891_ = lean_box(0);
v___x_892_ = ((size_t)0ULL);
v___x_893_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_888_, v___x_892_, v___x_893_, v___x_891_, v_a_285_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_dec_ref_known(v___x_894_, 1);
v___y_755_ = v___y_831_;
v___y_756_ = v___y_832_;
v___y_757_ = v___y_833_;
v_a_758_ = v___x_889_;
goto v___jp_754_;
}
else
{
lean_dec(v___x_889_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_894_;
}
}
}
}
v___jp_895_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; uint8_t v___x_903_; 
v___x_899_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_900_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_282_);
v___x_901_ = l_System_FilePath_join(v_repo_282_, v___x_900_);
v___x_902_ = l_System_FilePath_pathExists(v___x_901_);
lean_dec_ref(v___x_901_);
v___x_903_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_903_ == 0)
{
v___y_831_ = v___y_896_;
v___y_832_ = v___y_897_;
v___y_833_ = v_a_898_;
v_a_834_ = v___x_902_;
goto v___jp_830_;
}
else
{
lean_object* v___x_904_; size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
v___x_904_ = lean_box(0);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_899_, v___x_905_, v___x_906_, v___x_904_, v_a_285_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_dec_ref_known(v___x_907_, 1);
v___y_831_ = v___y_896_;
v___y_832_ = v___y_897_;
v___y_833_ = v_a_898_;
v_a_834_ = v___x_902_;
goto v___jp_830_;
}
else
{
lean_dec_ref(v_a_898_);
lean_dec_ref(v___y_897_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_907_;
}
}
}
v___jp_908_:
{
if (lean_obj_tag(v_a_911_) == 1)
{
lean_object* v_val_912_; 
lean_dec_ref(v_url_283_);
v_val_912_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v_a_911_, 1);
v___y_896_ = v___y_909_;
v___y_897_ = v___y_910_;
v_a_898_ = v_val_912_;
goto v___jp_895_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_a_911_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v_repo_282_);
v___x_913_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_914_ = lean_string_append(v_name_281_, v___x_913_);
v___x_915_ = lean_string_append(v___x_914_, v_url_283_);
lean_dec_ref(v_url_283_);
v___x_916_ = 3;
v___x_917_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*1, v___x_916_);
lean_inc_ref(v_a_285_);
v___x_918_ = lean_apply_2(v_a_285_, v___x_917_, lean_box(0));
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
v___jp_921_:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_array_get_size(v___y_925_);
v___x_928_ = lean_nat_dec_lt(v___y_923_, v___x_927_);
if (v___x_928_ == 0)
{
v___y_909_ = v___y_922_;
v___y_910_ = v___y_924_;
v_a_911_ = v_val_926_;
goto v___jp_908_;
}
else
{
lean_object* v___x_929_; size_t v___x_930_; size_t v___x_931_; lean_object* v___x_932_; 
v___x_929_ = lean_box(0);
v___x_930_ = ((size_t)0ULL);
v___x_931_ = lean_usize_of_nat(v___x_927_);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_925_, v___x_930_, v___x_931_, v___x_929_, v_a_285_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_dec_ref_known(v___x_932_, 1);
v___y_909_ = v___y_922_;
v___y_910_ = v___y_924_;
v_a_911_ = v_val_926_;
goto v___jp_908_;
}
else
{
lean_dec(v_val_926_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v_url_283_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_932_;
}
}
}
v___jp_933_:
{
if (v_a_936_ == 0)
{
v___y_896_ = v___y_934_;
v___y_897_ = v___y_935_;
v_a_898_ = v_url_283_;
goto v___jp_895_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_283_);
v___x_939_ = l_Lake_resolvePath(v_url_283_);
v___x_940_ = lean_string_utf8_byte_size(v___x_939_);
v___x_941_ = lean_nat_dec_eq(v___x_940_, v___x_937_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_939_);
v___y_922_ = v___y_934_;
v___y_923_ = v___x_937_;
v___y_924_ = v___y_935_;
v___y_925_ = v___x_938_;
v_val_926_ = v___x_942_;
goto v___jp_921_;
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v___x_939_);
v___x_943_ = lean_box(0);
v___y_922_ = v___y_934_;
v___y_923_ = v___x_937_;
v___y_924_ = v___y_935_;
v___y_925_ = v___x_938_;
v_val_926_ = v___x_943_;
goto v___jp_921_;
}
}
}
v___jp_944_:
{
lean_object* v_remote_946_; lean_object* v___x_947_; uint8_t v___x_948_; uint8_t v___x_949_; 
v_remote_946_ = l_Lake_Git_defaultRemote;
v___x_947_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_948_ = l_System_FilePath_pathExists(v_url_283_);
v___x_949_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_949_ == 0)
{
v___y_934_ = v_remote_946_;
v___y_935_ = v___y_945_;
v_a_936_ = v___x_948_;
goto v___jp_933_;
}
else
{
lean_object* v___x_950_; size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___x_950_ = lean_box(0);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_947_, v___x_951_, v___x_952_, v___x_950_, v_a_285_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_dec_ref_known(v___x_953_, 1);
v___y_934_ = v_remote_946_;
v___y_935_ = v___y_945_;
v_a_936_ = v___x_948_;
goto v___jp_933_;
}
else
{
lean_dec_ref(v___y_945_);
lean_dec_ref(v_url_283_);
lean_dec_ref(v_repo_282_);
lean_dec_ref(v_name_281_);
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_956_, lean_object* v_repo_957_, lean_object* v_url_958_, lean_object* v_rev_x3f_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_956_, v_repo_957_, v_url_958_, v_rev_x3f_959_, v_a_960_);
lean_dec_ref(v_a_960_);
return v_res_962_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = l_Lake_instInhabitedPackageEntry_default;
v___x_970_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_971_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
lean_ctor_set(v___x_972_, 3, v___x_970_);
lean_ctor_set(v___x_972_, 4, v___x_969_);
return v___x_972_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_973_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_975_){
_start:
{
lean_object* v_manifestEntry_976_; lean_object* v_name_977_; 
v_manifestEntry_976_ = lean_ctor_get(v_self_975_, 4);
v_name_977_ = lean_ctor_get(v_manifestEntry_976_, 0);
lean_inc(v_name_977_);
return v_name_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lake_MaterializedDep_name(v_self_978_);
lean_dec_ref(v_self_978_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_980_){
_start:
{
lean_object* v_manifestEntry_981_; lean_object* v_name_982_; uint8_t v___x_983_; lean_object* v___x_984_; 
v_manifestEntry_981_ = lean_ctor_get(v_self_980_, 4);
lean_inc_ref(v_manifestEntry_981_);
lean_dec_ref(v_self_980_);
v_name_982_ = lean_ctor_get(v_manifestEntry_981_, 0);
lean_inc(v_name_982_);
lean_dec_ref(v_manifestEntry_981_);
v___x_983_ = 0;
v___x_984_ = l_Lean_Name_toString(v_name_982_, v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_985_){
_start:
{
lean_object* v_manifestEntry_986_; lean_object* v_scope_987_; 
v_manifestEntry_986_ = lean_ctor_get(v_self_985_, 4);
v_scope_987_ = lean_ctor_get(v_manifestEntry_986_, 1);
lean_inc_ref(v_scope_987_);
return v_scope_987_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lake_MaterializedDep_scope(v_self_988_);
lean_dec_ref(v_self_988_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_990_){
_start:
{
lean_object* v_manifestEntry_991_; lean_object* v_manifestFile_x3f_992_; 
v_manifestEntry_991_ = lean_ctor_get(v_self_990_, 4);
v_manifestFile_x3f_992_ = lean_ctor_get(v_manifestEntry_991_, 3);
lean_inc(v_manifestFile_x3f_992_);
return v_manifestFile_x3f_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_993_);
lean_dec_ref(v_self_993_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_995_){
_start:
{
lean_object* v_manifestEntry_996_; lean_object* v_manifestFile_x3f_997_; 
v_manifestEntry_996_ = lean_ctor_get(v_self_995_, 4);
v_manifestFile_x3f_997_ = lean_ctor_get(v_manifestEntry_996_, 3);
if (lean_obj_tag(v_manifestFile_x3f_997_) == 0)
{
lean_object* v___x_998_; 
v___x_998_ = l_Lake_defaultManifestFile;
return v___x_998_;
}
else
{
lean_object* v_val_999_; 
v_val_999_ = lean_ctor_get(v_manifestFile_x3f_997_, 0);
lean_inc(v_val_999_);
return v_val_999_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lake_MaterializedDep_relManifestFile(v_self_1000_);
lean_dec_ref(v_self_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_1002_){
_start:
{
lean_object* v_manifestEntry_1003_; lean_object* v_manifestFile_x3f_1004_; 
v_manifestEntry_1003_ = lean_ctor_get(v_self_1002_, 4);
v_manifestFile_x3f_1004_ = lean_ctor_get(v_manifestEntry_1003_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1004_) == 0)
{
lean_object* v_pkgDir_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_pkgDir_1005_ = lean_ctor_get(v_self_1002_, 0);
lean_inc_ref(v_pkgDir_1005_);
lean_dec_ref(v_self_1002_);
v___x_1006_ = l_Lake_defaultManifestFile;
v___x_1007_ = l_Lake_joinRelative(v_pkgDir_1005_, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v_pkgDir_1008_; lean_object* v_val_1009_; lean_object* v___x_1010_; 
lean_inc_ref(v_manifestFile_x3f_1004_);
v_pkgDir_1008_ = lean_ctor_get(v_self_1002_, 0);
lean_inc_ref(v_pkgDir_1008_);
lean_dec_ref(v_self_1002_);
v_val_1009_ = lean_ctor_get(v_manifestFile_x3f_1004_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v_manifestFile_x3f_1004_, 1);
v___x_1010_ = l_Lake_joinRelative(v_pkgDir_1008_, v_val_1009_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_1011_){
_start:
{
lean_object* v_manifestEntry_1012_; lean_object* v_configFile_1013_; 
v_manifestEntry_1012_ = lean_ctor_get(v_self_1011_, 4);
v_configFile_1013_ = lean_ctor_get(v_manifestEntry_1012_, 2);
lean_inc_ref(v_configFile_1013_);
return v_configFile_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lake_MaterializedDep_relConfigFile(v_self_1014_);
lean_dec_ref(v_self_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_1016_){
_start:
{
lean_object* v_manifestEntry_1017_; lean_object* v_pkgDir_1018_; lean_object* v_configFile_1019_; lean_object* v___x_1020_; 
v_manifestEntry_1017_ = lean_ctor_get(v_self_1016_, 4);
lean_inc_ref(v_manifestEntry_1017_);
v_pkgDir_1018_ = lean_ctor_get(v_self_1016_, 0);
lean_inc_ref(v_pkgDir_1018_);
lean_dec_ref(v_self_1016_);
v_configFile_1019_ = lean_ctor_get(v_manifestEntry_1017_, 2);
lean_inc_ref(v_configFile_1019_);
lean_dec_ref(v_manifestEntry_1017_);
v___x_1020_ = l_Lake_joinRelative(v_pkgDir_1018_, v_configFile_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_1021_){
_start:
{
lean_object* v_manifest_x3f_1022_; 
v_manifest_x3f_1022_ = lean_ctor_get(v_self_1021_, 3);
if (lean_obj_tag(v_manifest_x3f_1022_) == 1)
{
lean_object* v_a_1023_; uint8_t v_fixedToolchain_1024_; 
v_a_1023_ = lean_ctor_get(v_manifest_x3f_1022_, 0);
v_fixedToolchain_1024_ = lean_ctor_get_uint8(v_a_1023_, sizeof(void*)*4);
return v_fixedToolchain_1024_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = 0;
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_1026_){
_start:
{
uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_res_1027_ = l_Lake_MaterializedDep_fixedToolchain(v_self_1026_);
lean_dec_ref(v_self_1026_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_dep_1037_){
_start:
{
lean_object* v_name_1038_; lean_object* v_scope_1039_; lean_object* v_version_1040_; lean_object* v_fst_1042_; lean_object* v_snd_1043_; 
v_name_1038_ = lean_ctor_get(v_dep_1037_, 0);
lean_inc(v_name_1038_);
v_scope_1039_ = lean_ctor_get(v_dep_1037_, 1);
lean_inc_ref(v_scope_1039_);
v_version_1040_ = lean_ctor_get(v_dep_1037_, 2);
lean_inc(v_version_1040_);
lean_dec_ref(v_dep_1037_);
switch(lean_obj_tag(v_version_1040_))
{
case 0:
{
lean_object* v___x_1066_; 
v___x_1066_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1042_ = v___x_1066_;
v_snd_1043_ = v___x_1066_;
goto v___jp_1041_;
}
case 1:
{
lean_object* v_rev_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1082_; 
v_rev_1067_ = lean_ctor_get(v_version_1040_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_version_1040_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1069_ = v_version_1040_;
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_rev_1067_);
lean_dec(v_version_1040_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1071_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1072_ = l_String_quote(v_rev_1067_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 3);
lean_ctor_set(v___x_1069_, 0, v___x_1072_);
v___x_1074_ = v___x_1069_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1075_ = l_Std_Format_defWidth;
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = l_Std_Format_pretty(v___x_1074_, v___x_1075_, v___x_1076_, v___x_1076_);
v___x_1078_ = lean_string_append(v___x_1071_, v___x_1077_);
v___x_1079_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1080_ = lean_string_append(v___x_1079_, v___x_1077_);
lean_dec_ref(v___x_1077_);
v_fst_1042_ = v___x_1078_;
v_snd_1043_ = v___x_1080_;
goto v___jp_1041_;
}
}
}
default: 
{
lean_object* v_ver_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1099_; 
v_ver_1083_ = lean_ctor_get(v_version_1040_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_version_1040_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1085_ = v_version_1040_;
v_isShared_1086_ = v_isSharedCheck_1099_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_ver_1083_);
lean_dec(v_version_1040_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1099_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_toString_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_toString_1087_ = lean_ctor_get(v_ver_1083_, 0);
lean_inc_ref(v_toString_1087_);
lean_dec_ref(v_ver_1083_);
v___x_1088_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1089_ = l_String_quote(v_toString_1087_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 3);
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1091_ = v___x_1085_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1092_ = l_Std_Format_defWidth;
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = l_Std_Format_pretty(v___x_1091_, v___x_1092_, v___x_1093_, v___x_1093_);
v___x_1095_ = lean_string_append(v___x_1088_, v___x_1094_);
v___x_1096_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1097_ = lean_string_append(v___x_1096_, v___x_1094_);
lean_dec_ref(v___x_1094_);
v_fst_1042_ = v___x_1095_;
v_snd_1043_ = v___x_1097_;
goto v___jp_1041_;
}
}
}
}
v___jp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1044_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1039_);
v___x_1045_ = lean_string_append(v_scope_1039_, v___x_1044_);
v___x_1046_ = 0;
v___x_1047_ = l_Lean_Name_toString(v_name_1038_, v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1045_, v___x_1047_);
v___x_1049_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___x_1051_ = lean_string_append(v___x_1050_, v_scope_1039_);
v___x_1052_ = lean_string_append(v___x_1051_, v___x_1044_);
v___x_1053_ = lean_string_append(v___x_1052_, v___x_1047_);
v___x_1054_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1055_ = lean_string_append(v___x_1053_, v___x_1054_);
v___x_1056_ = lean_string_append(v___x_1055_, v_fst_1042_);
lean_dec_ref(v_fst_1042_);
v___x_1057_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
v___x_1059_ = lean_string_append(v___x_1058_, v_scope_1039_);
lean_dec_ref(v_scope_1039_);
v___x_1060_ = lean_string_append(v___x_1059_, v___x_1044_);
v___x_1061_ = lean_string_append(v___x_1060_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1062_ = lean_string_append(v___x_1061_, v___x_1054_);
v___x_1063_ = lean_string_append(v___x_1062_, v_snd_1043_);
lean_dec_ref(v_snd_1043_);
v___x_1064_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1065_ = lean_string_append(v___x_1063_, v___x_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath(lean_object* v_wsDir_1100_, lean_object* v_relPkgsDir_1101_, lean_object* v_relSrc_1102_, lean_object* v_dirName_1103_, uint8_t v_copy_1104_, uint8_t v_update_1105_){
_start:
{
if (v_copy_1104_ == 0)
{
lean_object* v___x_1107_; 
lean_dec_ref(v_dirName_1103_);
lean_dec_ref(v_relPkgsDir_1101_);
lean_dec_ref(v_wsDir_1100_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_relSrc_1102_);
return v___x_1107_;
}
else
{
lean_object* v_relDst_1108_; lean_object* v_dst_1109_; 
v_relDst_1108_ = l_Lake_joinRelative(v_relPkgsDir_1101_, v_dirName_1103_);
lean_inc_ref(v_relDst_1108_);
lean_inc_ref(v_wsDir_1100_);
v_dst_1109_ = l_Lake_joinRelative(v_wsDir_1100_, v_relDst_1108_);
if (v_update_1105_ == 0)
{
uint8_t v___x_1129_; 
v___x_1129_ = l_System_FilePath_pathExists(v_dst_1109_);
if (v___x_1129_ == 0)
{
goto v___jp_1110_;
}
else
{
lean_object* v___x_1130_; 
lean_dec_ref(v_dst_1109_);
lean_dec_ref(v_relSrc_1102_);
lean_dec_ref(v_wsDir_1100_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_relDst_1108_);
return v___x_1130_;
}
}
else
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lake_removeDirAllIfExists(v_dst_1109_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_dec_ref_known(v___x_1131_, 1);
goto v___jp_1110_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_dst_1109_);
lean_dec_ref(v_relDst_1108_);
lean_dec_ref(v_relSrc_1102_);
lean_dec_ref(v_wsDir_1100_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
v___jp_1110_:
{
lean_object* v_src_1111_; lean_object* v___x_1112_; 
v_src_1111_ = l_Lake_joinRelative(v_wsDir_1100_, v_relSrc_1102_);
v___x_1112_ = l_Lake_copyDirAll(v_src_1111_, v_dst_1109_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v___x_1112_, 0);
lean_dec(v_unused_1120_);
v___x_1114_ = v___x_1112_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v___x_1112_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_relDst_1108_);
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_relDst_1108_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v_relDst_1108_);
v_a_1121_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1112_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1112_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath___boxed(lean_object* v_wsDir_1140_, lean_object* v_relPkgsDir_1141_, lean_object* v_relSrc_1142_, lean_object* v_dirName_1143_, lean_object* v_copy_1144_, lean_object* v_update_1145_, lean_object* v_a_1146_){
_start:
{
uint8_t v_copy_boxed_1147_; uint8_t v_update_boxed_1148_; lean_object* v_res_1149_; 
v_copy_boxed_1147_ = lean_unbox(v_copy_1144_);
v_update_boxed_1148_ = lean_unbox(v_update_1145_);
v_res_1149_ = l___private_Lake_Load_Materialize_0__Lake_mkPath(v_wsDir_1140_, v_relPkgsDir_1141_, v_relSrc_1142_, v_dirName_1143_, v_copy_boxed_1147_, v_update_boxed_1148_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1151_, uint8_t v_inherited_1152_, lean_object* v_wsDir_1153_, lean_object* v_name_1154_, lean_object* v_relPkgDir_1155_, lean_object* v_remoteUrl_1156_, lean_object* v_src_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___y_1161_; lean_object* v_a_1162_; lean_object* v___f_1179_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v_val_1185_; lean_object* v_pkgDir_1201_; lean_object* v_a_1203_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_val_1239_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___f_1179_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_1155_);
v_pkgDir_1201_ = l_Lake_joinRelative(v_wsDir_1153_, v_relPkgDir_1155_);
v___x_1235_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_1201_);
v___x_1254_ = l_Lake_resolvePath(v_pkgDir_1201_);
v___x_1255_ = lean_string_utf8_byte_size(v___x_1254_);
v___x_1256_ = lean_nat_dec_eq(v___x_1255_, v___x_1236_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1254_);
v_val_1239_ = v___x_1257_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1258_; 
lean_dec_ref(v___x_1254_);
v___x_1258_ = lean_box(0);
v_val_1239_ = v___x_1258_;
goto v___jp_1238_;
}
v___jp_1160_:
{
lean_object* v_name_1163_; lean_object* v_scope_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1175_; 
v_name_1163_ = lean_ctor_get(v_dep_1151_, 0);
v_scope_1164_ = lean_ctor_get(v_dep_1151_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_dep_1151_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1176_ = lean_ctor_get(v_dep_1151_, 4);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_dep_1151_, 3);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_dep_1151_, 2);
lean_dec(v_unused_1178_);
v___x_1166_ = v_dep_1151_;
v_isShared_1167_ = v_isSharedCheck_1175_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_scope_1164_);
lean_inc(v_name_1163_);
lean_dec(v_dep_1151_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1175_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1168_ = l_Lake_defaultConfigFile;
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1170_, 0, v_name_1163_);
lean_ctor_set(v___x_1170_, 1, v_scope_1164_);
lean_ctor_set(v___x_1170_, 2, v___x_1168_);
lean_ctor_set(v___x_1170_, 3, v___x_1169_);
lean_ctor_set(v___x_1170_, 4, v_src_1157_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*5, v_inherited_1152_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 4, v___x_1170_);
lean_ctor_set(v___x_1166_, 3, v_a_1162_);
lean_ctor_set(v___x_1166_, 2, v_remoteUrl_1156_);
lean_ctor_set(v___x_1166_, 1, v_relPkgDir_1155_);
lean_ctor_set(v___x_1166_, 0, v___y_1161_);
v___x_1172_ = v___x_1166_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___y_1161_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_relPkgDir_1155_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_remoteUrl_1156_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_a_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
}
v___jp_1180_:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_array_get_size(v___y_1182_);
v___x_1187_ = lean_nat_dec_lt(v___y_1184_, v___x_1186_);
if (v___x_1187_ == 0)
{
v___y_1161_ = v___y_1181_;
v_a_1162_ = v_val_1185_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1819__overap_1191_; lean_object* v___x_1192_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1186_);
lean_inc_ref(v___y_1182_);
lean_inc_ref(v___y_1183_);
v___x_1819__overap_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1183_, v___f_1179_, v___y_1182_, v___x_1189_, v___x_1190_, v___x_1188_);
lean_inc_ref(v_a_1158_);
v___x_1192_ = lean_apply_2(v___x_1819__overap_1191_, v_a_1158_, lean_box(0));
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_dec_ref_known(v___x_1192_, 1);
v___y_1161_ = v___y_1181_;
v_a_1162_ = v_val_1185_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_val_1185_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_src_1157_);
lean_dec_ref(v_remoteUrl_1156_);
lean_dec_ref(v_relPkgDir_1155_);
lean_dec_ref(v_dep_1151_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
v___jp_1202_:
{
if (lean_obj_tag(v_a_1203_) == 1)
{
lean_object* v_val_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v_pkgDir_1201_);
lean_dec_ref(v_name_1154_);
v_val_1204_ = lean_ctor_get(v_a_1203_, 0);
lean_inc_n(v_val_1204_, 2);
lean_dec_ref_known(v_a_1203_, 1);
v___x_1205_ = l_Lake_defaultManifestFile;
v___x_1206_ = l_Lake_joinRelative(v_val_1204_, v___x_1205_);
v___x_1207_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1210_ = l_Lake_Manifest_load(v___x_1206_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 1);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
v___y_1181_ = v_val_1204_;
v___y_1182_ = v___x_1209_;
v___y_1183_ = v___x_1207_;
v___y_1184_ = v___x_1208_;
v_val_1185_ = v___x_1216_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
v_a_1219_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1210_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1210_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 0);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
v___y_1181_ = v_val_1204_;
v___y_1182_ = v___x_1209_;
v___y_1183_ = v___x_1207_;
v___y_1184_ = v___x_1208_;
v_val_1185_ = v___x_1224_;
goto v___jp_1180_;
}
}
}
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec(v_a_1203_);
lean_dec_ref(v_src_1157_);
lean_dec_ref(v_remoteUrl_1156_);
lean_dec_ref(v_relPkgDir_1155_);
lean_dec_ref(v_dep_1151_);
v___x_1227_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1228_ = lean_string_append(v_name_1154_, v___x_1227_);
v___x_1229_ = lean_string_append(v___x_1228_, v_pkgDir_1201_);
lean_dec_ref(v_pkgDir_1201_);
v___x_1230_ = 3;
v___x_1231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set_uint8(v___x_1231_, sizeof(void*)*1, v___x_1230_);
lean_inc_ref(v_a_1158_);
v___x_1232_ = lean_apply_2(v_a_1158_, v___x_1231_, lean_box(0));
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
}
v___jp_1238_:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1240_ == 0)
{
v_a_1203_ = v_val_1239_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1865__overap_1244_; lean_object* v___x_1245_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1865__overap_1244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1235_, v___f_1179_, v___x_1237_, v___x_1242_, v___x_1243_, v___x_1241_);
lean_inc_ref(v_a_1158_);
v___x_1245_ = lean_apply_2(v___x_1865__overap_1244_, v_a_1158_, lean_box(0));
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_dec_ref_known(v___x_1245_, 1);
v_a_1203_ = v_val_1239_;
goto v___jp_1202_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_val_1239_);
lean_dec_ref(v_pkgDir_1201_);
lean_dec_ref(v_src_1157_);
lean_dec_ref(v_remoteUrl_1156_);
lean_dec_ref(v_relPkgDir_1155_);
lean_dec_ref(v_name_1154_);
lean_dec_ref(v_dep_1151_);
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1259_, lean_object* v_inherited_1260_, lean_object* v_wsDir_1261_, lean_object* v_name_1262_, lean_object* v_relPkgDir_1263_, lean_object* v_remoteUrl_1264_, lean_object* v_src_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
uint8_t v_inherited_boxed_1268_; lean_object* v_res_1269_; 
v_inherited_boxed_1268_ = lean_unbox(v_inherited_1260_);
v_res_1269_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1259_, v_inherited_boxed_1268_, v_wsDir_1261_, v_name_1262_, v_relPkgDir_1263_, v_remoteUrl_1264_, v_src_1265_, v_a_1266_);
lean_dec_ref(v_a_1266_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1270_, lean_object* v_name_1271_, lean_object* v_repo_1272_, lean_object* v_url_1273_, lean_object* v_rev_x3f_1274_){
_start:
{
lean_object* v___y_1286_; uint8_t v_a_1287_; lean_object* v___y_1295_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v_a_1366_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v_val_1378_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; uint8_t v_val_1428_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v_a_1440_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v_a_1487_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1582_; uint8_t v_a_1583_; lean_object* v___y_1591_; uint8_t v_a_1592_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; uint8_t v_val_1603_; lean_object* v___y_1611_; uint8_t v___y_1612_; uint8_t v___y_1613_; lean_object* v___y_1618_; uint8_t v___y_1619_; uint8_t v___y_1620_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___y_1653_; uint8_t v___y_1654_; lean_object* v_a_1655_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; uint8_t v_val_1702_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v_a_1714_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v_a_1747_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; uint8_t v_a_1823_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v_a_1887_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v_a_1900_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_val_1915_; lean_object* v___y_1923_; lean_object* v___y_1924_; uint8_t v_a_1925_; lean_object* v___y_1934_; 
if (lean_obj_tag(v_rev_x3f_1274_) == 0)
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lake_Git_upstreamBranch;
v___y_1934_ = v___x_1943_;
goto v___jp_1933_;
}
else
{
lean_object* v_val_1944_; 
v_val_1944_ = lean_ctor_get(v_rev_x3f_1274_, 0);
lean_inc(v_val_1944_);
lean_dec_ref_known(v_rev_x3f_1274_, 1);
v___y_1934_ = v_val_1944_;
goto v___jp_1933_;
}
v___jp_1276_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
v___jp_1279_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
v___jp_1282_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
v___jp_1285_:
{
if (v_a_1287_ == 0)
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
goto v___jp_1276_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1288_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1289_ = lean_string_append(v_name_1271_, v___x_1288_);
v___x_1290_ = lean_string_append(v___x_1289_, v_repo_1272_);
lean_dec_ref(v_repo_1272_);
v___x_1291_ = 2;
v___x_1292_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1, v___x_1291_);
lean_inc_ref(v___y_1286_);
v___x_1293_ = lean_apply_2(v___y_1286_, v___x_1292_, lean_box(0));
goto v___jp_1276_;
}
}
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1298_ = l_Lake_GitRepo_gcAuto(v_repo_1272_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
v_a_1300_ = lean_ctor_get(v___x_1298_, 1);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1298_, 2);
v___x_1301_ = lean_array_get_size(v_a_1300_);
v___x_1302_ = lean_nat_dec_lt(v___x_1296_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec(v_a_1300_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_a_1299_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = lean_usize_of_nat(v___x_1301_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1300_, v___x_1305_, v___x_1306_, v___x_1304_, v___y_1295_);
lean_dec(v_a_1300_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1307_, 0);
lean_dec(v_unused_1315_);
v___x_1309_ = v___x_1307_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v___x_1307_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v_a_1299_);
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1299_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_dec(v_a_1299_);
return v___x_1307_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1298_, 1);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1298_, 2);
v___x_1317_ = lean_array_get_size(v_a_1316_);
v___x_1318_ = lean_nat_dec_lt(v___x_1296_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec(v_a_1316_);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1317_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1316_, v___x_1322_, v___x_1323_, v___x_1321_, v___y_1295_);
lean_dec(v_a_1316_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1324_, 0);
lean_dec(v_unused_1332_);
v___x_1326_ = v___x_1324_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v___x_1324_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 1);
lean_ctor_set(v___x_1326_, 0, v___x_1321_);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1321_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
return v___x_1324_;
}
}
}
}
v___jp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
lean_inc_ref(v___y_1334_);
v___x_1338_ = l_Lake_GitRepo_pruneRemote(v___y_1334_, v_repo_1272_, v___x_1337_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 1);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 2);
v___x_1340_ = lean_array_get_size(v_a_1339_);
v___x_1341_ = lean_nat_dec_lt(v___x_1336_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec(v_a_1339_);
v___y_1295_ = v___y_1335_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = lean_usize_of_nat(v___x_1340_);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1339_, v___x_1343_, v___x_1344_, v___x_1342_, v___y_1335_);
lean_dec(v_a_1339_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_dec_ref_known(v___x_1345_, 1);
v___y_1295_ = v___y_1335_;
goto v___jp_1294_;
}
else
{
lean_dec_ref(v_repo_1272_);
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
lean_dec_ref(v_repo_1272_);
v_a_1346_ = lean_ctor_get(v___x_1338_, 1);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1338_, 2);
v___x_1347_ = lean_array_get_size(v_a_1346_);
v___x_1348_ = lean_nat_dec_lt(v___x_1336_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_a_1346_);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1347_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1346_, v___x_1352_, v___x_1353_, v___x_1351_, v___y_1335_);
lean_dec(v_a_1346_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1354_, 0);
lean_dec(v_unused_1362_);
v___x_1356_ = v___x_1354_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_dec(v___x_1354_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 1);
lean_ctor_set(v___x_1356_, 0, v___x_1351_);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1351_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
return v___x_1354_;
}
}
}
}
v___jp_1363_:
{
if (v_a_1366_ == 0)
{
lean_dec_ref(v_name_1271_);
v___y_1334_ = v___y_1364_;
v___y_1335_ = v___y_1365_;
goto v___jp_1333_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1367_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1368_ = lean_string_append(v_name_1271_, v___x_1367_);
v___x_1369_ = lean_string_append(v___x_1368_, v_repo_1272_);
v___x_1370_ = 2;
v___x_1371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*1, v___x_1370_);
lean_inc_ref(v___y_1365_);
v___x_1372_ = lean_apply_2(v___y_1365_, v___x_1371_, lean_box(0));
v___y_1334_ = v___y_1364_;
v___y_1335_ = v___y_1365_;
goto v___jp_1333_;
}
}
v___jp_1373_:
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = lean_array_get_size(v___y_1377_);
v___x_1380_ = lean_nat_dec_lt(v___y_1376_, v___x_1379_);
if (v___x_1380_ == 0)
{
v___y_1364_ = v___y_1374_;
v___y_1365_ = v___y_1375_;
v_a_1366_ = v_val_1378_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = lean_usize_of_nat(v___x_1379_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1377_, v___x_1382_, v___x_1383_, v___x_1381_, v___y_1375_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec_ref_known(v___x_1384_, 1);
v___y_1364_ = v___y_1374_;
v___y_1365_ = v___y_1375_;
v_a_1366_ = v_val_1378_;
goto v___jp_1363_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1384_;
}
}
}
v___jp_1385_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1391_ = l_Lake_GitRepo_hasNoDiff(v_repo_1272_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = 1;
v___y_1374_ = v___y_1386_;
v___y_1375_ = v___y_1387_;
v___y_1376_ = v___x_1389_;
v___y_1377_ = v___x_1390_;
v_val_1378_ = v___x_1392_;
goto v___jp_1373_;
}
else
{
v___y_1374_ = v___y_1386_;
v___y_1375_ = v___y_1387_;
v___y_1376_ = v___x_1389_;
v___y_1377_ = v___x_1390_;
v_val_1378_ = v___y_1388_;
goto v___jp_1373_;
}
}
v___jp_1393_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1399_ = l_Lake_GitRepo_clean(v_repo_1272_, v___x_1398_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 1);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 2);
v___x_1401_ = lean_array_get_size(v_a_1400_);
v___x_1402_ = lean_nat_dec_lt(v___x_1397_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_dec(v_a_1400_);
v___y_1386_ = v___y_1394_;
v___y_1387_ = v___y_1395_;
v___y_1388_ = v___y_1396_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = lean_usize_of_nat(v___x_1401_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1400_, v___x_1404_, v___x_1405_, v___x_1403_, v___y_1395_);
lean_dec(v_a_1400_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec_ref_known(v___x_1406_, 1);
v___y_1386_ = v___y_1394_;
v___y_1387_ = v___y_1395_;
v___y_1388_ = v___y_1396_;
goto v___jp_1385_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1406_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1407_ = lean_ctor_get(v___x_1399_, 1);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1399_, 2);
v___x_1408_ = lean_array_get_size(v_a_1407_);
v___x_1409_ = lean_nat_dec_lt(v___x_1397_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec(v_a_1407_);
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1408_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1407_, v___x_1413_, v___x_1414_, v___x_1412_, v___y_1395_);
lean_dec(v_a_1407_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1423_);
v___x_1417_ = v___x_1415_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v___x_1415_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 1);
lean_ctor_set(v___x_1417_, 0, v___x_1412_);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1412_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
return v___x_1415_;
}
}
}
}
v___jp_1424_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_array_get_size(v___y_1427_);
v___x_1430_ = lean_nat_dec_lt(v___y_1425_, v___x_1429_);
if (v___x_1430_ == 0)
{
v___y_1286_ = v___y_1426_;
v_a_1287_ = v_val_1428_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1431_; size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = ((size_t)0ULL);
v___x_1433_ = lean_usize_of_nat(v___x_1429_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1427_, v___x_1432_, v___x_1433_, v___x_1431_, v___y_1426_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref_known(v___x_1434_, 1);
v___y_1286_ = v___y_1426_;
v_a_1287_ = v_val_1428_;
goto v___jp_1285_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1434_;
}
}
}
v___jp_1435_:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_1442_ = l_Option_instDecidableEq___redArg(v___x_1441_, v_a_1440_, v___y_1439_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1443_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1271_);
v___x_1444_ = lean_string_append(v_name_1271_, v___x_1443_);
v___x_1445_ = lean_string_append(v___x_1444_, v___y_1436_);
v___x_1446_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1447_ = lean_string_append(v___x_1445_, v___x_1446_);
v___x_1448_ = 1;
v___x_1449_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1, v___x_1448_);
lean_inc_ref(v___y_1438_);
v___x_1450_ = lean_apply_2(v___y_1438_, v___x_1449_, lean_box(0));
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1453_ = l_Lake_GitRepo_checkoutDetach(v___y_1436_, v_repo_1272_, v___x_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 2);
v___x_1455_ = lean_array_get_size(v_a_1454_);
v___x_1456_ = lean_nat_dec_lt(v___x_1451_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_dec(v_a_1454_);
v___y_1394_ = v___y_1437_;
v___y_1395_ = v___y_1438_;
v___y_1396_ = v___x_1442_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1457_ = lean_box(0);
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1455_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1454_, v___x_1458_, v___x_1459_, v___x_1457_, v___y_1438_);
lean_dec(v_a_1454_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec_ref_known(v___x_1460_, 1);
v___y_1394_ = v___y_1437_;
v___y_1395_ = v___y_1438_;
v___y_1396_ = v___x_1442_;
goto v___jp_1393_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1460_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1461_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1453_, 2);
v___x_1462_ = lean_array_get_size(v_a_1461_);
v___x_1463_ = lean_nat_dec_lt(v___x_1451_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec(v_a_1461_);
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = lean_box(0);
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1462_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1461_, v___x_1467_, v___x_1468_, v___x_1466_, v___y_1438_);
lean_dec(v_a_1461_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1469_, 0);
lean_dec(v_unused_1477_);
v___x_1471_ = v___x_1469_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v___x_1469_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 1);
lean_ctor_set(v___x_1471_, 0, v___x_1466_);
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1466_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
lean_dec_ref(v___y_1436_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1480_ = l_Lake_GitRepo_hasNoDiff(v_repo_1272_);
if (v___x_1480_ == 0)
{
v___y_1425_ = v___x_1478_;
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___x_1479_;
v_val_1428_ = v___x_1442_;
goto v___jp_1424_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = 0;
v___y_1425_ = v___x_1478_;
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___x_1479_;
v_val_1428_ = v___x_1481_;
goto v___jp_1424_;
}
}
}
v___jp_1482_:
{
if (lean_obj_tag(v_a_1487_) == 1)
{
lean_object* v_val_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
lean_dec_ref(v___y_1485_);
lean_dec_ref(v___y_1483_);
v_val_1488_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_val_1488_);
v___x_1489_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1490_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1272_);
v___x_1491_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1490_, v_repo_1272_);
v___x_1492_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1492_ == 0)
{
v___y_1436_ = v_val_1488_;
v___y_1437_ = v___y_1484_;
v___y_1438_ = v___y_1486_;
v___y_1439_ = v_a_1487_;
v_a_1440_ = v___x_1491_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1493_; size_t v___x_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = ((size_t)0ULL);
v___x_1495_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1489_, v___x_1494_, v___x_1495_, v___x_1493_, v___y_1486_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_dec_ref_known(v___x_1496_, 1);
v___y_1436_ = v_val_1488_;
v___y_1437_ = v___y_1484_;
v___y_1438_ = v___y_1486_;
v___y_1439_ = v_a_1487_;
v_a_1440_ = v___x_1491_;
goto v___jp_1435_;
}
else
{
lean_dec(v___x_1491_);
lean_dec(v_val_1488_);
lean_dec_ref_known(v_a_1487_, 1);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1496_;
}
}
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_a_1487_);
lean_dec_ref(v_repo_1272_);
v___x_1497_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_1498_ = lean_string_append(v_name_1271_, v___x_1497_);
v___x_1499_ = lean_string_append(v___x_1498_, v___y_1485_);
lean_dec_ref(v___y_1485_);
v___x_1500_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_1501_ = lean_string_append(v___x_1499_, v___x_1500_);
v___x_1502_ = lean_string_append(v___x_1501_, v___y_1483_);
lean_dec_ref(v___y_1483_);
v___x_1503_ = 3;
v___x_1504_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*1, v___x_1503_);
lean_inc_ref(v___y_1486_);
v___x_1505_ = lean_apply_2(v___y_1486_, v___x_1504_, lean_box(0));
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
v___jp_1508_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1513_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_1271_);
v___x_1514_ = lean_string_append(v_name_1271_, v___x_1513_);
v___x_1515_ = lean_string_append(v___x_1514_, v___y_1511_);
v___x_1516_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_1517_ = lean_string_append(v___x_1515_, v___x_1516_);
v___x_1518_ = lean_string_append(v___x_1517_, v___y_1509_);
v___x_1519_ = 1;
v___x_1520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set_uint8(v___x_1520_, sizeof(void*)*1, v___x_1519_);
lean_inc_ref(v___y_1512_);
v___x_1521_ = lean_apply_2(v___y_1512_, v___x_1520_, lean_box(0));
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_1511_);
lean_inc_ref(v___y_1510_);
lean_inc_ref(v_repo_1272_);
v___x_1524_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_1272_, v___y_1510_, v___y_1511_, v___x_1523_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v_a_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
v_a_1526_ = lean_ctor_get(v___x_1524_, 1);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1524_, 2);
v___x_1527_ = lean_array_get_size(v_a_1526_);
v___x_1528_ = lean_nat_dec_lt(v___x_1522_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_dec(v_a_1526_);
v___y_1483_ = v___y_1509_;
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___y_1511_;
v___y_1486_ = v___y_1512_;
v_a_1487_ = v_a_1525_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = ((size_t)0ULL);
v___x_1531_ = lean_usize_of_nat(v___x_1527_);
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1526_, v___x_1530_, v___x_1531_, v___x_1529_, v___y_1512_);
lean_dec(v_a_1526_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref_known(v___x_1532_, 1);
v___y_1483_ = v___y_1509_;
v___y_1484_ = v___y_1510_;
v___y_1485_ = v___y_1511_;
v___y_1486_ = v___y_1512_;
v_a_1487_ = v_a_1525_;
goto v___jp_1482_;
}
else
{
lean_dec(v_a_1525_);
lean_dec_ref(v___y_1511_);
lean_dec_ref(v___y_1509_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1532_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
lean_dec_ref(v___y_1511_);
lean_dec_ref(v___y_1509_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1533_ = lean_ctor_get(v___x_1524_, 1);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1524_, 2);
v___x_1534_ = lean_array_get_size(v_a_1533_);
v___x_1535_ = lean_nat_dec_lt(v___x_1522_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_a_1533_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_box(0);
v___x_1539_ = ((size_t)0ULL);
v___x_1540_ = lean_usize_of_nat(v___x_1534_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1533_, v___x_1539_, v___x_1540_, v___x_1538_, v___y_1512_);
lean_dec(v_a_1533_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v___x_1541_, 0);
lean_dec(v_unused_1549_);
v___x_1543_ = v___x_1541_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v___x_1541_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1538_);
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1538_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
return v___x_1541_;
}
}
}
}
v___jp_1550_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
lean_inc_ref(v___y_1551_);
lean_inc_ref(v___y_1552_);
v___x_1556_ = l_Lake_GitRepo_addRemote(v___y_1552_, v___y_1551_, v_repo_1272_, v___x_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 2);
v___x_1558_ = lean_array_get_size(v_a_1557_);
v___x_1559_ = lean_nat_dec_lt(v___x_1554_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_dec(v_a_1557_);
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1552_;
v___y_1511_ = v___y_1553_;
v___y_1512_ = v_a_1270_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1560_; size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1560_ = lean_box(0);
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = lean_usize_of_nat(v___x_1558_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1557_, v___x_1561_, v___x_1562_, v___x_1560_, v_a_1270_);
lean_dec(v_a_1557_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_dec_ref_known(v___x_1563_, 1);
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1552_;
v___y_1511_ = v___y_1553_;
v___y_1512_ = v_a_1270_;
goto v___jp_1508_;
}
else
{
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___y_1551_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___y_1551_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1564_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1556_, 2);
v___x_1565_ = lean_array_get_size(v_a_1564_);
v___x_1566_ = lean_nat_dec_lt(v___x_1554_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec(v_a_1564_);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
else
{
lean_object* v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = lean_usize_of_nat(v___x_1565_);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1564_, v___x_1570_, v___x_1571_, v___x_1569_, v_a_1270_);
lean_dec(v_a_1564_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v___x_1572_, 0);
lean_dec(v_unused_1580_);
v___x_1574_ = v___x_1572_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v___x_1572_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 0, v___x_1569_);
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1569_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
else
{
return v___x_1572_;
}
}
}
}
v___jp_1581_:
{
if (v_a_1583_ == 0)
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
goto v___jp_1279_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1584_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1585_ = lean_string_append(v_name_1271_, v___x_1584_);
v___x_1586_ = lean_string_append(v___x_1585_, v_repo_1272_);
lean_dec_ref(v_repo_1272_);
v___x_1587_ = 2;
v___x_1588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*1, v___x_1587_);
lean_inc_ref(v___y_1582_);
v___x_1589_ = lean_apply_2(v___y_1582_, v___x_1588_, lean_box(0));
goto v___jp_1279_;
}
}
v___jp_1590_:
{
if (v_a_1592_ == 0)
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
goto v___jp_1282_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1593_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1594_ = lean_string_append(v_name_1271_, v___x_1593_);
v___x_1595_ = lean_string_append(v___x_1594_, v_repo_1272_);
lean_dec_ref(v_repo_1272_);
v___x_1596_ = 2;
v___x_1597_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*1, v___x_1596_);
lean_inc_ref(v___y_1591_);
v___x_1598_ = lean_apply_2(v___y_1591_, v___x_1597_, lean_box(0));
goto v___jp_1282_;
}
}
v___jp_1599_:
{
lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = lean_array_get_size(v___y_1602_);
v___x_1605_ = lean_nat_dec_lt(v___y_1600_, v___x_1604_);
if (v___x_1605_ == 0)
{
v___y_1582_ = v___y_1601_;
v_a_1583_ = v_val_1603_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = lean_usize_of_nat(v___x_1604_);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1602_, v___x_1607_, v___x_1608_, v___x_1606_, v___y_1601_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_dec_ref_known(v___x_1609_, 1);
v___y_1582_ = v___y_1601_;
v_a_1583_ = v_val_1603_;
goto v___jp_1581_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1609_;
}
}
}
v___jp_1610_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1616_ = l_Lake_GitRepo_hasNoDiff(v_repo_1272_);
if (v___x_1616_ == 0)
{
v___y_1600_ = v___x_1614_;
v___y_1601_ = v___y_1611_;
v___y_1602_ = v___x_1615_;
v_val_1603_ = v___y_1613_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___x_1614_;
v___y_1601_ = v___y_1611_;
v___y_1602_ = v___x_1615_;
v_val_1603_ = v___y_1612_;
goto v___jp_1599_;
}
}
v___jp_1617_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1623_ = l_Lake_GitRepo_clean(v_repo_1272_, v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 1);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 2);
v___x_1625_ = lean_array_get_size(v_a_1624_);
v___x_1626_ = lean_nat_dec_lt(v___x_1621_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_dec(v_a_1624_);
v___y_1611_ = v___y_1618_;
v___y_1612_ = v___y_1620_;
v___y_1613_ = v___y_1619_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1627_ = lean_box(0);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = lean_usize_of_nat(v___x_1625_);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1624_, v___x_1628_, v___x_1629_, v___x_1627_, v___y_1618_);
lean_dec(v_a_1624_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_dec_ref_known(v___x_1630_, 1);
v___y_1611_ = v___y_1618_;
v___y_1612_ = v___y_1620_;
v___y_1613_ = v___y_1619_;
goto v___jp_1610_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1630_;
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1631_ = lean_ctor_get(v___x_1623_, 1);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1623_, 2);
v___x_1632_ = lean_array_get_size(v_a_1631_);
v___x_1633_ = lean_nat_dec_lt(v___x_1621_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v_a_1631_);
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
v___x_1636_ = lean_box(0);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = lean_usize_of_nat(v___x_1632_);
v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1631_, v___x_1637_, v___x_1638_, v___x_1636_, v___y_1618_);
lean_dec(v_a_1631_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1639_, 0);
lean_dec(v_unused_1647_);
v___x_1641_ = v___x_1639_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v___x_1639_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 1);
lean_ctor_set(v___x_1641_, 0, v___x_1636_);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1636_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
return v___x_1639_;
}
}
}
}
v___jp_1648_:
{
if (lean_obj_tag(v_a_1655_) == 0)
{
v___y_1509_ = v___y_1649_;
v___y_1510_ = v___y_1650_;
v___y_1511_ = v___y_1651_;
v___y_1512_ = v___y_1652_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1696_; 
lean_dec_ref(v___y_1649_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_a_1655_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v_a_1655_, 0);
lean_dec(v_unused_1697_);
v___x_1657_ = v_a_1655_;
v_isShared_1658_ = v_isSharedCheck_1696_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v_a_1655_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1696_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1659_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1271_);
v___x_1660_ = lean_string_append(v_name_1271_, v___x_1659_);
v___x_1661_ = lean_string_append(v___x_1660_, v___y_1651_);
v___x_1662_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1663_ = lean_string_append(v___x_1661_, v___x_1662_);
v___x_1664_ = 1;
v___x_1665_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*1, v___x_1664_);
lean_inc_ref(v___y_1652_);
v___x_1666_ = lean_apply_2(v___y_1652_, v___x_1665_, lean_box(0));
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1669_ = l_Lake_GitRepo_checkoutDetach(v___y_1651_, v_repo_1272_, v___x_1668_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
lean_del_object(v___x_1657_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 1);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 2);
v___x_1671_ = lean_array_get_size(v_a_1670_);
v___x_1672_ = lean_nat_dec_lt(v___x_1667_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_dec(v_a_1670_);
v___y_1618_ = v___y_1652_;
v___y_1619_ = v___y_1654_;
v___y_1620_ = v___y_1653_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1673_; size_t v___x_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = lean_box(0);
v___x_1674_ = ((size_t)0ULL);
v___x_1675_ = lean_usize_of_nat(v___x_1671_);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1670_, v___x_1674_, v___x_1675_, v___x_1673_, v___y_1652_);
lean_dec(v_a_1670_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_dec_ref_known(v___x_1676_, 1);
v___y_1618_ = v___y_1652_;
v___y_1619_ = v___y_1654_;
v___y_1620_ = v___y_1653_;
goto v___jp_1617_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1677_ = lean_ctor_get(v___x_1669_, 1);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1669_, 2);
v___x_1678_ = lean_array_get_size(v_a_1677_);
v___x_1679_ = lean_nat_dec_lt(v___x_1667_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
lean_dec(v_a_1677_);
v___x_1680_ = lean_box(0);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1680_);
v___x_1682_ = v___x_1657_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
else
{
lean_object* v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
lean_del_object(v___x_1657_);
v___x_1684_ = lean_box(0);
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = lean_usize_of_nat(v___x_1678_);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1677_, v___x_1685_, v___x_1686_, v___x_1684_, v___y_1652_);
lean_dec(v_a_1677_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1687_, 0);
lean_dec(v_unused_1695_);
v___x_1689_ = v___x_1687_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_dec(v___x_1687_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 1);
lean_ctor_set(v___x_1689_, 0, v___x_1684_);
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1684_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
return v___x_1687_;
}
}
}
}
}
}
v___jp_1698_:
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = lean_array_get_size(v___y_1700_);
v___x_1704_ = lean_nat_dec_lt(v___y_1699_, v___x_1703_);
if (v___x_1704_ == 0)
{
v___y_1591_ = v___y_1701_;
v_a_1592_ = v_val_1702_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = lean_box(0);
v___x_1706_ = ((size_t)0ULL);
v___x_1707_ = lean_usize_of_nat(v___x_1703_);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1700_, v___x_1706_, v___x_1707_, v___x_1705_, v___y_1701_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_dec_ref_known(v___x_1708_, 1);
v___y_1591_ = v___y_1701_;
v_a_1592_ = v_val_1702_;
goto v___jp_1590_;
}
else
{
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1708_;
}
}
}
v___jp_1709_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1715_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_1712_);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___y_1712_);
v___x_1717_ = l_Option_instDecidableEq___redArg(v___x_1715_, v_a_1714_, v___x_1716_);
if (v___x_1717_ == 0)
{
uint8_t v___x_1718_; 
v___x_1718_ = l_Lake_GitRev_isFullSha1(v___y_1712_);
if (v___x_1718_ == 0)
{
v___y_1509_ = v___y_1710_;
v___y_1510_ = v___y_1711_;
v___y_1511_ = v___y_1712_;
v___y_1512_ = v___y_1713_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1719_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
lean_inc_ref(v___y_1712_);
v___x_1720_ = l_Lake_GitRepo_findCommit_x3f(v___y_1712_, v_repo_1272_);
v___x_1721_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1721_ == 0)
{
v___y_1649_ = v___y_1710_;
v___y_1650_ = v___y_1711_;
v___y_1651_ = v___y_1712_;
v___y_1652_ = v___y_1713_;
v___y_1653_ = v___x_1717_;
v___y_1654_ = v___x_1718_;
v_a_1655_ = v___x_1720_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1722_; size_t v___x_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1719_, v___x_1723_, v___x_1724_, v___x_1722_, v___y_1713_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_dec_ref_known(v___x_1725_, 1);
v___y_1649_ = v___y_1710_;
v___y_1650_ = v___y_1711_;
v___y_1651_ = v___y_1712_;
v___y_1652_ = v___y_1713_;
v___y_1653_ = v___x_1717_;
v___y_1654_ = v___x_1718_;
v_a_1655_ = v___x_1720_;
goto v___jp_1648_;
}
else
{
lean_dec(v___x_1720_);
lean_dec_ref(v___y_1712_);
lean_dec_ref(v___y_1710_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1725_;
}
}
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
lean_dec_ref(v___y_1712_);
lean_dec_ref(v___y_1710_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1728_ = l_Lake_GitRepo_hasNoDiff(v_repo_1272_);
if (v___x_1728_ == 0)
{
v___y_1699_ = v___x_1726_;
v___y_1700_ = v___x_1727_;
v___y_1701_ = v___y_1713_;
v_val_1702_ = v___x_1717_;
goto v___jp_1698_;
}
else
{
uint8_t v___x_1729_; 
v___x_1729_ = 0;
v___y_1699_ = v___x_1726_;
v___y_1700_ = v___x_1727_;
v___y_1701_ = v___y_1713_;
v_val_1702_ = v___x_1729_;
goto v___jp_1698_;
}
}
}
v___jp_1730_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1735_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1736_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1272_);
v___x_1737_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1736_, v_repo_1272_);
v___x_1738_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1738_ == 0)
{
v___y_1710_ = v___y_1731_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v___y_1733_;
v___y_1713_ = v___y_1734_;
v_a_1714_ = v___x_1737_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1735_, v___x_1740_, v___x_1741_, v___x_1739_, v___y_1734_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_dec_ref_known(v___x_1742_, 1);
v___y_1710_ = v___y_1731_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v___y_1733_;
v___y_1713_ = v___y_1734_;
v_a_1714_ = v___x_1737_;
goto v___jp_1709_;
}
else
{
lean_dec(v___x_1737_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1742_;
}
}
}
v___jp_1743_:
{
if (lean_obj_tag(v_a_1747_) == 1)
{
lean_object* v_val_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1791_; 
v_val_1748_ = lean_ctor_get(v_a_1747_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_a_1747_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1750_ = v_a_1747_;
v_isShared_1751_ = v_isSharedCheck_1791_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_val_1748_);
lean_dec(v_a_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1791_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_string_dec_eq(v_val_1748_, v___y_1744_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1753_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_1271_);
v___x_1754_ = lean_string_append(v_name_1271_, v___x_1753_);
v___x_1755_ = lean_string_append(v___x_1754_, v_val_1748_);
lean_dec(v_val_1748_);
v___x_1756_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_1757_ = lean_string_append(v___x_1755_, v___x_1756_);
v___x_1758_ = lean_string_append(v___x_1757_, v___y_1744_);
v___x_1759_ = 1;
v___x_1760_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*1, v___x_1759_);
lean_inc_ref(v_a_1270_);
v___x_1761_ = lean_apply_2(v_a_1270_, v___x_1760_, lean_box(0));
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
lean_inc_ref(v___y_1744_);
lean_inc_ref(v___y_1745_);
v___x_1764_ = l_Lake_GitRepo_setRemoteUrl(v___y_1745_, v___y_1744_, v_repo_1272_, v___x_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
lean_del_object(v___x_1750_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 1);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 2);
v___x_1766_ = lean_array_get_size(v_a_1765_);
v___x_1767_ = lean_nat_dec_lt(v___x_1762_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_dec(v_a_1765_);
v___y_1731_ = v___y_1744_;
v___y_1732_ = v___y_1745_;
v___y_1733_ = v___y_1746_;
v___y_1734_ = v_a_1270_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = ((size_t)0ULL);
v___x_1770_ = lean_usize_of_nat(v___x_1766_);
v___x_1771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1765_, v___x_1769_, v___x_1770_, v___x_1768_, v_a_1270_);
lean_dec(v_a_1765_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_dec_ref_known(v___x_1771_, 1);
v___y_1731_ = v___y_1744_;
v___y_1732_ = v___y_1745_;
v___y_1733_ = v___y_1746_;
v___y_1734_ = v_a_1270_;
goto v___jp_1730_;
}
else
{
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1771_;
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1772_ = lean_ctor_get(v___x_1764_, 1);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1764_, 2);
v___x_1773_ = lean_array_get_size(v_a_1772_);
v___x_1774_ = lean_nat_dec_lt(v___x_1762_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
lean_dec(v_a_1772_);
v___x_1775_ = lean_box(0);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1775_);
v___x_1777_ = v___x_1750_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
else
{
lean_object* v___x_1779_; size_t v___x_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
lean_del_object(v___x_1750_);
v___x_1779_ = lean_box(0);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = lean_usize_of_nat(v___x_1773_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1772_, v___x_1780_, v___x_1781_, v___x_1779_, v_a_1270_);
lean_dec(v_a_1772_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v___x_1782_, 0);
lean_dec(v_unused_1790_);
v___x_1784_ = v___x_1782_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_dec(v___x_1782_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 1);
lean_ctor_set(v___x_1784_, 0, v___x_1779_);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1779_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
else
{
return v___x_1782_;
}
}
}
}
else
{
lean_del_object(v___x_1750_);
lean_dec(v_val_1748_);
v___y_1731_ = v___y_1744_;
v___y_1732_ = v___y_1745_;
v___y_1733_ = v___y_1746_;
v___y_1734_ = v_a_1270_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v_a_1747_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
lean_inc_ref(v___y_1744_);
lean_inc_ref(v___y_1745_);
v___x_1794_ = l_Lake_GitRepo_addRemote(v___y_1745_, v___y_1744_, v_repo_1272_, v___x_1793_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 1);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 2);
v___x_1796_ = lean_array_get_size(v_a_1795_);
v___x_1797_ = lean_nat_dec_lt(v___x_1792_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec(v_a_1795_);
v___y_1731_ = v___y_1744_;
v___y_1732_ = v___y_1745_;
v___y_1733_ = v___y_1746_;
v___y_1734_ = v_a_1270_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1798_; size_t v___x_1799_; size_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = lean_box(0);
v___x_1799_ = ((size_t)0ULL);
v___x_1800_ = lean_usize_of_nat(v___x_1796_);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1795_, v___x_1799_, v___x_1800_, v___x_1798_, v_a_1270_);
lean_dec(v_a_1795_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_dec_ref_known(v___x_1801_, 1);
v___y_1731_ = v___y_1744_;
v___y_1732_ = v___y_1745_;
v___y_1733_ = v___y_1746_;
v___y_1734_ = v_a_1270_;
goto v___jp_1730_;
}
else
{
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1801_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1802_ = lean_ctor_get(v___x_1794_, 1);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1794_, 2);
v___x_1803_ = lean_array_get_size(v_a_1802_);
v___x_1804_ = lean_nat_dec_lt(v___x_1792_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v_a_1802_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = lean_box(0);
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_of_nat(v___x_1803_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1802_, v___x_1808_, v___x_1809_, v___x_1807_, v_a_1270_);
lean_dec(v_a_1802_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v___x_1810_, 0);
lean_dec(v_unused_1818_);
v___x_1812_ = v___x_1810_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_dec(v___x_1810_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set_tag(v___x_1812_, 1);
lean_ctor_set(v___x_1812_, 0, v___x_1807_);
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1807_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
return v___x_1810_;
}
}
}
}
}
v___jp_1819_:
{
if (v_a_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1824_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_1271_);
v___x_1825_ = lean_string_append(v_name_1271_, v___x_1824_);
v___x_1826_ = 1;
v___x_1827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*1, v___x_1826_);
lean_inc_ref(v_a_1270_);
v___x_1828_ = lean_apply_2(v_a_1270_, v___x_1827_, lean_box(0));
lean_inc_ref(v_repo_1272_);
v___x_1829_ = l_IO_FS_createDirAll(v_repo_1272_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1862_; 
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1863_);
v___x_1831_ = v___x_1829_;
v_isShared_1832_ = v_isSharedCheck_1862_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1862_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1834_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
v___x_1835_ = l_Lake_GitRepo_quietInit(v_repo_1272_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
lean_del_object(v___x_1831_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 1);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 2);
v___x_1837_ = lean_array_get_size(v_a_1836_);
v___x_1838_ = lean_nat_dec_lt(v___x_1833_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_dec(v_a_1836_);
v___y_1551_ = v___y_1820_;
v___y_1552_ = v___y_1821_;
v___y_1553_ = v___y_1822_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; lean_object* v___x_1842_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = ((size_t)0ULL);
v___x_1841_ = lean_usize_of_nat(v___x_1837_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1836_, v___x_1840_, v___x_1841_, v___x_1839_, v_a_1270_);
lean_dec(v_a_1836_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_dec_ref_known(v___x_1842_, 1);
v___y_1551_ = v___y_1820_;
v___y_1552_ = v___y_1821_;
v___y_1553_ = v___y_1822_;
goto v___jp_1550_;
}
else
{
lean_dec_ref(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1842_;
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
lean_dec_ref(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1843_ = lean_ctor_get(v___x_1835_, 1);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1835_, 2);
v___x_1844_ = lean_array_get_size(v_a_1843_);
v___x_1845_ = lean_nat_dec_lt(v___x_1833_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
lean_dec(v_a_1843_);
v___x_1846_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 1);
lean_ctor_set(v___x_1831_, 0, v___x_1846_);
v___x_1848_ = v___x_1831_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
else
{
lean_object* v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
lean_del_object(v___x_1831_);
v___x_1850_ = lean_box(0);
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = lean_usize_of_nat(v___x_1844_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1843_, v___x_1851_, v___x_1852_, v___x_1850_, v_a_1270_);
lean_dec(v_a_1843_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1853_, 0);
lean_dec(v_unused_1861_);
v___x_1855_ = v___x_1853_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_dec(v___x_1853_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 1);
lean_ctor_set(v___x_1855_, 0, v___x_1850_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1850_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
return v___x_1853_;
}
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
v_a_1864_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1866_ = v___x_1829_;
v_isShared_1867_ = v_isSharedCheck_1876_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1829_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1876_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1868_ = lean_io_error_to_string(v_a_1864_);
v___x_1869_ = 3;
v___x_1870_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set_uint8(v___x_1870_, sizeof(void*)*1, v___x_1869_);
lean_inc_ref(v_a_1270_);
v___x_1871_ = lean_apply_2(v_a_1270_, v___x_1870_, lean_box(0));
v___x_1872_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1872_);
v___x_1874_ = v___x_1866_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1877_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1272_);
lean_inc_ref(v___y_1821_);
v___x_1878_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_1821_, v_repo_1272_);
v___x_1879_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1879_ == 0)
{
v___y_1744_ = v___y_1820_;
v___y_1745_ = v___y_1821_;
v___y_1746_ = v___y_1822_;
v_a_1747_ = v___x_1878_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1880_; size_t v___x_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = ((size_t)0ULL);
v___x_1882_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1877_, v___x_1881_, v___x_1882_, v___x_1880_, v_a_1270_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_dec_ref_known(v___x_1883_, 1);
v___y_1744_ = v___y_1820_;
v___y_1745_ = v___y_1821_;
v___y_1746_ = v___y_1822_;
v_a_1747_ = v___x_1878_;
goto v___jp_1743_;
}
else
{
lean_dec(v___x_1878_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1883_;
}
}
}
}
v___jp_1884_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1888_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1889_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_1272_);
v___x_1890_ = l_System_FilePath_join(v_repo_1272_, v___x_1889_);
v___x_1891_ = l_System_FilePath_pathExists(v___x_1890_);
lean_dec_ref(v___x_1890_);
v___x_1892_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1892_ == 0)
{
v___y_1820_ = v_a_1887_;
v___y_1821_ = v___y_1885_;
v___y_1822_ = v___y_1886_;
v_a_1823_ = v___x_1891_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = ((size_t)0ULL);
v___x_1895_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1888_, v___x_1894_, v___x_1895_, v___x_1893_, v_a_1270_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_dec_ref_known(v___x_1896_, 1);
v___y_1820_ = v_a_1887_;
v___y_1821_ = v___y_1885_;
v___y_1822_ = v___y_1886_;
v_a_1823_ = v___x_1891_;
goto v___jp_1819_;
}
else
{
lean_dec_ref(v_a_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1896_;
}
}
}
v___jp_1897_:
{
if (lean_obj_tag(v_a_1900_) == 1)
{
lean_object* v_val_1901_; 
lean_dec_ref(v_url_1273_);
v_val_1901_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v_a_1900_, 1);
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v_a_1887_ = v_val_1901_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_a_1900_);
lean_dec_ref(v___y_1899_);
lean_dec_ref(v_repo_1272_);
v___x_1902_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_1903_ = lean_string_append(v_name_1271_, v___x_1902_);
v___x_1904_ = lean_string_append(v___x_1903_, v_url_1273_);
lean_dec_ref(v_url_1273_);
v___x_1905_ = 3;
v___x_1906_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*1, v___x_1905_);
lean_inc_ref(v_a_1270_);
v___x_1907_ = lean_apply_2(v_a_1270_, v___x_1906_, lean_box(0));
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
}
v___jp_1910_:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = lean_array_get_size(v___y_1914_);
v___x_1917_ = lean_nat_dec_lt(v___y_1913_, v___x_1916_);
if (v___x_1917_ == 0)
{
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v_a_1900_ = v_val_1915_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1918_; size_t v___x_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = lean_usize_of_nat(v___x_1916_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1914_, v___x_1919_, v___x_1920_, v___x_1918_, v_a_1270_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_dec_ref_known(v___x_1921_, 1);
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v_a_1900_ = v_val_1915_;
goto v___jp_1897_;
}
else
{
lean_dec(v_val_1915_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v_url_1273_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1921_;
}
}
}
v___jp_1922_:
{
if (v_a_1925_ == 0)
{
v___y_1885_ = v___y_1923_;
v___y_1886_ = v___y_1924_;
v_a_1887_ = v_url_1273_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_1273_);
v___x_1928_ = l_Lake_resolvePath(v_url_1273_);
v___x_1929_ = lean_string_utf8_byte_size(v___x_1928_);
v___x_1930_ = lean_nat_dec_eq(v___x_1929_, v___x_1926_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1928_);
v___y_1911_ = v___y_1923_;
v___y_1912_ = v___y_1924_;
v___y_1913_ = v___x_1926_;
v___y_1914_ = v___x_1927_;
v_val_1915_ = v___x_1931_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1932_; 
lean_dec_ref(v___x_1928_);
v___x_1932_ = lean_box(0);
v___y_1911_ = v___y_1923_;
v___y_1912_ = v___y_1924_;
v___y_1913_ = v___x_1926_;
v___y_1914_ = v___x_1927_;
v_val_1915_ = v___x_1932_;
goto v___jp_1910_;
}
}
}
v___jp_1933_:
{
lean_object* v_remote_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; uint8_t v___x_1938_; 
v_remote_1935_ = l_Lake_Git_defaultRemote;
v___x_1936_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1937_ = l_System_FilePath_pathExists(v_url_1273_);
v___x_1938_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1938_ == 0)
{
v___y_1923_ = v_remote_1935_;
v___y_1924_ = v___y_1934_;
v_a_1925_ = v___x_1937_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1939_; size_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1936_, v___x_1940_, v___x_1941_, v___x_1939_, v_a_1270_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_dec_ref_known(v___x_1942_, 1);
v___y_1923_ = v_remote_1935_;
v___y_1924_ = v___y_1934_;
v_a_1925_ = v___x_1937_;
goto v___jp_1922_;
}
else
{
lean_dec_ref(v___y_1934_);
lean_dec_ref(v_url_1273_);
lean_dec_ref(v_repo_1272_);
lean_dec_ref(v_name_1271_);
return v___x_1942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1945_, lean_object* v_name_1946_, lean_object* v_repo_1947_, lean_object* v_url_1948_, lean_object* v_rev_x3f_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1945_, v_name_1946_, v_repo_1947_, v_url_1948_, v_rev_x3f_1949_);
lean_dec_ref(v_a_1945_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1952_, uint8_t v_inherited_1953_, lean_object* v_lakeEnv_1954_, lean_object* v_wsDir_1955_, lean_object* v_name_1956_, lean_object* v_relPkgDir_1957_, lean_object* v_gitUrl_1958_, lean_object* v_remoteUrl_1959_, lean_object* v_inputRev_x3f_1960_, lean_object* v_subDir_x3f_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_pkgUrlMap_1964_; lean_object* v_name_1965_; lean_object* v_scope_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2142_; 
v_pkgUrlMap_1964_ = lean_ctor_get(v_lakeEnv_1954_, 5);
v_name_1965_ = lean_ctor_get(v_dep_1952_, 0);
v_scope_1966_ = lean_ctor_get(v_dep_1952_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_dep_1952_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; lean_object* v_unused_2144_; lean_object* v_unused_2145_; 
v_unused_2143_ = lean_ctor_get(v_dep_1952_, 4);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_dep_1952_, 3);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_dep_1952_, 2);
lean_dec(v_unused_2145_);
v___x_1968_ = v_dep_1952_;
v_isShared_1969_ = v_isSharedCheck_2142_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_scope_1966_);
lean_inc(v_name_1965_);
lean_dec(v_dep_1952_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2142_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v_a_1974_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_val_1988_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v_a_2007_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v_val_2044_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2073_; lean_object* v_a_2074_; lean_object* v_gitDir_2077_; lean_object* v___y_2079_; lean_object* v___x_2140_; 
lean_inc_ref(v_relPkgDir_1957_);
lean_inc_ref(v_wsDir_1955_);
v_gitDir_2077_ = l_Lake_joinRelative(v_wsDir_1955_, v_relPkgDir_1957_);
v___x_2140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_1964_, v_name_1965_);
if (lean_obj_tag(v___x_2140_) == 0)
{
v___y_2079_ = v_gitUrl_1958_;
goto v___jp_2078_;
}
else
{
lean_object* v_val_2141_; 
lean_dec_ref(v_gitUrl_1958_);
v_val_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___y_2079_ = v_val_2141_;
goto v___jp_2078_;
}
v___jp_1970_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1975_ = l_Lake_defaultConfigFile;
v___x_1976_ = lean_box(0);
v___x_1977_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1977_, 0, v_name_1965_);
lean_ctor_set(v___x_1977_, 1, v_scope_1966_);
lean_ctor_set(v___x_1977_, 2, v___x_1975_);
lean_ctor_set(v___x_1977_, 3, v___x_1976_);
lean_ctor_set(v___x_1977_, 4, v___y_1971_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*5, v_inherited_1953_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_1977_);
lean_ctor_set(v___x_1968_, 3, v_a_1974_);
lean_ctor_set(v___x_1968_, 2, v_remoteUrl_1959_);
lean_ctor_set(v___x_1968_, 1, v___y_1972_);
lean_ctor_set(v___x_1968_, 0, v___y_1973_);
v___x_1979_ = v___x_1968_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___y_1973_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___y_1972_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_remoteUrl_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_a_1974_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
v___jp_1982_:
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = lean_array_get_size(v___y_1983_);
v___x_1990_ = lean_nat_dec_lt(v___y_1984_, v___x_1989_);
if (v___x_1990_ == 0)
{
v___y_1971_ = v___y_1985_;
v___y_1972_ = v___y_1986_;
v___y_1973_ = v___y_1987_;
v_a_1974_ = v_val_1988_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = lean_box(0);
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = lean_usize_of_nat(v___x_1989_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1983_, v___x_1992_, v___x_1993_, v___x_1991_, v_a_1962_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_dec_ref_known(v___x_1994_, 1);
v___y_1971_ = v___y_1985_;
v___y_1972_ = v___y_1986_;
v___y_1973_ = v___y_1987_;
v_a_1974_ = v_val_1988_;
goto v___jp_1970_;
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_val_1988_);
lean_dec_ref(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1966_);
lean_dec(v_name_1965_);
lean_dec_ref(v_remoteUrl_1959_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
v___jp_2003_:
{
if (lean_obj_tag(v_a_2007_) == 1)
{
lean_object* v_val_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec_ref(v___y_2006_);
lean_dec_ref(v_name_1956_);
v_val_2008_ = lean_ctor_get(v_a_2007_, 0);
lean_inc_n(v_val_2008_, 2);
lean_dec_ref_known(v_a_2007_, 1);
v___x_2009_ = l_Lake_defaultManifestFile;
v___x_2010_ = l_Lake_joinRelative(v_val_2008_, v___x_2009_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2013_ = l_Lake_Manifest_load(v___x_2010_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 1);
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
v___y_1983_ = v___x_2012_;
v___y_1984_ = v___x_2011_;
v___y_1985_ = v___y_2004_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v_val_2008_;
v_val_1988_ = v___x_2019_;
goto v___jp_1982_;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2013_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2013_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set_tag(v___x_2024_, 0);
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
v___y_1983_ = v___x_2012_;
v___y_1984_ = v___x_2011_;
v___y_1985_ = v___y_2004_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v_val_2008_;
v_val_1988_ = v___x_2027_;
goto v___jp_1982_;
}
}
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v_a_2007_);
lean_dec_ref(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1966_);
lean_dec(v_name_1965_);
lean_dec_ref(v_remoteUrl_1959_);
v___x_2030_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2031_ = lean_string_append(v_name_1956_, v___x_2030_);
v___x_2032_ = lean_string_append(v___x_2031_, v___y_2006_);
lean_dec_ref(v___y_2006_);
v___x_2033_ = 3;
v___x_2034_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*1, v___x_2033_);
lean_inc_ref(v_a_1962_);
v___x_2035_ = lean_apply_2(v_a_1962_, v___x_2034_, lean_box(0));
v___x_2036_ = lean_box(0);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
v___jp_2038_:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = lean_array_get_size(v___y_2039_);
v___x_2046_ = lean_nat_dec_lt(v___y_2043_, v___x_2045_);
if (v___x_2046_ == 0)
{
v___y_2004_ = v___y_2040_;
v___y_2005_ = v___y_2041_;
v___y_2006_ = v___y_2042_;
v_a_2007_ = v_val_2044_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = lean_usize_of_nat(v___x_2045_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2039_, v___x_2048_, v___x_2049_, v___x_2047_, v_a_1962_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_dec_ref_known(v___x_2050_, 1);
v___y_2004_ = v___y_2040_;
v___y_2005_ = v___y_2041_;
v___y_2006_ = v___y_2042_;
v_a_2007_ = v_val_2044_;
goto v___jp_2003_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_val_2044_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1966_);
lean_dec(v_name_1965_);
lean_dec_ref(v_remoteUrl_1959_);
lean_dec_ref(v_name_1956_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
v___jp_2059_:
{
lean_object* v___x_2063_; lean_object* v_pkgDir_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2063_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2063_, 0, v___y_2061_);
lean_ctor_set(v___x_2063_, 1, v___y_2060_);
lean_ctor_set(v___x_2063_, 2, v_inputRev_x3f_1960_);
lean_ctor_set(v___x_2063_, 3, v_subDir_x3f_1961_);
lean_inc_ref(v___y_2062_);
v_pkgDir_2064_ = l_Lake_joinRelative(v_wsDir_1955_, v___y_2062_);
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2064_);
v___x_2067_ = l_Lake_resolvePath(v_pkgDir_2064_);
v___x_2068_ = lean_string_utf8_byte_size(v___x_2067_);
v___x_2069_ = lean_nat_dec_eq(v___x_2068_, v___x_2065_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2067_);
v___y_2039_ = v___x_2066_;
v___y_2040_ = v___x_2063_;
v___y_2041_ = v___y_2062_;
v___y_2042_ = v_pkgDir_2064_;
v___y_2043_ = v___x_2065_;
v_val_2044_ = v___x_2070_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2071_; 
lean_dec_ref(v___x_2067_);
v___x_2071_ = lean_box(0);
v___y_2039_ = v___x_2066_;
v___y_2040_ = v___x_2063_;
v___y_2041_ = v___y_2062_;
v___y_2042_ = v_pkgDir_2064_;
v___y_2043_ = v___x_2065_;
v_val_2044_ = v___x_2071_;
goto v___jp_2038_;
}
}
v___jp_2072_:
{
if (lean_obj_tag(v_subDir_x3f_1961_) == 1)
{
lean_object* v_val_2075_; lean_object* v___x_2076_; 
v_val_2075_ = lean_ctor_get(v_subDir_x3f_1961_, 0);
lean_inc(v_val_2075_);
v___x_2076_ = l_Lake_joinRelative(v_relPkgDir_1957_, v_val_2075_);
v___y_2060_ = v_a_2074_;
v___y_2061_ = v___y_2073_;
v___y_2062_ = v___x_2076_;
goto v___jp_2059_;
}
else
{
v___y_2060_ = v_a_2074_;
v___y_2061_ = v___y_2073_;
v___y_2062_ = v_relPkgDir_1957_;
goto v___jp_2059_;
}
}
v___jp_2078_:
{
lean_object* v___x_2080_; 
lean_inc(v_inputRev_x3f_1960_);
lean_inc_ref(v___y_2079_);
lean_inc_ref(v_gitDir_2077_);
lean_inc_ref(v_name_1956_);
v___x_2080_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1962_, v_name_1956_, v_gitDir_2077_, v___y_2079_, v_inputRev_x3f_1960_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2130_; 
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2080_, 0);
lean_dec(v_unused_2131_);
v___x_2082_ = v___x_2080_;
v_isShared_2083_ = v_isSharedCheck_2130_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v___x_2080_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2130_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2086_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2077_, v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v_a_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
lean_del_object(v___x_2082_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
v_a_2088_ = lean_ctor_get(v___x_2086_, 1);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2086_, 2);
v___x_2089_ = lean_array_get_size(v_a_2088_);
v___x_2090_ = lean_nat_dec_lt(v___x_2084_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_dec(v_a_2088_);
v___y_2073_ = v___y_2079_;
v_a_2074_ = v_a_2087_;
goto v___jp_2072_;
}
else
{
lean_object* v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = lean_usize_of_nat(v___x_2089_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2088_, v___x_2092_, v___x_2093_, v___x_2091_, v_a_1962_);
lean_dec(v_a_2088_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v___y_2073_ = v___y_2079_;
v_a_2074_ = v_a_2087_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2087_);
lean_dec_ref(v___y_2079_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1966_);
lean_dec(v_name_1965_);
lean_dec(v_subDir_x3f_1961_);
lean_dec(v_inputRev_x3f_1960_);
lean_dec_ref(v_remoteUrl_1959_);
lean_dec_ref(v_relPkgDir_1957_);
lean_dec_ref(v_name_1956_);
lean_dec_ref(v_wsDir_1955_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
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
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
lean_dec_ref(v___y_2079_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1966_);
lean_dec(v_name_1965_);
lean_dec(v_subDir_x3f_1961_);
lean_dec(v_inputRev_x3f_1960_);
lean_dec_ref(v_remoteUrl_1959_);
lean_dec_ref(v_relPkgDir_1957_);
lean_dec_ref(v_name_1956_);
lean_dec_ref(v_wsDir_1955_);
v_a_2103_ = lean_ctor_get(v___x_2086_, 1);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2086_, 2);
v___x_2104_ = lean_array_get_size(v_a_2103_);
v___x_2105_ = lean_nat_dec_lt(v___x_2084_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_dec(v_a_2103_);
v___x_2106_ = lean_box(0);
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 1);
lean_ctor_set(v___x_2082_, 0, v___x_2106_);
v___x_2108_ = v___x_2082_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
else
{
lean_object* v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
lean_del_object(v___x_2082_);
v___x_2110_ = lean_box(0);
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = lean_usize_of_nat(v___x_2104_);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2103_, v___x_2111_, v___x_2112_, v___x_2110_, v_a_1962_);
lean_dec(v_a_2103_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v___x_2113_, 0);
lean_dec(v_unused_2121_);
v___x_2115_ = v___x_2113_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v___x_2113_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 1);
lean_ctor_set(v___x_2115_, 0, v___x_2110_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2110_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_a_2122_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2113_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2113_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_gitDir_2077_);
lean_del_object(v___x_1968_);
lean_dec_ref(v_scope_1966_);
lean_dec(v_name_1965_);
lean_dec(v_subDir_x3f_1961_);
lean_dec(v_inputRev_x3f_1960_);
lean_dec_ref(v_remoteUrl_1959_);
lean_dec_ref(v_relPkgDir_1957_);
lean_dec_ref(v_name_1956_);
lean_dec_ref(v_wsDir_1955_);
v_a_2132_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2080_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2080_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_2146_, lean_object* v_inherited_2147_, lean_object* v_lakeEnv_2148_, lean_object* v_wsDir_2149_, lean_object* v_name_2150_, lean_object* v_relPkgDir_2151_, lean_object* v_gitUrl_2152_, lean_object* v_remoteUrl_2153_, lean_object* v_inputRev_x3f_2154_, lean_object* v_subDir_x3f_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
uint8_t v_inherited_boxed_2158_; lean_object* v_res_2159_; 
v_inherited_boxed_2158_ = lean_unbox(v_inherited_2147_);
v_res_2159_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_2146_, v_inherited_boxed_2158_, v_lakeEnv_2148_, v_wsDir_2149_, v_name_2150_, v_relPkgDir_2151_, v_gitUrl_2152_, v_remoteUrl_2153_, v_inputRev_x3f_2154_, v_subDir_x3f_2155_, v_a_2156_);
lean_dec_ref(v_a_2156_);
lean_dec_ref(v_lakeEnv_2148_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_2160_, lean_object* v_dep_2161_, uint8_t v_inherited_2162_, lean_object* v_lakeEnv_2163_, lean_object* v_wsDir_2164_, lean_object* v_name_2165_, lean_object* v_relPkgDir_2166_, lean_object* v_gitUrl_2167_, lean_object* v_remoteUrl_2168_, lean_object* v_inputRev_x3f_2169_, lean_object* v_subDir_x3f_2170_){
_start:
{
lean_object* v_pkgUrlMap_2172_; lean_object* v_name_2173_; lean_object* v_scope_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2350_; 
v_pkgUrlMap_2172_ = lean_ctor_get(v_lakeEnv_2163_, 5);
v_name_2173_ = lean_ctor_get(v_dep_2161_, 0);
v_scope_2174_ = lean_ctor_get(v_dep_2161_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_dep_2161_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; lean_object* v_unused_2352_; lean_object* v_unused_2353_; 
v_unused_2351_ = lean_ctor_get(v_dep_2161_, 4);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_dep_2161_, 3);
lean_dec(v_unused_2352_);
v_unused_2353_ = lean_ctor_get(v_dep_2161_, 2);
lean_dec(v_unused_2353_);
v___x_2176_ = v_dep_2161_;
v_isShared_2177_ = v_isSharedCheck_2350_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_scope_2174_);
lean_inc(v_name_2173_);
lean_dec(v_dep_2161_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2350_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v_a_2182_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v_val_2196_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v_a_2215_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v_val_2252_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2281_; lean_object* v_a_2282_; lean_object* v_gitDir_2285_; lean_object* v___y_2287_; lean_object* v___x_2348_; 
lean_inc_ref(v_relPkgDir_2166_);
lean_inc_ref(v_wsDir_2164_);
v_gitDir_2285_ = l_Lake_joinRelative(v_wsDir_2164_, v_relPkgDir_2166_);
v___x_2348_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2172_, v_name_2173_);
if (lean_obj_tag(v___x_2348_) == 0)
{
v___y_2287_ = v_gitUrl_2167_;
goto v___jp_2286_;
}
else
{
lean_object* v_val_2349_; 
lean_dec_ref(v_gitUrl_2167_);
v_val_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_val_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___y_2287_ = v_val_2349_;
goto v___jp_2286_;
}
v___jp_2178_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2183_ = l_Lake_defaultConfigFile;
v___x_2184_ = lean_box(0);
v___x_2185_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2185_, 0, v_name_2173_);
lean_ctor_set(v___x_2185_, 1, v_scope_2174_);
lean_ctor_set(v___x_2185_, 2, v___x_2183_);
lean_ctor_set(v___x_2185_, 3, v___x_2184_);
lean_ctor_set(v___x_2185_, 4, v___y_2181_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*5, v_inherited_2162_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 4, v___x_2185_);
lean_ctor_set(v___x_2176_, 3, v_a_2182_);
lean_ctor_set(v___x_2176_, 2, v_remoteUrl_2168_);
lean_ctor_set(v___x_2176_, 1, v___y_2179_);
lean_ctor_set(v___x_2176_, 0, v___y_2180_);
v___x_2187_ = v___x_2176_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___y_2180_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___y_2179_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_remoteUrl_2168_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_a_2182_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
return v___x_2188_;
}
}
v___jp_2190_:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_array_get_size(v___y_2194_);
v___x_2198_ = lean_nat_dec_lt(v___y_2195_, v___x_2197_);
if (v___x_2198_ == 0)
{
v___y_2179_ = v___y_2192_;
v___y_2180_ = v___y_2191_;
v___y_2181_ = v___y_2193_;
v_a_2182_ = v_val_2196_;
goto v___jp_2178_;
}
else
{
lean_object* v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = lean_box(0);
v___x_2200_ = ((size_t)0ULL);
v___x_2201_ = lean_usize_of_nat(v___x_2197_);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2194_, v___x_2200_, v___x_2201_, v___x_2199_, v_a_2160_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_dec_ref_known(v___x_2202_, 1);
v___y_2179_ = v___y_2192_;
v___y_2180_ = v___y_2191_;
v___y_2181_ = v___y_2193_;
v_a_2182_ = v_val_2196_;
goto v___jp_2178_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v_val_2196_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_del_object(v___x_2176_);
lean_dec_ref(v_scope_2174_);
lean_dec(v_name_2173_);
lean_dec_ref(v_remoteUrl_2168_);
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
v___jp_2211_:
{
if (lean_obj_tag(v_a_2215_) == 1)
{
lean_object* v_val_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec_ref(v___y_2214_);
lean_dec_ref(v_name_2165_);
v_val_2216_ = lean_ctor_get(v_a_2215_, 0);
lean_inc_n(v_val_2216_, 2);
lean_dec_ref_known(v_a_2215_, 1);
v___x_2217_ = l_Lake_defaultManifestFile;
v___x_2218_ = l_Lake_joinRelative(v_val_2216_, v___x_2217_);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2221_ = l_Lake_Manifest_load(v___x_2218_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 1);
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
v___y_2191_ = v_val_2216_;
v___y_2192_ = v___y_2212_;
v___y_2193_ = v___y_2213_;
v___y_2194_ = v___x_2220_;
v___y_2195_ = v___x_2219_;
v_val_2196_ = v___x_2227_;
goto v___jp_2190_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2221_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2221_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 0);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
v___y_2191_ = v_val_2216_;
v___y_2192_ = v___y_2212_;
v___y_2193_ = v___y_2213_;
v___y_2194_ = v___x_2220_;
v___y_2195_ = v___x_2219_;
v_val_2196_ = v___x_2235_;
goto v___jp_2190_;
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v_a_2215_);
lean_dec_ref(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_del_object(v___x_2176_);
lean_dec_ref(v_scope_2174_);
lean_dec(v_name_2173_);
lean_dec_ref(v_remoteUrl_2168_);
v___x_2238_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2239_ = lean_string_append(v_name_2165_, v___x_2238_);
v___x_2240_ = lean_string_append(v___x_2239_, v___y_2214_);
lean_dec_ref(v___y_2214_);
v___x_2241_ = 3;
v___x_2242_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*1, v___x_2241_);
lean_inc_ref(v_a_2160_);
v___x_2243_ = lean_apply_2(v_a_2160_, v___x_2242_, lean_box(0));
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
v___jp_2246_:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_array_get_size(v___y_2251_);
v___x_2254_ = lean_nat_dec_lt(v___y_2247_, v___x_2253_);
if (v___x_2254_ == 0)
{
v___y_2212_ = v___y_2248_;
v___y_2213_ = v___y_2249_;
v___y_2214_ = v___y_2250_;
v_a_2215_ = v_val_2252_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2255_; size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = lean_usize_of_nat(v___x_2253_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2251_, v___x_2256_, v___x_2257_, v___x_2255_, v_a_2160_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_dec_ref_known(v___x_2258_, 1);
v___y_2212_ = v___y_2248_;
v___y_2213_ = v___y_2249_;
v___y_2214_ = v___y_2250_;
v_a_2215_ = v_val_2252_;
goto v___jp_2211_;
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_val_2252_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_del_object(v___x_2176_);
lean_dec_ref(v_scope_2174_);
lean_dec(v_name_2173_);
lean_dec_ref(v_remoteUrl_2168_);
lean_dec_ref(v_name_2165_);
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
v___jp_2267_:
{
lean_object* v___x_2271_; lean_object* v_pkgDir_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2271_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2271_, 0, v___y_2269_);
lean_ctor_set(v___x_2271_, 1, v___y_2268_);
lean_ctor_set(v___x_2271_, 2, v_inputRev_x3f_2169_);
lean_ctor_set(v___x_2271_, 3, v_subDir_x3f_2170_);
lean_inc_ref(v___y_2270_);
v_pkgDir_2272_ = l_Lake_joinRelative(v_wsDir_2164_, v___y_2270_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2272_);
v___x_2275_ = l_Lake_resolvePath(v_pkgDir_2272_);
v___x_2276_ = lean_string_utf8_byte_size(v___x_2275_);
v___x_2277_ = lean_nat_dec_eq(v___x_2276_, v___x_2273_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2275_);
v___y_2247_ = v___x_2273_;
v___y_2248_ = v___y_2270_;
v___y_2249_ = v___x_2271_;
v___y_2250_ = v_pkgDir_2272_;
v___y_2251_ = v___x_2274_;
v_val_2252_ = v___x_2278_;
goto v___jp_2246_;
}
else
{
lean_object* v___x_2279_; 
lean_dec_ref(v___x_2275_);
v___x_2279_ = lean_box(0);
v___y_2247_ = v___x_2273_;
v___y_2248_ = v___y_2270_;
v___y_2249_ = v___x_2271_;
v___y_2250_ = v_pkgDir_2272_;
v___y_2251_ = v___x_2274_;
v_val_2252_ = v___x_2279_;
goto v___jp_2246_;
}
}
v___jp_2280_:
{
if (lean_obj_tag(v_subDir_x3f_2170_) == 1)
{
lean_object* v_val_2283_; lean_object* v___x_2284_; 
v_val_2283_ = lean_ctor_get(v_subDir_x3f_2170_, 0);
lean_inc(v_val_2283_);
v___x_2284_ = l_Lake_joinRelative(v_relPkgDir_2166_, v_val_2283_);
v___y_2268_ = v_a_2282_;
v___y_2269_ = v___y_2281_;
v___y_2270_ = v___x_2284_;
goto v___jp_2267_;
}
else
{
v___y_2268_ = v_a_2282_;
v___y_2269_ = v___y_2281_;
v___y_2270_ = v_relPkgDir_2166_;
goto v___jp_2267_;
}
}
v___jp_2286_:
{
lean_object* v___x_2288_; 
lean_inc(v_inputRev_x3f_2169_);
lean_inc_ref(v___y_2287_);
lean_inc_ref(v_gitDir_2285_);
lean_inc_ref(v_name_2165_);
v___x_2288_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2160_, v_name_2165_, v_gitDir_2285_, v___y_2287_, v_inputRev_x3f_2169_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2338_; 
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2288_, 0);
lean_dec(v_unused_2339_);
v___x_2290_ = v___x_2288_;
v_isShared_2291_ = v_isSharedCheck_2338_;
goto v_resetjp_2289_;
}
else
{
lean_dec(v___x_2288_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2338_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2294_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2285_, v___x_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v_a_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
lean_del_object(v___x_2290_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
v_a_2296_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2294_, 2);
v___x_2297_ = lean_array_get_size(v_a_2296_);
v___x_2298_ = lean_nat_dec_lt(v___x_2292_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_dec(v_a_2296_);
v___y_2281_ = v___y_2287_;
v_a_2282_ = v_a_2295_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2299_; size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = lean_box(0);
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2297_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2296_, v___x_2300_, v___x_2301_, v___x_2299_, v_a_2160_);
lean_dec(v_a_2296_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_dec_ref_known(v___x_2302_, 1);
v___y_2281_ = v___y_2287_;
v_a_2282_ = v_a_2295_;
goto v___jp_2280_;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2295_);
lean_dec_ref(v___y_2287_);
lean_del_object(v___x_2176_);
lean_dec_ref(v_scope_2174_);
lean_dec(v_name_2173_);
lean_dec(v_subDir_x3f_2170_);
lean_dec(v_inputRev_x3f_2169_);
lean_dec_ref(v_remoteUrl_2168_);
lean_dec_ref(v_relPkgDir_2166_);
lean_dec_ref(v_name_2165_);
lean_dec_ref(v_wsDir_2164_);
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
else
{
lean_object* v_a_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
lean_dec_ref(v___y_2287_);
lean_del_object(v___x_2176_);
lean_dec_ref(v_scope_2174_);
lean_dec(v_name_2173_);
lean_dec(v_subDir_x3f_2170_);
lean_dec(v_inputRev_x3f_2169_);
lean_dec_ref(v_remoteUrl_2168_);
lean_dec_ref(v_relPkgDir_2166_);
lean_dec_ref(v_name_2165_);
lean_dec_ref(v_wsDir_2164_);
v_a_2311_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2294_, 2);
v___x_2312_ = lean_array_get_size(v_a_2311_);
v___x_2313_ = lean_nat_dec_lt(v___x_2292_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
lean_dec(v_a_2311_);
v___x_2314_ = lean_box(0);
if (v_isShared_2291_ == 0)
{
lean_ctor_set_tag(v___x_2290_, 1);
lean_ctor_set(v___x_2290_, 0, v___x_2314_);
v___x_2316_ = v___x_2290_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
else
{
lean_object* v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; 
lean_del_object(v___x_2290_);
v___x_2318_ = lean_box(0);
v___x_2319_ = ((size_t)0ULL);
v___x_2320_ = lean_usize_of_nat(v___x_2312_);
v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2311_, v___x_2319_, v___x_2320_, v___x_2318_, v_a_2160_);
lean_dec(v_a_2311_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v___x_2321_, 0);
lean_dec(v_unused_2329_);
v___x_2323_ = v___x_2321_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_dec(v___x_2321_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 1);
lean_ctor_set(v___x_2323_, 0, v___x_2318_);
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2318_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_a_2330_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2321_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2321_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v___y_2287_);
lean_dec_ref(v_gitDir_2285_);
lean_del_object(v___x_2176_);
lean_dec_ref(v_scope_2174_);
lean_dec(v_name_2173_);
lean_dec(v_subDir_x3f_2170_);
lean_dec(v_inputRev_x3f_2169_);
lean_dec_ref(v_remoteUrl_2168_);
lean_dec_ref(v_relPkgDir_2166_);
lean_dec_ref(v_name_2165_);
lean_dec_ref(v_wsDir_2164_);
v_a_2340_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2288_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2288_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_2354_, lean_object* v_dep_2355_, lean_object* v_inherited_2356_, lean_object* v_lakeEnv_2357_, lean_object* v_wsDir_2358_, lean_object* v_name_2359_, lean_object* v_relPkgDir_2360_, lean_object* v_gitUrl_2361_, lean_object* v_remoteUrl_2362_, lean_object* v_inputRev_x3f_2363_, lean_object* v_subDir_x3f_2364_, lean_object* v_a_2365_){
_start:
{
uint8_t v_inherited_boxed_2366_; lean_object* v_res_2367_; 
v_inherited_boxed_2366_ = lean_unbox(v_inherited_2356_);
v_res_2367_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2354_, v_dep_2355_, v_inherited_boxed_2366_, v_lakeEnv_2357_, v_wsDir_2358_, v_name_2359_, v_relPkgDir_2360_, v_gitUrl_2361_, v_remoteUrl_2362_, v_inputRev_x3f_2363_, v_subDir_x3f_2364_);
lean_dec_ref(v_lakeEnv_2357_);
lean_dec_ref(v_a_2354_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_2371_, lean_object* v_as_2372_, size_t v_sz_2373_, size_t v_i_2374_, lean_object* v_b_2375_){
_start:
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_usize_dec_lt(v_i_2374_, v_sz_2373_);
if (v___x_2376_ == 0)
{
lean_inc_ref(v_b_2375_);
return v_b_2375_;
}
else
{
lean_object* v_a_2377_; lean_object* v_version_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_a_2377_ = lean_array_uget_borrowed(v_as_2372_, v_i_2374_);
v_version_2378_ = lean_ctor_get(v_a_2377_, 0);
v___x_2379_ = lean_box(0);
v___x_2380_ = l_Lake_VerRange_test(v_ver_2371_, v_version_2378_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; 
v___x_2381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_2382_ = ((size_t)1ULL);
v___x_2383_ = lean_usize_add(v_i_2374_, v___x_2382_);
v_i_2374_ = v___x_2383_;
v_b_2375_ = v___x_2381_;
goto _start;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_inc(v_a_2377_);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v_a_2377_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v___x_2379_);
return v___x_2387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_2388_, lean_object* v_as_2389_, lean_object* v_sz_2390_, lean_object* v_i_2391_, lean_object* v_b_2392_){
_start:
{
size_t v_sz_boxed_2393_; size_t v_i_boxed_2394_; lean_object* v_res_2395_; 
v_sz_boxed_2393_ = lean_unbox_usize(v_sz_2390_);
lean_dec(v_sz_2390_);
v_i_boxed_2394_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_2388_, v_as_2389_, v_sz_boxed_2393_, v_i_boxed_2394_, v_b_2392_);
lean_dec_ref(v_b_2392_);
lean_dec_ref(v_as_2389_);
lean_dec_ref(v_ver_2388_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_2405_, uint8_t v_inherited_2406_, lean_object* v_lakeEnv_2407_, lean_object* v_wsDir_2408_, lean_object* v_relPkgsDir_2409_, lean_object* v_relParentDir_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v_a_2439_; lean_object* v_a_2443_; lean_object* v_name_2450_; lean_object* v_scope_2451_; lean_object* v_version_2452_; lean_object* v_src_x3f_2453_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_a_2459_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v_val_2472_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v_a_2493_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v_val_2532_; 
v_name_2450_ = lean_ctor_get(v_dep_2405_, 0);
v_scope_2451_ = lean_ctor_get(v_dep_2405_, 1);
v_version_2452_ = lean_ctor_get(v_dep_2405_, 2);
v_src_x3f_2453_ = lean_ctor_get(v_dep_2405_, 3);
lean_inc(v_src_x3f_2453_);
if (lean_obj_tag(v_src_x3f_2453_) == 1)
{
lean_object* v_val_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2597_; 
v_val_2547_ = lean_ctor_get(v_src_x3f_2453_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_src_x3f_2453_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2549_ = v_src_x3f_2453_;
v_isShared_2550_ = v_isSharedCheck_2597_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_val_2547_);
lean_dec(v_src_x3f_2453_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2597_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
if (lean_obj_tag(v_val_2547_) == 0)
{
lean_object* v_dir_2551_; uint8_t v_copy_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2584_; 
lean_inc_ref(v_scope_2451_);
lean_inc(v_name_2450_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v_dir_2551_ = lean_ctor_get(v_val_2547_, 0);
v_copy_2552_ = lean_ctor_get_uint8(v_val_2547_, sizeof(void*)*1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_val_2547_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2554_ = v_val_2547_;
v_isShared_2555_ = v_isSharedCheck_2584_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_dir_2551_);
lean_dec(v_val_2547_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2584_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v_relSrc_2556_; lean_object* v_a_2558_; 
v_relSrc_2556_ = l_Lake_joinRelative(v_relParentDir_2410_, v_dir_2551_);
if (v_copy_2552_ == 0)
{
lean_dec_ref(v_relPkgsDir_2409_);
lean_inc_ref(v_relSrc_2556_);
v_a_2558_ = v_relSrc_2556_;
goto v___jp_2557_;
}
else
{
uint8_t v___x_2575_; lean_object* v___x_2576_; lean_object* v_relDst_2577_; lean_object* v_dst_2578_; lean_object* v___x_2579_; 
v___x_2575_ = 0;
lean_inc(v_name_2450_);
v___x_2576_ = l_Lean_Name_toString(v_name_2450_, v___x_2575_);
v_relDst_2577_ = l_Lake_joinRelative(v_relPkgsDir_2409_, v___x_2576_);
lean_inc_ref(v_relDst_2577_);
lean_inc_ref(v_wsDir_2408_);
v_dst_2578_ = l_Lake_joinRelative(v_wsDir_2408_, v_relDst_2577_);
v___x_2579_ = l_Lake_removeDirAllIfExists(v_dst_2578_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_src_2580_; lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2579_, 1);
lean_inc_ref(v_relSrc_2556_);
lean_inc_ref(v_wsDir_2408_);
v_src_2580_ = l_Lake_joinRelative(v_wsDir_2408_, v_relSrc_2556_);
v___x_2581_ = l_Lake_copyDirAll(v_src_2580_, v_dst_2578_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_dec_ref_known(v___x_2581_, 1);
v_a_2558_ = v_relDst_2577_;
goto v___jp_2557_;
}
else
{
lean_object* v_a_2582_; 
lean_dec_ref(v_relDst_2577_);
lean_dec_ref(v_relSrc_2556_);
lean_del_object(v___x_2554_);
lean_del_object(v___x_2549_);
lean_dec_ref(v_scope_2451_);
lean_dec(v_name_2450_);
lean_dec_ref(v_wsDir_2408_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v_a_2443_ = v_a_2582_;
goto v___jp_2442_;
}
}
else
{
lean_object* v_a_2583_; 
lean_dec_ref(v_dst_2578_);
lean_dec_ref(v_relDst_2577_);
lean_dec_ref(v_relSrc_2556_);
lean_del_object(v___x_2554_);
lean_del_object(v___x_2549_);
lean_dec_ref(v_scope_2451_);
lean_dec(v_name_2450_);
lean_dec_ref(v_wsDir_2408_);
v_a_2583_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2579_, 1);
v_a_2443_ = v_a_2583_;
goto v___jp_2442_;
}
}
v___jp_2557_:
{
uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2559_ = 0;
lean_inc(v_name_2450_);
v___x_2560_ = l_Lean_Name_toString(v_name_2450_, v___x_2559_);
v___x_2561_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v_relSrc_2556_);
v___x_2563_ = v___x_2554_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_relSrc_2556_);
lean_ctor_set_uint8(v_reuseFailAlloc_2574_, sizeof(void*)*1, v_copy_2552_);
v___x_2563_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
lean_object* v_pkgDir_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
lean_inc_ref(v_a_2558_);
v_pkgDir_2564_ = l_Lake_joinRelative(v_wsDir_2408_, v_a_2558_);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2564_);
v___x_2567_ = l_Lake_resolvePath(v_pkgDir_2564_);
v___x_2568_ = lean_string_utf8_byte_size(v___x_2567_);
v___x_2569_ = lean_nat_dec_eq(v___x_2568_, v___x_2565_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2571_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2567_);
v___x_2571_ = v___x_2549_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2567_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
v___y_2525_ = v___x_2561_;
v___y_2526_ = v___x_2566_;
v___y_2527_ = v___x_2560_;
v___y_2528_ = v_pkgDir_2564_;
v___y_2529_ = v___x_2565_;
v___y_2530_ = v___x_2563_;
v___y_2531_ = v_a_2558_;
v_val_2532_ = v___x_2571_;
goto v___jp_2524_;
}
}
else
{
lean_object* v___x_2573_; 
lean_dec_ref(v___x_2567_);
lean_del_object(v___x_2549_);
v___x_2573_ = lean_box(0);
v___y_2525_ = v___x_2561_;
v___y_2526_ = v___x_2566_;
v___y_2527_ = v___x_2560_;
v___y_2528_ = v_pkgDir_2564_;
v___y_2529_ = v___x_2565_;
v___y_2530_ = v___x_2563_;
v___y_2531_ = v_a_2558_;
v_val_2532_ = v___x_2573_;
goto v___jp_2524_;
}
}
}
}
}
else
{
lean_object* v_url_2585_; lean_object* v_rev_2586_; lean_object* v_subDir_2587_; lean_object* v___y_2589_; lean_object* v___x_2594_; 
lean_del_object(v___x_2549_);
lean_dec_ref(v_relParentDir_2410_);
v_url_2585_ = lean_ctor_get(v_val_2547_, 0);
lean_inc_ref_n(v_url_2585_, 2);
v_rev_2586_ = lean_ctor_get(v_val_2547_, 1);
lean_inc(v_rev_2586_);
v_subDir_2587_ = lean_ctor_get(v_val_2547_, 2);
lean_inc(v_subDir_2587_);
lean_dec_ref_known(v_val_2547_, 3);
v___x_2594_ = l_Lake_Git_filterUrl_x3f(v_url_2585_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2595_; 
v___x_2595_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2589_ = v___x_2595_;
goto v___jp_2588_;
}
else
{
lean_object* v_val_2596_; 
v_val_2596_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_val_2596_);
lean_dec_ref_known(v___x_2594_, 1);
v___y_2589_ = v_val_2596_;
goto v___jp_2588_;
}
v___jp_2588_:
{
uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2590_ = 0;
lean_inc(v_name_2450_);
v___x_2591_ = l_Lean_Name_toString(v_name_2450_, v___x_2590_);
lean_inc_ref(v___x_2591_);
v___x_2592_ = l_Lake_joinRelative(v_relPkgsDir_2409_, v___x_2591_);
v___x_2593_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2411_, v_dep_2405_, v_inherited_2406_, v_lakeEnv_2407_, v_wsDir_2408_, v___x_2591_, v___x_2592_, v_url_2585_, v___y_2589_, v_rev_2586_, v_subDir_2587_);
lean_dec_ref(v_lakeEnv_2407_);
return v___x_2593_;
}
}
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
lean_dec(v_src_x3f_2453_);
lean_dec_ref(v_relParentDir_2410_);
v___x_2598_ = lean_string_utf8_byte_size(v_scope_2451_);
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_nat_dec_eq(v___x_2598_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___y_2603_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v_a_2625_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v_a_2692_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v_fst_2799_; lean_object* v_snd_2800_; 
lean_inc(v_name_2450_);
v___x_2601_ = l_Lean_Name_toString(v_name_2450_, v___x_2600_);
v___x_2796_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2451_);
lean_inc_ref(v_lakeEnv_2407_);
v___x_2797_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_2407_, v_scope_2451_, v___x_2601_, v___x_2796_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2815_; lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2815_);
v_a_2816_ = lean_ctor_get(v___x_2797_, 1);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2797_, 2);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2815_);
v_fst_2799_ = v___x_2817_;
v_snd_2800_ = v_a_2816_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2818_; lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2818_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2818_);
v_a_2819_ = lean_ctor_get(v___x_2797_, 1);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2797_, 2);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v_a_2818_);
v_fst_2799_ = v___x_2820_;
v_snd_2800_ = v_a_2819_;
goto v___jp_2798_;
}
v___jp_2602_:
{
lean_object* v_toString_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_toString_2604_ = lean_ctor_get(v___y_2603_, 0);
lean_inc_ref(v_toString_2604_);
lean_dec_ref(v___y_2603_);
v___x_2605_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2606_ = lean_string_append(v_scope_2451_, v___x_2605_);
v___x_2607_ = lean_string_append(v___x_2606_, v___x_2601_);
lean_dec_ref(v___x_2601_);
v___x_2608_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_2609_ = lean_string_append(v___x_2607_, v___x_2608_);
v___x_2610_ = lean_string_append(v___x_2609_, v_toString_2604_);
lean_dec_ref(v_toString_2604_);
v___x_2611_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_2612_ = lean_string_append(v___x_2610_, v___x_2611_);
v___x_2613_ = 3;
v___x_2614_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*1, v___x_2613_);
lean_inc_ref(v_a_2411_);
v___x_2615_ = lean_apply_2(v_a_2411_, v___x_2614_, lean_box(0));
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
v___jp_2618_:
{
if (lean_obj_tag(v_a_2625_) == 0)
{
lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2641_; 
lean_inc_ref(v_scope_2451_);
lean_dec_ref(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_a_2625_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; 
v_unused_2642_ = lean_ctor_get(v_a_2625_, 0);
lean_dec(v_unused_2642_);
v___x_2627_ = v_a_2625_;
v_isShared_2628_ = v_isSharedCheck_2641_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v_a_2625_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2641_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2629_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2630_ = lean_string_append(v_scope_2451_, v___x_2629_);
v___x_2631_ = lean_string_append(v___x_2630_, v___x_2601_);
lean_dec_ref(v___x_2601_);
v___x_2632_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_2633_ = lean_string_append(v___x_2631_, v___x_2632_);
v___x_2634_ = 3;
v___x_2635_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*1, v___x_2634_);
lean_inc_ref(v_a_2411_);
v___x_2636_ = lean_apply_2(v_a_2411_, v___x_2635_, lean_box(0));
v___x_2637_ = lean_box(0);
if (v_isShared_2628_ == 0)
{
lean_ctor_set_tag(v___x_2627_, 1);
lean_ctor_set(v___x_2627_, 0, v___x_2637_);
v___x_2639_ = v___x_2627_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2644_; size_t v_sz_2645_; size_t v___x_2646_; lean_object* v___x_2647_; lean_object* v_fst_2648_; 
v_a_2643_ = lean_ctor_get(v_a_2625_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v_a_2625_, 1);
v___x_2644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_2645_ = lean_array_size(v_a_2643_);
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_2619_, v_a_2643_, v_sz_2645_, v___x_2646_, v___x_2644_);
lean_dec(v_a_2643_);
v_fst_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_fst_2648_);
lean_dec_ref(v___x_2647_);
if (lean_obj_tag(v_fst_2648_) == 0)
{
lean_inc_ref(v_scope_2451_);
lean_dec_ref(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v___y_2603_ = v___y_2619_;
goto v___jp_2602_;
}
else
{
lean_object* v_val_2649_; 
v_val_2649_ = lean_ctor_get(v_fst_2648_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v_fst_2648_, 1);
if (lean_obj_tag(v_val_2649_) == 1)
{
lean_object* v_val_2650_; lean_object* v_version_2651_; lean_object* v_revision_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec_ref(v___y_2619_);
v_val_2650_ = lean_ctor_get(v_val_2649_, 0);
lean_inc(v_val_2650_);
lean_dec_ref_known(v_val_2649_, 1);
v_version_2651_ = lean_ctor_get(v_val_2650_, 0);
lean_inc_ref(v_version_2651_);
v_revision_2652_ = lean_ctor_get(v_val_2650_, 1);
lean_inc_ref(v_revision_2652_);
lean_dec(v_val_2650_);
v___x_2653_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_2451_);
v___x_2654_ = lean_string_append(v_scope_2451_, v___x_2653_);
v___x_2655_ = lean_string_append(v___x_2654_, v___x_2601_);
lean_dec_ref(v___x_2601_);
v___x_2656_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_2657_ = lean_string_append(v___x_2655_, v___x_2656_);
v___x_2658_ = l_Lake_StdVer_toString(v_version_2651_);
v___x_2659_ = lean_string_append(v___x_2657_, v___x_2658_);
lean_dec_ref(v___x_2658_);
v___x_2660_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_2661_ = lean_string_append(v___x_2659_, v___x_2660_);
v___x_2662_ = lean_string_append(v___x_2661_, v_revision_2652_);
v___x_2663_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_2664_ = lean_string_append(v___x_2662_, v___x_2663_);
v___x_2665_ = 1;
v___x_2666_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*1, v___x_2665_);
lean_inc_ref(v_a_2411_);
v___x_2667_ = lean_apply_2(v_a_2411_, v___x_2666_, lean_box(0));
v___y_2434_ = v___y_2620_;
v___y_2435_ = v___y_2621_;
v___y_2436_ = v___y_2622_;
v___y_2437_ = v___y_2623_;
v___y_2438_ = v___y_2624_;
v_a_2439_ = v_revision_2652_;
goto v___jp_2433_;
}
else
{
lean_inc_ref(v_scope_2451_);
lean_dec(v_val_2649_);
lean_dec_ref(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v___y_2603_ = v___y_2619_;
goto v___jp_2602_;
}
}
}
}
v___jp_2668_:
{
lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = lean_array_get_size(v_snd_2676_);
v___x_2678_ = lean_nat_dec_lt(v___x_2599_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v_snd_2676_);
v___y_2619_ = v___y_2669_;
v___y_2620_ = v___y_2670_;
v___y_2621_ = v___y_2671_;
v___y_2622_ = v___y_2672_;
v___y_2623_ = v___y_2673_;
v___y_2624_ = v___y_2674_;
v_a_2625_ = v_fst_2675_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2679_; size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___x_2679_ = lean_box(0);
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = lean_usize_of_nat(v___x_2677_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2676_, v___x_2680_, v___x_2681_, v___x_2679_, v_a_2411_);
lean_dec_ref(v_snd_2676_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_dec_ref_known(v___x_2682_, 1);
v___y_2619_ = v___y_2669_;
v___y_2620_ = v___y_2670_;
v___y_2621_ = v___y_2671_;
v___y_2622_ = v___y_2672_;
v___y_2623_ = v___y_2673_;
v___y_2624_ = v___y_2674_;
v_a_2625_ = v_fst_2675_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_fst_2675_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
v___jp_2691_:
{
if (lean_obj_tag(v_a_2692_) == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_inc_ref(v_scope_2451_);
lean_dec_ref_known(v_a_2692_, 1);
lean_dec_ref(v_relPkgsDir_2409_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v___x_2693_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2694_ = lean_string_append(v_scope_2451_, v___x_2693_);
v___x_2695_ = lean_string_append(v___x_2694_, v___x_2601_);
lean_dec_ref(v___x_2601_);
v___x_2696_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2697_ = lean_string_append(v___x_2695_, v___x_2696_);
v___x_2698_ = 3;
v___x_2699_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*1, v___x_2698_);
lean_inc_ref(v_a_2411_);
v___x_2700_ = lean_apply_2(v_a_2411_, v___x_2699_, lean_box(0));
v___x_2701_ = lean_box(0);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2795_; 
v_a_2703_ = lean_ctor_get(v_a_2692_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_a_2692_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2705_ = v_a_2692_;
v_isShared_2706_ = v_isSharedCheck_2795_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v_a_2692_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2795_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
if (lean_obj_tag(v_a_2703_) == 0)
{
lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_del_object(v___x_2705_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_relPkgsDir_2409_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
v___x_2707_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_2405_);
v___x_2708_ = 3;
v___x_2709_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*1, v___x_2708_);
lean_inc_ref(v_a_2411_);
v___x_2710_ = lean_apply_2(v_a_2411_, v___x_2709_, lean_box(0));
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
else
{
lean_object* v_val_2713_; lean_object* v___x_2714_; 
v_val_2713_ = lean_ctor_get(v_a_2703_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v_a_2703_, 1);
v___x_2714_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2713_);
if (lean_obj_tag(v___x_2714_) == 1)
{
lean_object* v_val_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2794_; 
v_val_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2794_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_val_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2794_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
if (lean_obj_tag(v_val_2715_) == 0)
{
lean_object* v_url_2719_; lean_object* v_githubUrl_x3f_2720_; lean_object* v_defaultBranch_x3f_2721_; lean_object* v_subDir_x3f_2722_; lean_object* v_name_2723_; lean_object* v_fullName_2724_; lean_object* v___x_2725_; 
v_url_2719_ = lean_ctor_get(v_val_2715_, 1);
lean_inc_ref(v_url_2719_);
v_githubUrl_x3f_2720_ = lean_ctor_get(v_val_2715_, 2);
lean_inc(v_githubUrl_x3f_2720_);
v_defaultBranch_x3f_2721_ = lean_ctor_get(v_val_2715_, 3);
lean_inc(v_defaultBranch_x3f_2721_);
v_subDir_x3f_2722_ = lean_ctor_get(v_val_2715_, 4);
lean_inc(v_subDir_x3f_2722_);
lean_dec_ref_known(v_val_2715_, 5);
v_name_2723_ = lean_ctor_get(v_val_2713_, 0);
lean_inc_ref(v_name_2723_);
v_fullName_2724_ = lean_ctor_get(v_val_2713_, 1);
lean_inc_ref(v_fullName_2724_);
lean_dec(v_val_2713_);
v___x_2725_ = l_Lake_joinRelative(v_relPkgsDir_2409_, v_name_2723_);
switch(lean_obj_tag(v_version_2452_))
{
case 0:
{
lean_object* v___x_2726_; 
lean_del_object(v___x_2705_);
lean_dec_ref(v___x_2601_);
v___x_2726_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_2721_) == 0)
{
uint8_t v___x_2727_; 
lean_dec_ref(v___x_2725_);
lean_dec_ref(v_fullName_2724_);
lean_dec(v_subDir_x3f_2722_);
lean_dec(v_githubUrl_x3f_2720_);
lean_dec_ref(v_url_2719_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v___x_2727_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2728_ = lean_box(0);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2728_);
v___x_2730_ = v___x_2717_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
else
{
lean_object* v___x_2732_; size_t v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
lean_del_object(v___x_2717_);
v___x_2732_ = lean_box(0);
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2726_, v___x_2733_, v___x_2734_, v___x_2732_, v_a_2411_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v___x_2735_, 0);
lean_dec(v_unused_2743_);
v___x_2737_ = v___x_2735_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_dec(v___x_2735_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 1);
lean_ctor_set(v___x_2737_, 0, v___x_2732_);
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2732_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_a_2744_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2735_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2735_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
else
{
lean_object* v_val_2752_; uint8_t v___x_2753_; 
lean_del_object(v___x_2717_);
v_val_2752_ = lean_ctor_get(v_defaultBranch_x3f_2721_, 0);
lean_inc(v_val_2752_);
lean_dec_ref_known(v_defaultBranch_x3f_2721_, 1);
v___x_2753_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2753_ == 0)
{
v___y_2434_ = v_subDir_x3f_2722_;
v___y_2435_ = v_githubUrl_x3f_2720_;
v___y_2436_ = v_fullName_2724_;
v___y_2437_ = v___x_2725_;
v___y_2438_ = v_url_2719_;
v_a_2439_ = v_val_2752_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2754_; size_t v___x_2755_; size_t v___x_2756_; lean_object* v___x_2757_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2726_, v___x_2755_, v___x_2756_, v___x_2754_, v_a_2411_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_dec_ref_known(v___x_2757_, 1);
v___y_2434_ = v_subDir_x3f_2722_;
v___y_2435_ = v_githubUrl_x3f_2720_;
v___y_2436_ = v_fullName_2724_;
v___y_2437_ = v___x_2725_;
v___y_2438_ = v_url_2719_;
v_a_2439_ = v_val_2752_;
goto v___jp_2433_;
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_val_2752_);
lean_dec_ref(v___x_2725_);
lean_dec_ref(v_fullName_2724_);
lean_dec(v_subDir_x3f_2722_);
lean_dec(v_githubUrl_x3f_2720_);
lean_dec_ref(v_url_2719_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
lean_dec(v_defaultBranch_x3f_2721_);
lean_del_object(v___x_2717_);
lean_del_object(v___x_2705_);
lean_dec_ref(v___x_2601_);
v_rev_2766_ = lean_ctor_get(v_version_2452_, 0);
v___x_2767_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2768_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2768_ == 0)
{
lean_inc_ref(v_rev_2766_);
v___y_2434_ = v_subDir_x3f_2722_;
v___y_2435_ = v_githubUrl_x3f_2720_;
v___y_2436_ = v_fullName_2724_;
v___y_2437_ = v___x_2725_;
v___y_2438_ = v_url_2719_;
v_a_2439_ = v_rev_2766_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2769_; size_t v___x_2770_; size_t v___x_2771_; lean_object* v___x_2772_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = ((size_t)0ULL);
v___x_2771_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2767_, v___x_2770_, v___x_2771_, v___x_2769_, v_a_2411_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_dec_ref_known(v___x_2772_, 1);
lean_inc_ref(v_rev_2766_);
v___y_2434_ = v_subDir_x3f_2722_;
v___y_2435_ = v_githubUrl_x3f_2720_;
v___y_2436_ = v_fullName_2724_;
v___y_2437_ = v___x_2725_;
v___y_2438_ = v_url_2719_;
v_a_2439_ = v_rev_2766_;
goto v___jp_2433_;
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v___x_2725_);
lean_dec_ref(v_fullName_2724_);
lean_dec(v_subDir_x3f_2722_);
lean_dec(v_githubUrl_x3f_2720_);
lean_dec_ref(v_url_2719_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
default: 
{
lean_object* v_ver_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec(v_defaultBranch_x3f_2721_);
lean_del_object(v___x_2717_);
v_ver_2781_ = lean_ctor_get(v_version_2452_, 0);
v___x_2782_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2451_);
lean_inc_ref(v_lakeEnv_2407_);
v___x_2783_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_2407_, v_scope_2451_, v___x_2601_, v___x_2782_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v_a_2785_; lean_object* v___x_2787_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
v_a_2785_ = lean_ctor_get(v___x_2783_, 1);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2783_, 2);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v_a_2784_);
v___x_2787_ = v___x_2705_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2784_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_inc_ref(v_ver_2781_);
v___y_2669_ = v_ver_2781_;
v___y_2670_ = v_subDir_x3f_2722_;
v___y_2671_ = v_githubUrl_x3f_2720_;
v___y_2672_ = v_fullName_2724_;
v___y_2673_ = v___x_2725_;
v___y_2674_ = v_url_2719_;
v_fst_2675_ = v___x_2787_;
v_snd_2676_ = v_a_2785_;
goto v___jp_2668_;
}
}
else
{
lean_object* v_a_2789_; lean_object* v_a_2790_; lean_object* v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2789_);
v_a_2790_ = lean_ctor_get(v___x_2783_, 1);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2783_, 2);
if (v_isShared_2706_ == 0)
{
lean_ctor_set_tag(v___x_2705_, 0);
lean_ctor_set(v___x_2705_, 0, v_a_2789_);
v___x_2792_ = v___x_2705_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2789_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_inc_ref(v_ver_2781_);
v___y_2669_ = v_ver_2781_;
v___y_2670_ = v_subDir_x3f_2722_;
v___y_2671_ = v_githubUrl_x3f_2720_;
v___y_2672_ = v_fullName_2724_;
v___y_2673_ = v___x_2725_;
v___y_2674_ = v_url_2719_;
v_fst_2675_ = v___x_2792_;
v_snd_2676_ = v_a_2790_;
goto v___jp_2668_;
}
}
}
}
}
else
{
lean_del_object(v___x_2717_);
lean_dec(v_val_2715_);
lean_del_object(v___x_2705_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_relPkgsDir_2409_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v___y_2414_ = v_val_2713_;
v___y_2415_ = v_a_2411_;
goto v___jp_2413_;
}
}
}
else
{
lean_dec(v___x_2714_);
lean_del_object(v___x_2705_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_relPkgsDir_2409_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v___y_2414_ = v_val_2713_;
v___y_2415_ = v_a_2411_;
goto v___jp_2413_;
}
}
}
}
}
v___jp_2798_:
{
lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2801_ = lean_array_get_size(v_snd_2800_);
v___x_2802_ = lean_nat_dec_lt(v___x_2599_, v___x_2801_);
if (v___x_2802_ == 0)
{
lean_dec_ref(v_snd_2800_);
v_a_2692_ = v_fst_2799_;
goto v___jp_2691_;
}
else
{
lean_object* v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = lean_usize_of_nat(v___x_2801_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2800_, v___x_2804_, v___x_2805_, v___x_2803_, v_a_2411_);
lean_dec_ref(v_snd_2800_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref_known(v___x_2806_, 1);
v_a_2692_ = v_fst_2799_;
goto v___jp_2691_;
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref(v_fst_2799_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_relPkgsDir_2409_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
}
else
{
uint8_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_inc(v_name_2450_);
lean_dec_ref(v_relPkgsDir_2409_);
lean_dec_ref(v_wsDir_2408_);
lean_dec_ref(v_lakeEnv_2407_);
lean_dec_ref(v_dep_2405_);
v___x_2821_ = 0;
v___x_2822_ = l_Lean_Name_toString(v_name_2450_, v___x_2821_);
v___x_2823_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2824_ = lean_string_append(v___x_2822_, v___x_2823_);
v___x_2825_ = 3;
v___x_2826_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*1, v___x_2825_);
lean_inc_ref(v_a_2411_);
v___x_2827_ = lean_apply_2(v_a_2411_, v___x_2826_, lean_box(0));
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
}
v___jp_2413_:
{
lean_object* v_fullName_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_fullName_2416_ = lean_ctor_get(v___y_2414_, 1);
lean_inc_ref(v_fullName_2416_);
lean_dec_ref(v___y_2414_);
v___x_2417_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_2418_ = lean_string_append(v_fullName_2416_, v___x_2417_);
v___x_2419_ = 3;
v___x_2420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*1, v___x_2419_);
lean_inc_ref(v___y_2415_);
v___x_2421_ = lean_apply_2(v___y_2415_, v___x_2420_, lean_box(0));
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
v___jp_2424_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___y_2429_);
v___x_2432_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2411_, v_dep_2405_, v_inherited_2406_, v_lakeEnv_2407_, v_wsDir_2408_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2430_, v___x_2431_, v___y_2425_);
lean_dec_ref(v_lakeEnv_2407_);
return v___x_2432_;
}
v___jp_2433_:
{
if (lean_obj_tag(v___y_2435_) == 0)
{
lean_object* v___x_2440_; 
v___x_2440_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2425_ = v___y_2434_;
v___y_2426_ = v___y_2436_;
v___y_2427_ = v___y_2437_;
v___y_2428_ = v___y_2438_;
v___y_2429_ = v_a_2439_;
v___y_2430_ = v___x_2440_;
goto v___jp_2424_;
}
else
{
lean_object* v_val_2441_; 
v_val_2441_ = lean_ctor_get(v___y_2435_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v___y_2435_, 1);
v___y_2425_ = v___y_2434_;
v___y_2426_ = v___y_2436_;
v___y_2427_ = v___y_2437_;
v___y_2428_ = v___y_2438_;
v___y_2429_ = v_a_2439_;
v___y_2430_ = v_val_2441_;
goto v___jp_2424_;
}
}
v___jp_2442_:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2444_ = lean_io_error_to_string(v_a_2443_);
v___x_2445_ = 3;
v___x_2446_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2446_, 0, v___x_2444_);
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*1, v___x_2445_);
lean_inc_ref(v_a_2411_);
v___x_2447_ = lean_apply_2(v_a_2411_, v___x_2446_, lean_box(0));
v___x_2448_ = lean_box(0);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
v___jp_2454_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2460_ = l_Lake_defaultConfigFile;
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2462_, 0, v_name_2450_);
lean_ctor_set(v___x_2462_, 1, v_scope_2451_);
lean_ctor_set(v___x_2462_, 2, v___x_2460_);
lean_ctor_set(v___x_2462_, 3, v___x_2461_);
lean_ctor_set(v___x_2462_, 4, v___y_2457_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*5, v_inherited_2406_);
lean_inc_ref(v___y_2455_);
v___x_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2463_, 0, v___y_2456_);
lean_ctor_set(v___x_2463_, 1, v___y_2458_);
lean_ctor_set(v___x_2463_, 2, v___y_2455_);
lean_ctor_set(v___x_2463_, 3, v_a_2459_);
lean_ctor_set(v___x_2463_, 4, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
v___jp_2465_:
{
lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = lean_array_get_size(v___y_2470_);
v___x_2474_ = lean_nat_dec_lt(v___y_2467_, v___x_2473_);
if (v___x_2474_ == 0)
{
v___y_2455_ = v___y_2466_;
v___y_2456_ = v___y_2468_;
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___y_2471_;
v_a_2459_ = v_val_2472_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2475_; size_t v___x_2476_; size_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2475_ = lean_box(0);
v___x_2476_ = ((size_t)0ULL);
v___x_2477_ = lean_usize_of_nat(v___x_2473_);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2470_, v___x_2476_, v___x_2477_, v___x_2475_, v_a_2411_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_dec_ref_known(v___x_2478_, 1);
v___y_2455_ = v___y_2466_;
v___y_2456_ = v___y_2468_;
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___y_2471_;
v_a_2459_ = v_val_2472_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_val_2472_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec_ref(v_scope_2451_);
lean_dec(v_name_2450_);
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
v___jp_2487_:
{
if (lean_obj_tag(v_a_2493_) == 1)
{
lean_object* v_val_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___y_2489_);
v_val_2494_ = lean_ctor_get(v_a_2493_, 0);
lean_inc_n(v_val_2494_, 2);
lean_dec_ref_known(v_a_2493_, 1);
v___x_2495_ = l_Lake_defaultManifestFile;
v___x_2496_ = l_Lake_joinRelative(v_val_2494_, v___x_2495_);
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2499_ = l_Lake_Manifest_load(v___x_2496_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 1);
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
v___y_2466_ = v___y_2488_;
v___y_2467_ = v___x_2497_;
v___y_2468_ = v_val_2494_;
v___y_2469_ = v___y_2491_;
v___y_2470_ = v___x_2498_;
v___y_2471_ = v___y_2492_;
v_val_2472_ = v___x_2505_;
goto v___jp_2465_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
v_a_2508_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2499_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2499_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set_tag(v___x_2510_, 0);
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
v___y_2466_ = v___y_2488_;
v___y_2467_ = v___x_2497_;
v___y_2468_ = v_val_2494_;
v___y_2469_ = v___y_2491_;
v___y_2470_ = v___x_2498_;
v___y_2471_ = v___y_2492_;
v_val_2472_ = v___x_2513_;
goto v___jp_2465_;
}
}
}
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v_a_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v_scope_2451_);
lean_dec(v_name_2450_);
v___x_2516_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2517_ = lean_string_append(v___y_2489_, v___x_2516_);
v___x_2518_ = lean_string_append(v___x_2517_, v___y_2490_);
lean_dec_ref(v___y_2490_);
v___x_2519_ = 3;
v___x_2520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*1, v___x_2519_);
lean_inc_ref(v_a_2411_);
v___x_2521_ = lean_apply_2(v_a_2411_, v___x_2520_, lean_box(0));
v___x_2522_ = lean_box(0);
v___x_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
}
v___jp_2524_:
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = lean_array_get_size(v___y_2526_);
v___x_2534_ = lean_nat_dec_lt(v___y_2529_, v___x_2533_);
if (v___x_2534_ == 0)
{
v___y_2488_ = v___y_2525_;
v___y_2489_ = v___y_2527_;
v___y_2490_ = v___y_2528_;
v___y_2491_ = v___y_2530_;
v___y_2492_ = v___y_2531_;
v_a_2493_ = v_val_2532_;
goto v___jp_2487_;
}
else
{
lean_object* v___x_2535_; size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2535_ = lean_box(0);
v___x_2536_ = ((size_t)0ULL);
v___x_2537_ = lean_usize_of_nat(v___x_2533_);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2526_, v___x_2536_, v___x_2537_, v___x_2535_, v_a_2411_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_dec_ref_known(v___x_2538_, 1);
v___y_2488_ = v___y_2525_;
v___y_2489_ = v___y_2527_;
v___y_2490_ = v___y_2528_;
v___y_2491_ = v___y_2530_;
v___y_2492_ = v___y_2531_;
v_a_2493_ = v_val_2532_;
goto v___jp_2487_;
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_val_2532_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_scope_2451_);
lean_dec(v_name_2450_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2830_, lean_object* v_inherited_2831_, lean_object* v_lakeEnv_2832_, lean_object* v_wsDir_2833_, lean_object* v_relPkgsDir_2834_, lean_object* v_relParentDir_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
uint8_t v_inherited_boxed_2838_; lean_object* v_res_2839_; 
v_inherited_boxed_2838_ = lean_unbox(v_inherited_2831_);
v_res_2839_ = l_Lake_Dependency_materialize(v_dep_2830_, v_inherited_boxed_2838_, v_lakeEnv_2832_, v_wsDir_2833_, v_relPkgsDir_2834_, v_relParentDir_2835_, v_a_2836_);
lean_dec_ref(v_a_2836_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2845_, lean_object* v_wsDir_2846_, lean_object* v_relPkgDir_2847_, lean_object* v_remoteUrl_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___y_2852_; lean_object* v_a_2853_; lean_object* v___f_2856_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v_val_2862_; lean_object* v_pkgDir_2878_; lean_object* v_a_2880_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v_val_2922_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___f_2856_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_2847_);
v_pkgDir_2878_ = l_Lake_joinRelative(v_wsDir_2846_, v_relPkgDir_2847_);
v___x_2918_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_2919_ = lean_unsigned_to_nat(0u);
v___x_2920_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2878_);
v___x_2937_ = l_Lake_resolvePath(v_pkgDir_2878_);
v___x_2938_ = lean_string_utf8_byte_size(v___x_2937_);
v___x_2939_ = lean_nat_dec_eq(v___x_2938_, v___x_2919_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2937_);
v_val_2922_ = v___x_2940_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2941_; 
lean_dec_ref(v___x_2937_);
v___x_2941_ = lean_box(0);
v_val_2922_ = v___x_2941_;
goto v___jp_2921_;
}
v___jp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2854_, 0, v___y_2852_);
lean_ctor_set(v___x_2854_, 1, v_relPkgDir_2847_);
lean_ctor_set(v___x_2854_, 2, v_remoteUrl_2848_);
lean_ctor_set(v___x_2854_, 3, v_a_2853_);
lean_ctor_set(v___x_2854_, 4, v_manifestEntry_2845_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
v___jp_2857_:
{
lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = lean_array_get_size(v___y_2861_);
v___x_2864_ = lean_nat_dec_lt(v___y_2860_, v___x_2863_);
if (v___x_2864_ == 0)
{
v___y_2852_ = v___y_2859_;
v_a_2853_ = v_val_2862_;
goto v___jp_2851_;
}
else
{
lean_object* v___x_2865_; size_t v___x_2866_; size_t v___x_2867_; lean_object* v___x_1877__overap_2868_; lean_object* v___x_2869_; 
v___x_2865_ = lean_box(0);
v___x_2866_ = ((size_t)0ULL);
v___x_2867_ = lean_usize_of_nat(v___x_2863_);
lean_inc_ref(v___y_2861_);
lean_inc_ref(v___y_2858_);
v___x_1877__overap_2868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2858_, v___f_2856_, v___y_2861_, v___x_2866_, v___x_2867_, v___x_2865_);
lean_inc_ref(v_a_2849_);
v___x_2869_ = lean_apply_2(v___x_1877__overap_2868_, v_a_2849_, lean_box(0));
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref_known(v___x_2869_, 1);
v___y_2852_ = v___y_2859_;
v_a_2853_ = v_val_2862_;
goto v___jp_2851_;
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref(v_val_2862_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v_remoteUrl_2848_);
lean_dec_ref(v_relPkgDir_2847_);
lean_dec_ref(v_manifestEntry_2845_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
v___jp_2879_:
{
if (lean_obj_tag(v_a_2880_) == 1)
{
lean_object* v_manifestFile_x3f_2881_; 
lean_dec_ref(v_pkgDir_2878_);
v_manifestFile_x3f_2881_ = lean_ctor_get(v_manifestEntry_2845_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2881_) == 1)
{
lean_object* v_val_2882_; lean_object* v_val_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_val_2882_ = lean_ctor_get(v_a_2880_, 0);
lean_inc_n(v_val_2882_, 2);
lean_dec_ref_known(v_a_2880_, 1);
v_val_2883_ = lean_ctor_get(v_manifestFile_x3f_2881_, 0);
lean_inc(v_val_2883_);
v___x_2884_ = l_Lake_joinRelative(v_val_2882_, v_val_2883_);
v___x_2885_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2888_ = l_Lake_Manifest_load(v___x_2884_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set_tag(v___x_2891_, 1);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v___y_2858_ = v___x_2885_;
v___y_2859_ = v_val_2882_;
v___y_2860_ = v___x_2886_;
v___y_2861_ = v___x_2887_;
v_val_2862_ = v___x_2894_;
goto v___jp_2857_;
}
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2888_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2888_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set_tag(v___x_2899_, 0);
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
v___y_2858_ = v___x_2885_;
v___y_2859_ = v_val_2882_;
v___y_2860_ = v___x_2886_;
v___y_2861_ = v___x_2887_;
v_val_2862_ = v___x_2902_;
goto v___jp_2857_;
}
}
}
}
else
{
lean_object* v_val_2905_; lean_object* v___x_2906_; 
v_val_2905_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_val_2905_);
lean_dec_ref_known(v_a_2880_, 1);
v___x_2906_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2852_ = v_val_2905_;
v_a_2853_ = v___x_2906_;
goto v___jp_2851_;
}
}
else
{
lean_object* v_name_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec(v_a_2880_);
lean_dec_ref(v_remoteUrl_2848_);
lean_dec_ref(v_relPkgDir_2847_);
v_name_2907_ = lean_ctor_get(v_manifestEntry_2845_, 0);
lean_inc(v_name_2907_);
lean_dec_ref(v_manifestEntry_2845_);
v___x_2908_ = 0;
v___x_2909_ = l_Lean_Name_toString(v_name_2907_, v___x_2908_);
v___x_2910_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2911_ = lean_string_append(v___x_2909_, v___x_2910_);
v___x_2912_ = lean_string_append(v___x_2911_, v_pkgDir_2878_);
lean_dec_ref(v_pkgDir_2878_);
v___x_2913_ = 3;
v___x_2914_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*1, v___x_2913_);
lean_inc_ref(v_a_2849_);
v___x_2915_ = lean_apply_2(v_a_2849_, v___x_2914_, lean_box(0));
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
return v___x_2917_;
}
}
v___jp_2921_:
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2923_ == 0)
{
v_a_2880_ = v_val_2922_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_1931__overap_2927_; lean_object* v___x_2928_; 
v___x_2924_ = lean_box(0);
v___x_2925_ = ((size_t)0ULL);
v___x_2926_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1931__overap_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2918_, v___f_2856_, v___x_2920_, v___x_2925_, v___x_2926_, v___x_2924_);
lean_inc_ref(v_a_2849_);
v___x_2928_ = lean_apply_2(v___x_1931__overap_2927_, v_a_2849_, lean_box(0));
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_dec_ref_known(v___x_2928_, 1);
v_a_2880_ = v_val_2922_;
goto v___jp_2879_;
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_val_2922_);
lean_dec_ref(v_pkgDir_2878_);
lean_dec_ref(v_remoteUrl_2848_);
lean_dec_ref(v_relPkgDir_2847_);
lean_dec_ref(v_manifestEntry_2845_);
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2942_, lean_object* v_wsDir_2943_, lean_object* v_relPkgDir_2944_, lean_object* v_remoteUrl_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2942_, v_wsDir_2943_, v_relPkgDir_2944_, v_remoteUrl_2945_, v_a_2946_);
lean_dec_ref(v_a_2946_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object* v_t_2949_, lean_object* v_k_2950_, lean_object* v_fallback_2951_){
_start:
{
if (lean_obj_tag(v_t_2949_) == 0)
{
lean_object* v_k_2952_; lean_object* v_v_2953_; lean_object* v_l_2954_; lean_object* v_r_2955_; uint8_t v___x_2956_; 
v_k_2952_ = lean_ctor_get(v_t_2949_, 1);
v_v_2953_ = lean_ctor_get(v_t_2949_, 2);
v_l_2954_ = lean_ctor_get(v_t_2949_, 3);
v_r_2955_ = lean_ctor_get(v_t_2949_, 4);
v___x_2956_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2950_, v_k_2952_);
switch(v___x_2956_)
{
case 0:
{
v_t_2949_ = v_l_2954_;
goto _start;
}
case 1:
{
lean_inc(v_v_2953_);
return v_v_2953_;
}
default: 
{
v_t_2949_ = v_r_2955_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2951_);
return v_fallback_2951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object* v_t_2959_, lean_object* v_k_2960_, lean_object* v_fallback_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_2959_, v_k_2960_, v_fallback_2961_);
lean_dec(v_fallback_2961_);
lean_dec(v_k_2960_);
lean_dec(v_t_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2963_, lean_object* v_lakeEnv_2964_, lean_object* v_wsDir_2965_, lean_object* v_relPkgsDir_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v_a_2973_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v_val_2982_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v_a_3001_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v_val_3010_; lean_object* v_name_3025_; lean_object* v_manifestFile_x3f_3026_; lean_object* v_src_3027_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v_a_3032_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v_val_3081_; lean_object* v_a_3097_; 
v_name_3025_ = lean_ctor_get(v_manifestEntry_2963_, 0);
v_manifestFile_x3f_3026_ = lean_ctor_get(v_manifestEntry_2963_, 3);
v_src_3027_ = lean_ctor_get(v_manifestEntry_2963_, 4);
lean_inc_ref(v_src_3027_);
if (lean_obj_tag(v_src_3027_) == 0)
{
uint8_t v_copy_3107_; 
v_copy_3107_ = lean_ctor_get_uint8(v_src_3027_, sizeof(void*)*1);
if (v_copy_3107_ == 0)
{
lean_object* v_dir_3108_; 
lean_dec_ref(v_relPkgsDir_2966_);
v_dir_3108_ = lean_ctor_get(v_src_3027_, 0);
lean_inc_ref(v_dir_3108_);
lean_dec_ref_known(v_src_3027_, 1);
v_a_3097_ = v_dir_3108_;
goto v___jp_3096_;
}
else
{
lean_object* v_dir_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3135_; 
v_dir_3109_ = lean_ctor_get(v_src_3027_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_src_3027_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3111_ = v_src_3027_;
v_isShared_3112_ = v_isSharedCheck_3135_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_dir_3109_);
lean_dec(v_src_3027_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3135_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v_relDst_3115_; lean_object* v_dst_3116_; uint8_t v___x_3117_; 
v___x_3113_ = 0;
lean_inc(v_name_3025_);
v___x_3114_ = l_Lean_Name_toString(v_name_3025_, v___x_3113_);
v_relDst_3115_ = l_Lake_joinRelative(v_relPkgsDir_2966_, v___x_3114_);
lean_inc_ref(v_relDst_3115_);
lean_inc_ref(v_wsDir_2965_);
v_dst_3116_ = l_Lake_joinRelative(v_wsDir_2965_, v_relDst_3115_);
v___x_3117_ = l_System_FilePath_pathExists(v_dst_3116_);
if (v___x_3117_ == 0)
{
lean_object* v_src_3118_; lean_object* v___x_3119_; 
lean_inc_ref(v_wsDir_2965_);
v_src_3118_ = l_Lake_joinRelative(v_wsDir_2965_, v_dir_3109_);
v___x_3119_ = l_Lake_copyDirAll(v_src_3118_, v_dst_3116_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_dec_ref_known(v___x_3119_, 1);
lean_del_object(v___x_3111_);
v_a_3097_ = v_relDst_3115_;
goto v___jp_3096_;
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v_relDst_3115_);
lean_dec_ref(v_wsDir_2965_);
lean_dec_ref(v_manifestEntry_2963_);
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3122_ = v___x_3119_;
v_isShared_3123_ = v_isSharedCheck_3134_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3134_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3127_; 
v___x_3124_ = lean_io_error_to_string(v_a_3120_);
v___x_3125_ = 3;
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3124_);
v___x_3127_ = v___x_3111_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3124_);
v___x_3127_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*1, v___x_3125_);
lean_inc_ref(v_a_2967_);
v___x_3128_ = lean_apply_2(v_a_2967_, v___x_3127_, lean_box(0));
v___x_3129_ = lean_box(0);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3129_);
v___x_3131_ = v___x_3122_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
else
{
lean_dec_ref(v_dst_3116_);
lean_del_object(v___x_3111_);
lean_dec_ref(v_dir_3109_);
v_a_3097_ = v_relDst_3115_;
goto v___jp_3096_;
}
}
}
}
else
{
lean_object* v_url_3136_; lean_object* v_rev_3137_; lean_object* v_subDir_x3f_3138_; lean_object* v_pkgUrlMap_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v_a_3146_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v_val_3185_; lean_object* v_relGitDir_3200_; lean_object* v_repo_3201_; lean_object* v_url_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_url_3136_ = lean_ctor_get(v_src_3027_, 0);
lean_inc_ref(v_url_3136_);
v_rev_3137_ = lean_ctor_get(v_src_3027_, 1);
lean_inc_ref(v_rev_3137_);
v_subDir_x3f_3138_ = lean_ctor_get(v_src_3027_, 3);
lean_inc(v_subDir_x3f_3138_);
lean_dec_ref_known(v_src_3027_, 4);
v_pkgUrlMap_3139_ = lean_ctor_get(v_lakeEnv_2964_, 5);
v___x_3140_ = 0;
lean_inc(v_name_3025_);
v___x_3141_ = l_Lean_Name_toString(v_name_3025_, v___x_3140_);
lean_inc_ref_n(v___x_3141_, 2);
v_relGitDir_3200_ = l_Lake_joinRelative(v_relPkgsDir_2966_, v___x_3141_);
lean_inc_ref(v_relGitDir_3200_);
lean_inc_ref(v_wsDir_2965_);
v_repo_3201_ = l_Lake_joinRelative(v_wsDir_2965_, v_relGitDir_3200_);
v_url_3202_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_pkgUrlMap_3139_, v_name_3025_, v_url_3136_);
lean_dec_ref(v_url_3136_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_rev_3137_);
lean_inc(v_url_3202_);
v___x_3204_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2967_, v___x_3141_, v_repo_3201_, v_url_3202_, v___x_3203_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3217_; 
lean_dec_ref_known(v___x_3204_, 1);
if (lean_obj_tag(v_subDir_x3f_3138_) == 0)
{
v___y_3217_ = v_relGitDir_3200_;
goto v___jp_3216_;
}
else
{
lean_object* v_val_3221_; lean_object* v___x_3222_; 
v_val_3221_ = lean_ctor_get(v_subDir_x3f_3138_, 0);
lean_inc(v_val_3221_);
lean_dec_ref_known(v_subDir_x3f_3138_, 1);
v___x_3222_ = l_Lake_joinRelative(v_relGitDir_3200_, v_val_3221_);
v___y_3217_ = v___x_3222_;
goto v___jp_3216_;
}
v___jp_3205_:
{
lean_object* v_pkgDir_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
lean_inc_ref(v___y_3206_);
v_pkgDir_3208_ = l_Lake_joinRelative(v_wsDir_2965_, v___y_3206_);
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3208_);
v___x_3211_ = l_Lake_resolvePath(v_pkgDir_3208_);
v___x_3212_ = lean_string_utf8_byte_size(v___x_3211_);
v___x_3213_ = lean_nat_dec_eq(v___x_3212_, v___x_3209_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3211_);
v___y_3180_ = v___x_3210_;
v___y_3181_ = v___y_3206_;
v___y_3182_ = v___x_3209_;
v___y_3183_ = v_pkgDir_3208_;
v___y_3184_ = v___y_3207_;
v_val_3185_ = v___x_3214_;
goto v___jp_3179_;
}
else
{
lean_object* v___x_3215_; 
lean_dec_ref(v___x_3211_);
v___x_3215_ = lean_box(0);
v___y_3180_ = v___x_3210_;
v___y_3181_ = v___y_3206_;
v___y_3182_ = v___x_3209_;
v___y_3183_ = v_pkgDir_3208_;
v___y_3184_ = v___y_3207_;
v_val_3185_ = v___x_3215_;
goto v___jp_3179_;
}
}
v___jp_3216_:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lake_Git_filterUrl_x3f(v_url_3202_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v___x_3219_; 
v___x_3219_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_3206_ = v___y_3217_;
v___y_3207_ = v___x_3219_;
goto v___jp_3205_;
}
else
{
lean_object* v_val_3220_; 
v_val_3220_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v___x_3218_, 1);
v___y_3206_ = v___y_3217_;
v___y_3207_ = v_val_3220_;
goto v___jp_3205_;
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec(v_url_3202_);
lean_dec_ref(v_relGitDir_3200_);
lean_dec_ref(v___x_3141_);
lean_dec(v_subDir_x3f_3138_);
lean_dec_ref(v_wsDir_2965_);
lean_dec_ref(v_manifestEntry_2963_);
v_a_3223_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3204_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3204_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
v___jp_3142_:
{
if (lean_obj_tag(v_a_3146_) == 1)
{
lean_dec_ref(v___y_3144_);
lean_dec_ref(v___x_3141_);
if (lean_obj_tag(v_manifestFile_x3f_3026_) == 1)
{
lean_object* v_val_3147_; lean_object* v_val_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_val_3147_ = lean_ctor_get(v_a_3146_, 0);
lean_inc_n(v_val_3147_, 2);
lean_dec_ref_known(v_a_3146_, 1);
v_val_3148_ = lean_ctor_get(v_manifestFile_x3f_3026_, 0);
lean_inc(v_val_3148_);
v___x_3149_ = l_Lake_joinRelative(v_val_3147_, v_val_3148_);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3152_ = l_Lake_Manifest_load(v___x_3149_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 1);
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
v___y_2977_ = v___x_3150_;
v___y_2978_ = v_val_3147_;
v___y_2979_ = v___y_3143_;
v___y_2980_ = v___x_3151_;
v___y_2981_ = v___y_3145_;
v_val_2982_ = v___x_3158_;
goto v___jp_2976_;
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_a_3161_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3152_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3152_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 0);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
v___y_2977_ = v___x_3150_;
v___y_2978_ = v_val_3147_;
v___y_2979_ = v___y_3143_;
v___y_2980_ = v___x_3151_;
v___y_2981_ = v___y_3145_;
v_val_2982_ = v___x_3166_;
goto v___jp_2976_;
}
}
}
}
else
{
lean_object* v_val_3169_; lean_object* v___x_3170_; 
v_val_3169_ = lean_ctor_get(v_a_3146_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v_a_3146_, 1);
v___x_3170_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2970_ = v___y_3143_;
v___y_2971_ = v_val_3169_;
v___y_2972_ = v___y_3145_;
v_a_2973_ = v___x_3170_;
goto v___jp_2969_;
}
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_dec(v_a_3146_);
lean_dec_ref(v___y_3145_);
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_manifestEntry_2963_);
v___x_3171_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3172_ = lean_string_append(v___x_3141_, v___x_3171_);
v___x_3173_ = lean_string_append(v___x_3172_, v___y_3144_);
lean_dec_ref(v___y_3144_);
v___x_3174_ = 3;
v___x_3175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*1, v___x_3174_);
lean_inc_ref(v_a_2967_);
v___x_3176_ = lean_apply_2(v_a_2967_, v___x_3175_, lean_box(0));
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
v___jp_3179_:
{
lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = lean_array_get_size(v___y_3180_);
v___x_3187_ = lean_nat_dec_lt(v___y_3182_, v___x_3186_);
if (v___x_3187_ == 0)
{
v___y_3143_ = v___y_3181_;
v___y_3144_ = v___y_3183_;
v___y_3145_ = v___y_3184_;
v_a_3146_ = v_val_3185_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3188_; size_t v___x_3189_; size_t v___x_3190_; lean_object* v___x_3191_; 
v___x_3188_ = lean_box(0);
v___x_3189_ = ((size_t)0ULL);
v___x_3190_ = lean_usize_of_nat(v___x_3186_);
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3180_, v___x_3189_, v___x_3190_, v___x_3188_, v_a_2967_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_dec_ref_known(v___x_3191_, 1);
v___y_3143_ = v___y_3181_;
v___y_3144_ = v___y_3183_;
v___y_3145_ = v___y_3184_;
v_a_3146_ = v_val_3185_;
goto v___jp_3142_;
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec(v_val_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v_manifestEntry_2963_);
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
}
v___jp_2969_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2974_, 0, v___y_2971_);
lean_ctor_set(v___x_2974_, 1, v___y_2970_);
lean_ctor_set(v___x_2974_, 2, v___y_2972_);
lean_ctor_set(v___x_2974_, 3, v_a_2973_);
lean_ctor_set(v___x_2974_, 4, v_manifestEntry_2963_);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
v___jp_2976_:
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = lean_array_get_size(v___y_2980_);
v___x_2984_ = lean_nat_dec_lt(v___y_2977_, v___x_2983_);
if (v___x_2984_ == 0)
{
v___y_2970_ = v___y_2979_;
v___y_2971_ = v___y_2978_;
v___y_2972_ = v___y_2981_;
v_a_2973_ = v_val_2982_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2985_ = lean_box(0);
v___x_2986_ = ((size_t)0ULL);
v___x_2987_ = lean_usize_of_nat(v___x_2983_);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2980_, v___x_2986_, v___x_2987_, v___x_2985_, v_a_2967_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_dec_ref_known(v___x_2988_, 1);
v___y_2970_ = v___y_2979_;
v___y_2971_ = v___y_2978_;
v___y_2972_ = v___y_2981_;
v_a_2973_ = v_val_2982_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_val_2982_);
lean_dec_ref(v___y_2981_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v_manifestEntry_2963_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
v___jp_2997_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_inc_ref(v___y_3000_);
v___x_3002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3002_, 0, v___y_2998_);
lean_ctor_set(v___x_3002_, 1, v___y_2999_);
lean_ctor_set(v___x_3002_, 2, v___y_3000_);
lean_ctor_set(v___x_3002_, 3, v_a_3001_);
lean_ctor_set(v___x_3002_, 4, v_manifestEntry_2963_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
v___jp_3004_:
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = lean_array_get_size(v___y_3009_);
v___x_3012_ = lean_nat_dec_lt(v___y_3006_, v___x_3011_);
if (v___x_3012_ == 0)
{
v___y_2998_ = v___y_3005_;
v___y_2999_ = v___y_3007_;
v___y_3000_ = v___y_3008_;
v_a_3001_ = v_val_3010_;
goto v___jp_2997_;
}
else
{
lean_object* v___x_3013_; size_t v___x_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3013_ = lean_box(0);
v___x_3014_ = ((size_t)0ULL);
v___x_3015_ = lean_usize_of_nat(v___x_3011_);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3009_, v___x_3014_, v___x_3015_, v___x_3013_, v_a_2967_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_dec_ref_known(v___x_3016_, 1);
v___y_2998_ = v___y_3005_;
v___y_2999_ = v___y_3007_;
v___y_3000_ = v___y_3008_;
v_a_3001_ = v_val_3010_;
goto v___jp_2997_;
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v_val_3010_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v___y_3005_);
lean_dec_ref(v_manifestEntry_2963_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
v___jp_3028_:
{
if (lean_obj_tag(v_a_3032_) == 1)
{
lean_dec_ref(v___y_3029_);
if (lean_obj_tag(v_manifestFile_x3f_3026_) == 1)
{
lean_object* v_val_3033_; lean_object* v_val_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_val_3033_ = lean_ctor_get(v_a_3032_, 0);
lean_inc_n(v_val_3033_, 2);
lean_dec_ref_known(v_a_3032_, 1);
v_val_3034_ = lean_ctor_get(v_manifestFile_x3f_3026_, 0);
lean_inc(v_val_3034_);
v___x_3035_ = l_Lake_joinRelative(v_val_3033_, v_val_3034_);
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3038_ = l_Lake_Manifest_load(v___x_3035_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 1);
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
v___y_3005_ = v_val_3033_;
v___y_3006_ = v___x_3036_;
v___y_3007_ = v___y_3030_;
v___y_3008_ = v___y_3031_;
v___y_3009_ = v___x_3037_;
v_val_3010_ = v___x_3044_;
goto v___jp_3004_;
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v_a_3047_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3038_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3038_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set_tag(v___x_3049_, 0);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
v___y_3005_ = v_val_3033_;
v___y_3006_ = v___x_3036_;
v___y_3007_ = v___y_3030_;
v___y_3008_ = v___y_3031_;
v___y_3009_ = v___x_3037_;
v_val_3010_ = v___x_3052_;
goto v___jp_3004_;
}
}
}
}
else
{
lean_object* v_val_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3064_; 
v_val_3055_ = lean_ctor_get(v_a_3032_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_3032_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3057_ = v_a_3032_;
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_val_3055_);
lean_dec(v_a_3032_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
uint32_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3059_ = 0;
lean_inc_ref_n(v___y_3031_, 2);
v___x_3060_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_3060_, 0, v___y_3031_);
lean_ctor_set(v___x_3060_, 1, v___y_3031_);
lean_ctor_set_uint32(v___x_3060_, sizeof(void*)*2, v___x_3059_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set_tag(v___x_3057_, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3060_);
v___x_3062_ = v___x_3057_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
v___y_2998_ = v_val_3055_;
v___y_2999_ = v___y_3030_;
v___y_3000_ = v___y_3031_;
v_a_3001_ = v___x_3062_;
goto v___jp_2997_;
}
}
}
}
else
{
uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_inc(v_name_3025_);
lean_dec(v_a_3032_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v_manifestEntry_2963_);
v___x_3065_ = 0;
v___x_3066_ = l_Lean_Name_toString(v_name_3025_, v___x_3065_);
v___x_3067_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3068_ = lean_string_append(v___x_3066_, v___x_3067_);
v___x_3069_ = lean_string_append(v___x_3068_, v___y_3029_);
lean_dec_ref(v___y_3029_);
v___x_3070_ = 3;
v___x_3071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*1, v___x_3070_);
lean_inc_ref(v_a_2967_);
v___x_3072_ = lean_apply_2(v_a_2967_, v___x_3071_, lean_box(0));
v___x_3073_ = lean_box(0);
v___x_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
}
v___jp_3075_:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = lean_array_get_size(v___y_3078_);
v___x_3083_ = lean_nat_dec_lt(v___y_3080_, v___x_3082_);
if (v___x_3083_ == 0)
{
v___y_3029_ = v___y_3076_;
v___y_3030_ = v___y_3077_;
v___y_3031_ = v___y_3079_;
v_a_3032_ = v_val_3081_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; lean_object* v___x_3087_; 
v___x_3084_ = lean_box(0);
v___x_3085_ = ((size_t)0ULL);
v___x_3086_ = lean_usize_of_nat(v___x_3082_);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3078_, v___x_3085_, v___x_3086_, v___x_3084_, v_a_2967_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_dec_ref_known(v___x_3087_, 1);
v___y_3029_ = v___y_3076_;
v___y_3030_ = v___y_3077_;
v___y_3031_ = v___y_3079_;
v_a_3032_ = v_val_3081_;
goto v___jp_3028_;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_val_3081_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec_ref(v_manifestEntry_2963_);
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
v___jp_3096_:
{
lean_object* v___x_3098_; lean_object* v_pkgDir_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3098_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_a_3097_);
v_pkgDir_3099_ = l_Lake_joinRelative(v_wsDir_2965_, v_a_3097_);
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3099_);
v___x_3102_ = l_Lake_resolvePath(v_pkgDir_3099_);
v___x_3103_ = lean_string_utf8_byte_size(v___x_3102_);
v___x_3104_ = lean_nat_dec_eq(v___x_3103_, v___x_3100_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3102_);
v___y_3076_ = v_pkgDir_3099_;
v___y_3077_ = v_a_3097_;
v___y_3078_ = v___x_3101_;
v___y_3079_ = v___x_3098_;
v___y_3080_ = v___x_3100_;
v_val_3081_ = v___x_3105_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3106_; 
lean_dec_ref(v___x_3102_);
v___x_3106_ = lean_box(0);
v___y_3076_ = v_pkgDir_3099_;
v___y_3077_ = v_a_3097_;
v___y_3078_ = v___x_3101_;
v___y_3079_ = v___x_3098_;
v___y_3080_ = v___x_3100_;
v_val_3081_ = v___x_3106_;
goto v___jp_3075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_3231_, lean_object* v_lakeEnv_3232_, lean_object* v_wsDir_3233_, lean_object* v_relPkgsDir_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lake_PackageEntry_materialize(v_manifestEntry_3231_, v_lakeEnv_3232_, v_wsDir_3233_, v_relPkgsDir_3234_, v_a_3235_);
lean_dec_ref(v_a_3235_);
lean_dec_ref(v_lakeEnv_3232_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object* v_00_u03b4_3238_, lean_object* v_t_3239_, lean_object* v_k_3240_, lean_object* v_fallback_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3239_, v_k_3240_, v_fallback_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object* v_00_u03b4_3243_, lean_object* v_t_3244_, lean_object* v_k_3245_, lean_object* v_fallback_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(v_00_u03b4_3243_, v_t_3244_, v_k_3245_, v_fallback_3246_);
lean_dec(v_fallback_3246_);
lean_dec(v_k_3245_);
lean_dec(v_t_3244_);
return v_res_3247_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Reservoir(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Materialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
