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
v___x_54_ = lean_array_get_size(v___y_50_);
v___x_55_ = lean_nat_dec_lt(v___y_52_, v___x_54_);
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
lean_inc_ref(v___y_50_);
lean_inc_ref(v___y_51_);
v___x_1563__overap_59_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_51_, v___f_48_, v___y_50_, v___x_57_, v___x_58_, v___x_56_);
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
v___y_50_ = v___x_74_;
v___y_51_ = v___x_72_;
v___y_52_ = v___x_73_;
v_val_53_ = v___x_78_;
goto v___jp_49_;
}
else
{
lean_object* v___x_79_; 
lean_dec_ref(v___x_75_);
v___x_79_ = lean_box(0);
v___y_50_ = v___x_74_;
v___y_51_ = v___x_72_;
v___y_52_ = v___x_73_;
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
uint8_t v_a_145_; lean_object* v___f_155_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; uint8_t v_val_160_; lean_object* v___y_176_; lean_object* v___y_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___f_155_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
v___x_210_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_139_);
v___x_211_ = lean_string_append(v_name_139_, v___x_210_);
v___x_212_ = lean_string_append(v___x_211_, v_rev_141_);
v___x_213_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_214_ = lean_string_append(v___x_212_, v___x_213_);
v___x_215_ = 1;
v___x_216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*1, v___x_215_);
lean_inc_ref(v_a_142_);
v___x_217_ = lean_apply_2(v_a_142_, v___x_216_, lean_box(0));
v___x_218_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_140_);
v___x_221_ = l_Lake_GitRepo_checkoutDetach(v_rev_141_, v_repo_140_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_a_222_ = lean_ctor_get(v___x_221_, 1);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_221_, 2);
v___x_223_ = lean_array_get_size(v_a_222_);
v___x_224_ = lean_nat_dec_lt(v___x_219_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v_a_222_);
goto v___jp_177_;
}
else
{
lean_object* v___x_225_; size_t v___x_226_; size_t v___x_227_; lean_object* v___x_2319__overap_228_; lean_object* v___x_229_; 
v___x_225_ = lean_box(0);
v___x_226_ = ((size_t)0ULL);
v___x_227_ = lean_usize_of_nat(v___x_223_);
v___x_2319__overap_228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_218_, v___f_155_, v_a_222_, v___x_226_, v___x_227_, v___x_225_);
lean_inc_ref(v_a_142_);
v___x_229_ = lean_apply_2(v___x_2319__overap_228_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_229_) == 0)
{
lean_dec_ref_known(v___x_229_, 1);
goto v___jp_177_;
}
else
{
v___y_209_ = v___x_229_;
goto v___jp_208_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_a_230_ = lean_ctor_get(v___x_221_, 1);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_221_, 2);
v___x_231_ = lean_array_get_size(v_a_230_);
v___x_232_ = lean_nat_dec_lt(v___x_219_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_a_230_);
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; lean_object* v___x_2336__overap_238_; lean_object* v___x_239_; 
v___x_235_ = lean_box(0);
v___x_236_ = ((size_t)0ULL);
v___x_237_ = lean_usize_of_nat(v___x_231_);
v___x_2336__overap_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_218_, v___f_155_, v_a_230_, v___x_236_, v___x_237_, v___x_235_);
lean_inc_ref(v_a_142_);
v___x_239_ = lean_apply_2(v___x_2336__overap_238_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v___x_239_, 0);
lean_dec(v_unused_247_);
v___x_241_ = v___x_239_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_dec(v___x_239_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 0, v___x_235_);
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_235_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
v___y_209_ = v___x_239_;
goto v___jp_208_;
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
v___x_161_ = lean_array_get_size(v___y_159_);
v___x_162_ = lean_nat_dec_lt(v___y_157_, v___x_161_);
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
lean_inc_ref(v___y_159_);
lean_inc_ref(v___y_158_);
v___x_2656__overap_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_158_, v___f_155_, v___y_159_, v___x_164_, v___x_165_, v___x_163_);
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
v___y_157_ = v___x_170_;
v___y_158_ = v___x_169_;
v___y_159_ = v___x_171_;
v_val_160_ = v___x_173_;
goto v___jp_156_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = 0;
v___y_157_ = v___x_170_;
v___y_158_ = v___x_169_;
v___y_159_ = v___x_171_;
v_val_160_ = v___x_174_;
goto v___jp_156_;
}
}
v___jp_175_:
{
if (lean_obj_tag(v___y_176_) == 0)
{
lean_dec_ref_known(v___y_176_, 1);
goto v___jp_168_;
}
else
{
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
return v___y_176_;
}
}
v___jp_177_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_140_);
v___x_181_ = l_Lake_GitRepo_clean(v_repo_140_, v___x_180_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_a_182_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 2);
v___x_183_ = lean_array_get_size(v_a_182_);
v___x_184_ = lean_nat_dec_lt(v___x_179_, v___x_183_);
if (v___x_184_ == 0)
{
lean_dec(v_a_182_);
goto v___jp_168_;
}
else
{
lean_object* v___x_185_; size_t v___x_186_; size_t v___x_187_; lean_object* v___x_2692__overap_188_; lean_object* v___x_189_; 
v___x_185_ = lean_box(0);
v___x_186_ = ((size_t)0ULL);
v___x_187_ = lean_usize_of_nat(v___x_183_);
v___x_2692__overap_188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_178_, v___f_155_, v_a_182_, v___x_186_, v___x_187_, v___x_185_);
lean_inc_ref(v_a_142_);
v___x_189_ = lean_apply_2(v___x_2692__overap_188_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_189_) == 0)
{
lean_dec_ref_known(v___x_189_, 1);
goto v___jp_168_;
}
else
{
v___y_176_ = v___x_189_;
goto v___jp_175_;
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_a_190_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_181_, 2);
v___x_191_ = lean_array_get_size(v_a_190_);
v___x_192_ = lean_nat_dec_lt(v___x_179_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_a_190_);
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_2709__overap_198_; lean_object* v___x_199_; 
v___x_195_ = lean_box(0);
v___x_196_ = ((size_t)0ULL);
v___x_197_ = lean_usize_of_nat(v___x_191_);
v___x_2709__overap_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_178_, v___f_155_, v_a_190_, v___x_196_, v___x_197_, v___x_195_);
lean_inc_ref(v_a_142_);
v___x_199_ = lean_apply_2(v___x_2709__overap_198_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_199_, 0);
lean_dec(v_unused_207_);
v___x_201_ = v___x_199_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_dec(v___x_199_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 1);
lean_ctor_set(v___x_201_, 0, v___x_195_);
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_195_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
v___y_176_ = v___x_199_;
goto v___jp_175_;
}
}
}
}
v___jp_208_:
{
if (lean_obj_tag(v___y_209_) == 0)
{
lean_dec_ref_known(v___y_209_, 1);
goto v___jp_177_;
}
else
{
lean_dec_ref(v_repo_140_);
lean_dec_ref(v_name_139_);
return v___y_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___boxed(lean_object* v_name_248_, lean_object* v_repo_249_, lean_object* v_rev_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout(v_name_248_, v_repo_249_, v_rev_250_, v_a_251_);
lean_dec_ref(v_a_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object* v_as_254_, size_t v_i_255_, size_t v_stop_256_, lean_object* v_b_257_, lean_object* v___y_258_){
_start:
{
uint8_t v___x_260_; 
v___x_260_ = lean_usize_dec_eq(v_i_255_, v_stop_256_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; size_t v___x_263_; size_t v___x_264_; 
v___x_261_ = lean_array_uget_borrowed(v_as_254_, v_i_255_);
lean_inc_ref(v___y_258_);
lean_inc(v___x_261_);
v___x_262_ = lean_apply_2(v___y_258_, v___x_261_, lean_box(0));
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_255_, v___x_263_);
v_i_255_ = v___x_264_;
v_b_257_ = v___x_262_;
goto _start;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_b_257_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object* v_as_267_, lean_object* v_i_268_, lean_object* v_stop_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
size_t v_i_boxed_273_; size_t v_stop_boxed_274_; lean_object* v_res_275_; 
v_i_boxed_273_ = lean_unbox_usize(v_i_268_);
lean_dec(v_i_268_);
v_stop_boxed_274_ = lean_unbox_usize(v_stop_269_);
lean_dec(v_stop_269_);
v_res_275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_as_267_, v_i_boxed_273_, v_stop_boxed_274_, v_b_270_, v___y_271_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v_as_267_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* v_name_285_, lean_object* v_repo_286_, lean_object* v_url_287_, lean_object* v_rev_x3f_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___y_301_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_373_; lean_object* v___y_374_; uint8_t v_a_375_; lean_object* v___y_383_; uint8_t v_a_384_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; uint8_t v_val_396_; uint8_t v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; uint8_t v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; uint8_t v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; uint8_t v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; uint8_t v_val_456_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v_a_468_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v_a_515_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_620_; uint8_t v_a_621_; lean_object* v___y_629_; uint8_t v_a_630_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; uint8_t v_val_641_; lean_object* v___y_649_; uint8_t v___y_650_; uint8_t v___y_651_; lean_object* v___y_656_; uint8_t v___y_657_; uint8_t v___y_658_; lean_object* v___y_659_; lean_object* v___y_661_; uint8_t v___y_662_; uint8_t v___y_663_; lean_object* v___y_692_; uint8_t v___y_693_; uint8_t v___y_694_; lean_object* v___y_695_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; uint8_t v___y_700_; uint8_t v___y_701_; lean_object* v___y_702_; lean_object* v_a_703_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; uint8_t v_val_750_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v_a_762_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v_a_805_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; uint8_t v_a_881_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v_a_945_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v_a_958_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v_val_973_; lean_object* v___y_981_; lean_object* v___y_982_; uint8_t v_a_983_; lean_object* v___y_992_; 
if (lean_obj_tag(v_rev_x3f_288_) == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lake_Git_upstreamBranch;
v___y_992_ = v___x_1001_;
goto v___jp_991_;
}
else
{
lean_object* v_val_1002_; 
v_val_1002_ = lean_ctor_get(v_rev_x3f_288_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v_rev_x3f_288_, 1);
v___y_992_ = v_val_1002_;
goto v___jp_991_;
}
v___jp_291_:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
v___jp_294_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
v___jp_297_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_box(0);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_304_ = l_Lake_GitRepo_gcAuto(v_repo_286_, v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v_a_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
v_a_306_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_304_, 2);
v___x_307_ = lean_array_get_size(v_a_306_);
v___x_308_ = lean_nat_dec_lt(v___x_302_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v_a_306_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v_a_305_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_box(0);
v___x_311_ = ((size_t)0ULL);
v___x_312_ = lean_usize_of_nat(v___x_307_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_306_, v___x_311_, v___x_312_, v___x_310_, v___y_301_);
lean_dec(v_a_306_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_321_);
v___x_315_ = v___x_313_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___x_313_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_a_305_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_305_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_dec(v_a_305_);
return v___x_313_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_304_, 2);
v___x_323_ = lean_array_get_size(v_a_322_);
v___x_324_ = lean_nat_dec_lt(v___x_302_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_a_322_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_327_ = lean_box(0);
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_323_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_322_, v___x_328_, v___x_329_, v___x_327_, v___y_301_);
lean_dec(v_a_322_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v___x_330_, 0);
lean_dec(v_unused_338_);
v___x_332_ = v___x_330_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_dec(v___x_330_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 0, v___x_327_);
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_327_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
return v___x_330_;
}
}
}
}
v___jp_339_:
{
if (lean_obj_tag(v___y_341_) == 0)
{
lean_dec_ref_known(v___y_341_, 1);
v___y_301_ = v___y_340_;
goto v___jp_300_;
}
else
{
lean_dec_ref(v_repo_286_);
return v___y_341_;
}
}
v___jp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
lean_inc_ref(v___y_344_);
v___x_347_ = l_Lake_GitRepo_pruneRemote(v___y_344_, v_repo_286_, v___x_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_a_348_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 2);
v___x_349_ = lean_array_get_size(v_a_348_);
v___x_350_ = lean_nat_dec_lt(v___x_345_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec(v_a_348_);
v___y_301_ = v___y_343_;
goto v___jp_300_;
}
else
{
lean_object* v___x_351_; size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_351_ = lean_box(0);
v___x_352_ = ((size_t)0ULL);
v___x_353_ = lean_usize_of_nat(v___x_349_);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_348_, v___x_352_, v___x_353_, v___x_351_, v___y_343_);
lean_dec(v_a_348_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_dec_ref_known(v___x_354_, 1);
v___y_301_ = v___y_343_;
goto v___jp_300_;
}
else
{
v___y_340_ = v___y_343_;
v___y_341_ = v___x_354_;
goto v___jp_339_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_a_355_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_347_, 2);
v___x_356_ = lean_array_get_size(v_a_355_);
v___x_357_ = lean_nat_dec_lt(v___x_345_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_a_355_);
lean_dec_ref(v_repo_286_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v___x_360_ = lean_box(0);
v___x_361_ = ((size_t)0ULL);
v___x_362_ = lean_usize_of_nat(v___x_356_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_355_, v___x_361_, v___x_362_, v___x_360_, v___y_343_);
lean_dec(v_a_355_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v_repo_286_);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_371_);
v___x_365_ = v___x_363_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_dec(v___x_363_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
lean_ctor_set(v___x_365_, 0, v___x_360_);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_360_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
v___y_340_ = v___y_343_;
v___y_341_ = v___x_363_;
goto v___jp_339_;
}
}
}
}
v___jp_372_:
{
if (v_a_375_ == 0)
{
lean_dec_ref(v_name_285_);
v___y_343_ = v___y_373_;
v___y_344_ = v___y_374_;
goto v___jp_342_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_376_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_377_ = lean_string_append(v_name_285_, v___x_376_);
v___x_378_ = lean_string_append(v___x_377_, v_repo_286_);
v___x_379_ = 2;
v___x_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v___x_379_);
lean_inc_ref(v___y_373_);
v___x_381_ = lean_apply_2(v___y_373_, v___x_380_, lean_box(0));
v___y_343_ = v___y_373_;
v___y_344_ = v___y_374_;
goto v___jp_342_;
}
}
v___jp_382_:
{
if (v_a_384_ == 0)
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
goto v___jp_297_;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_385_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_386_ = lean_string_append(v_name_285_, v___x_385_);
v___x_387_ = lean_string_append(v___x_386_, v_repo_286_);
lean_dec_ref(v_repo_286_);
v___x_388_ = 2;
v___x_389_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_388_);
lean_inc_ref(v___y_383_);
v___x_390_ = lean_apply_2(v___y_383_, v___x_389_, lean_box(0));
goto v___jp_297_;
}
}
v___jp_391_:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_array_get_size(v___y_395_);
v___x_398_ = lean_nat_dec_lt(v___y_392_, v___x_397_);
if (v___x_398_ == 0)
{
v___y_373_ = v___y_393_;
v___y_374_ = v___y_394_;
v_a_375_ = v_val_396_;
goto v___jp_372_;
}
else
{
lean_object* v___x_399_; size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_box(0);
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_397_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_395_, v___x_400_, v___x_401_, v___x_399_, v___y_393_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_dec_ref_known(v___x_402_, 1);
v___y_373_ = v___y_393_;
v___y_374_ = v___y_394_;
v_a_375_ = v_val_396_;
goto v___jp_372_;
}
else
{
lean_dec_ref(v_name_285_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_dec_ref_known(v___x_402_, 1);
v___y_343_ = v___y_393_;
v___y_344_ = v___y_394_;
goto v___jp_342_;
}
else
{
lean_dec_ref(v_repo_286_);
return v___x_402_;
}
}
}
}
v___jp_403_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_409_ = l_Lake_GitRepo_hasNoDiff(v_repo_286_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = 1;
v___y_392_ = v___x_407_;
v___y_393_ = v___y_405_;
v___y_394_ = v___y_406_;
v___y_395_ = v___x_408_;
v_val_396_ = v___x_410_;
goto v___jp_391_;
}
else
{
v___y_392_ = v___x_407_;
v___y_393_ = v___y_405_;
v___y_394_ = v___y_406_;
v___y_395_ = v___x_408_;
v_val_396_ = v___y_404_;
goto v___jp_391_;
}
}
v___jp_411_:
{
if (lean_obj_tag(v___y_415_) == 0)
{
lean_dec_ref_known(v___y_415_, 1);
v___y_404_ = v___y_412_;
v___y_405_ = v___y_413_;
v___y_406_ = v___y_414_;
goto v___jp_403_;
}
else
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_415_;
}
}
v___jp_416_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_422_ = l_Lake_GitRepo_clean(v_repo_286_, v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 2);
v___x_424_ = lean_array_get_size(v_a_423_);
v___x_425_ = lean_nat_dec_lt(v___x_420_, v___x_424_);
if (v___x_425_ == 0)
{
lean_dec(v_a_423_);
v___y_404_ = v___y_417_;
v___y_405_ = v___y_418_;
v___y_406_ = v___y_419_;
goto v___jp_403_;
}
else
{
lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_426_ = lean_box(0);
v___x_427_ = ((size_t)0ULL);
v___x_428_ = lean_usize_of_nat(v___x_424_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_423_, v___x_427_, v___x_428_, v___x_426_, v___y_418_);
lean_dec(v_a_423_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_dec_ref_known(v___x_429_, 1);
v___y_404_ = v___y_417_;
v___y_405_ = v___y_418_;
v___y_406_ = v___y_419_;
goto v___jp_403_;
}
else
{
v___y_412_ = v___y_417_;
v___y_413_ = v___y_418_;
v___y_414_ = v___y_419_;
v___y_415_ = v___x_429_;
goto v___jp_411_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_422_, 2);
v___x_431_ = lean_array_get_size(v_a_430_);
v___x_432_ = lean_nat_dec_lt(v___x_420_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_a_430_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_435_ = lean_box(0);
v___x_436_ = ((size_t)0ULL);
v___x_437_ = lean_usize_of_nat(v___x_431_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_430_, v___x_436_, v___x_437_, v___x_435_, v___y_418_);
lean_dec(v_a_430_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_438_, 0);
lean_dec(v_unused_446_);
v___x_440_ = v___x_438_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_dec(v___x_438_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 1);
lean_ctor_set(v___x_440_, 0, v___x_435_);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_435_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
v___y_412_ = v___y_417_;
v___y_413_ = v___y_418_;
v___y_414_ = v___y_419_;
v___y_415_ = v___x_438_;
goto v___jp_411_;
}
}
}
}
v___jp_447_:
{
if (lean_obj_tag(v___y_451_) == 0)
{
lean_dec_ref_known(v___y_451_, 1);
v___y_417_ = v___y_448_;
v___y_418_ = v___y_449_;
v___y_419_ = v___y_450_;
goto v___jp_416_;
}
else
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_451_;
}
}
v___jp_452_:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_array_get_size(v___y_455_);
v___x_458_ = lean_nat_dec_lt(v___y_453_, v___x_457_);
if (v___x_458_ == 0)
{
v___y_383_ = v___y_454_;
v_a_384_ = v_val_456_;
goto v___jp_382_;
}
else
{
lean_object* v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v___x_459_ = lean_box(0);
v___x_460_ = ((size_t)0ULL);
v___x_461_ = lean_usize_of_nat(v___x_457_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_455_, v___x_460_, v___x_461_, v___x_459_, v___y_454_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_dec_ref_known(v___x_462_, 1);
v___y_383_ = v___y_454_;
v_a_384_ = v_val_456_;
goto v___jp_382_;
}
else
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_dec_ref_known(v___x_462_, 1);
goto v___jp_297_;
}
else
{
return v___x_462_;
}
}
}
}
v___jp_463_:
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_470_ = l_Option_instDecidableEq___redArg(v___x_469_, v_a_468_, v___y_467_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_471_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_285_);
v___x_472_ = lean_string_append(v_name_285_, v___x_471_);
v___x_473_ = lean_string_append(v___x_472_, v___y_464_);
v___x_474_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v___x_476_ = 1;
v___x_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
lean_inc_ref(v___y_465_);
v___x_478_ = lean_apply_2(v___y_465_, v___x_477_, lean_box(0));
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_481_ = l_Lake_GitRepo_checkoutDetach(v___y_464_, v_repo_286_, v___x_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_a_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 2);
v___x_483_ = lean_array_get_size(v_a_482_);
v___x_484_ = lean_nat_dec_lt(v___x_479_, v___x_483_);
if (v___x_484_ == 0)
{
lean_dec(v_a_482_);
v___y_417_ = v___x_470_;
v___y_418_ = v___y_465_;
v___y_419_ = v___y_466_;
goto v___jp_416_;
}
else
{
lean_object* v___x_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_485_ = lean_box(0);
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_483_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_482_, v___x_486_, v___x_487_, v___x_485_, v___y_465_);
lean_dec(v_a_482_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_dec_ref_known(v___x_488_, 1);
v___y_417_ = v___x_470_;
v___y_418_ = v___y_465_;
v___y_419_ = v___y_466_;
goto v___jp_416_;
}
else
{
v___y_448_ = v___x_470_;
v___y_449_ = v___y_465_;
v___y_450_ = v___y_466_;
v___y_451_ = v___x_488_;
goto v___jp_447_;
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_a_489_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_481_, 2);
v___x_490_ = lean_array_get_size(v_a_489_);
v___x_491_ = lean_nat_dec_lt(v___x_479_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v_a_489_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v___x_494_ = lean_box(0);
v___x_495_ = ((size_t)0ULL);
v___x_496_ = lean_usize_of_nat(v___x_490_);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_489_, v___x_495_, v___x_496_, v___x_494_, v___y_465_);
lean_dec(v_a_489_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v___x_497_, 0);
lean_dec(v_unused_505_);
v___x_499_ = v___x_497_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_dec(v___x_497_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 1);
lean_ctor_set(v___x_499_, 0, v___x_494_);
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_494_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
v___y_448_ = v___x_470_;
v___y_449_ = v___y_465_;
v___y_450_ = v___y_466_;
v___y_451_ = v___x_497_;
goto v___jp_447_;
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
lean_dec_ref(v___y_464_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_508_ = l_Lake_GitRepo_hasNoDiff(v_repo_286_);
if (v___x_508_ == 0)
{
v___y_453_ = v___x_506_;
v___y_454_ = v___y_465_;
v___y_455_ = v___x_507_;
v_val_456_ = v___x_470_;
goto v___jp_452_;
}
else
{
uint8_t v___x_509_; 
v___x_509_ = 0;
v___y_453_ = v___x_506_;
v___y_454_ = v___y_465_;
v___y_455_ = v___x_507_;
v_val_456_ = v___x_509_;
goto v___jp_452_;
}
}
}
v___jp_510_:
{
if (lean_obj_tag(v_a_515_) == 1)
{
lean_object* v_val_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
lean_dec_ref(v___y_514_);
lean_dec_ref(v___y_513_);
v_val_516_ = lean_ctor_get(v_a_515_, 0);
lean_inc(v_val_516_);
v___x_517_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_518_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_286_);
v___x_519_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_518_, v_repo_286_);
v___x_520_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_520_ == 0)
{
v___y_464_ = v_val_516_;
v___y_465_ = v___y_511_;
v___y_466_ = v___y_512_;
v___y_467_ = v_a_515_;
v_a_468_ = v___x_519_;
goto v___jp_463_;
}
else
{
lean_object* v___x_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_521_ = lean_box(0);
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_517_, v___x_522_, v___x_523_, v___x_521_, v___y_511_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_dec_ref_known(v___x_524_, 1);
v___y_464_ = v_val_516_;
v___y_465_ = v___y_511_;
v___y_466_ = v___y_512_;
v___y_467_ = v_a_515_;
v_a_468_ = v___x_519_;
goto v___jp_463_;
}
else
{
lean_dec(v___x_519_);
lean_dec_ref_known(v_a_515_, 1);
lean_dec(v_val_516_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_524_;
}
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_a_515_);
lean_dec_ref(v_repo_286_);
v___x_525_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_526_ = lean_string_append(v_name_285_, v___x_525_);
v___x_527_ = lean_string_append(v___x_526_, v___y_513_);
lean_dec_ref(v___y_513_);
v___x_528_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
v___x_530_ = lean_string_append(v___x_529_, v___y_514_);
lean_dec_ref(v___y_514_);
v___x_531_ = 3;
v___x_532_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_531_);
lean_inc_ref(v___y_511_);
v___x_533_ = lean_apply_2(v___y_511_, v___x_532_, lean_box(0));
v___x_534_ = lean_box(0);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
v___jp_536_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_541_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_285_);
v___x_542_ = lean_string_append(v_name_285_, v___x_541_);
v___x_543_ = lean_string_append(v___x_542_, v___y_538_);
v___x_544_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
v___x_546_ = lean_string_append(v___x_545_, v___y_539_);
v___x_547_ = 1;
v___x_548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*1, v___x_547_);
lean_inc_ref(v___y_540_);
v___x_549_ = lean_apply_2(v___y_540_, v___x_548_, lean_box(0));
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc_ref(v_repo_286_);
v___x_552_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_286_, v___y_537_, v___y_538_, v___x_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v_a_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
v_a_554_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_552_, 2);
v___x_555_ = lean_array_get_size(v_a_554_);
v___x_556_ = lean_nat_dec_lt(v___x_550_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_a_554_);
v___y_511_ = v___y_540_;
v___y_512_ = v___y_537_;
v___y_513_ = v___y_538_;
v___y_514_ = v___y_539_;
v_a_515_ = v_a_553_;
goto v___jp_510_;
}
else
{
lean_object* v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v___x_557_ = lean_box(0);
v___x_558_ = ((size_t)0ULL);
v___x_559_ = lean_usize_of_nat(v___x_555_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_554_, v___x_558_, v___x_559_, v___x_557_, v___y_540_);
lean_dec(v_a_554_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_dec_ref_known(v___x_560_, 1);
v___y_511_ = v___y_540_;
v___y_512_ = v___y_537_;
v___y_513_ = v___y_538_;
v___y_514_ = v___y_539_;
v_a_515_ = v_a_553_;
goto v___jp_510_;
}
else
{
lean_dec(v_a_553_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_560_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
lean_dec_ref(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_a_561_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_552_, 2);
v___x_562_ = lean_array_get_size(v_a_561_);
v___x_563_ = lean_nat_dec_lt(v___x_550_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_a_561_);
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_566_ = lean_box(0);
v___x_567_ = ((size_t)0ULL);
v___x_568_ = lean_usize_of_nat(v___x_562_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_561_, v___x_567_, v___x_568_, v___x_566_, v___y_540_);
lean_dec(v_a_561_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v___x_569_, 0);
lean_dec(v_unused_577_);
v___x_571_ = v___x_569_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_dec(v___x_569_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 1);
lean_ctor_set(v___x_571_, 0, v___x_566_);
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_566_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
return v___x_569_;
}
}
}
}
v___jp_578_:
{
if (lean_obj_tag(v___y_582_) == 0)
{
lean_dec_ref_known(v___y_582_, 1);
v___y_537_ = v___y_579_;
v___y_538_ = v___y_580_;
v___y_539_ = v___y_581_;
v___y_540_ = v_a_289_;
goto v___jp_536_;
}
else
{
lean_dec_ref(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_582_;
}
}
v___jp_583_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
lean_inc_ref(v___y_586_);
lean_inc_ref(v___y_584_);
v___x_589_ = l_Lake_GitRepo_addRemote(v___y_584_, v___y_586_, v_repo_286_, v___x_588_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 1);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 2);
v___x_591_ = lean_array_get_size(v_a_590_);
v___x_592_ = lean_nat_dec_lt(v___x_587_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_a_590_);
v___y_537_ = v___y_584_;
v___y_538_ = v___y_585_;
v___y_539_ = v___y_586_;
v___y_540_ = v_a_289_;
goto v___jp_536_;
}
else
{
lean_object* v___x_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___x_593_ = lean_box(0);
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_591_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_590_, v___x_594_, v___x_595_, v___x_593_, v_a_289_);
lean_dec(v_a_590_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_dec_ref_known(v___x_596_, 1);
v___y_537_ = v___y_584_;
v___y_538_ = v___y_585_;
v___y_539_ = v___y_586_;
v___y_540_ = v_a_289_;
goto v___jp_536_;
}
else
{
v___y_579_ = v___y_584_;
v___y_580_ = v___y_585_;
v___y_581_ = v___y_586_;
v___y_582_ = v___x_596_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_a_597_ = lean_ctor_get(v___x_589_, 1);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_589_, 2);
v___x_598_ = lean_array_get_size(v_a_597_);
v___x_599_ = lean_nat_dec_lt(v___x_587_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_a_597_);
lean_dec_ref(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_602_ = lean_box(0);
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_598_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_597_, v___x_603_, v___x_604_, v___x_602_, v_a_289_);
lean_dec(v_a_597_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_605_, 0);
lean_dec(v_unused_613_);
v___x_607_ = v___x_605_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_dec(v___x_605_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 1);
lean_ctor_set(v___x_607_, 0, v___x_602_);
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_602_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
v___y_579_ = v___y_584_;
v___y_580_ = v___y_585_;
v___y_581_ = v___y_586_;
v___y_582_ = v___x_605_;
goto v___jp_578_;
}
}
}
}
v___jp_614_:
{
if (lean_obj_tag(v___y_618_) == 0)
{
lean_dec_ref_known(v___y_618_, 1);
v___y_584_ = v___y_615_;
v___y_585_ = v___y_616_;
v___y_586_ = v___y_617_;
goto v___jp_583_;
}
else
{
lean_dec_ref(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_618_;
}
}
v___jp_619_:
{
if (v_a_621_ == 0)
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
goto v___jp_294_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_622_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_623_ = lean_string_append(v_name_285_, v___x_622_);
v___x_624_ = lean_string_append(v___x_623_, v_repo_286_);
lean_dec_ref(v_repo_286_);
v___x_625_ = 2;
v___x_626_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*1, v___x_625_);
lean_inc_ref(v___y_620_);
v___x_627_ = lean_apply_2(v___y_620_, v___x_626_, lean_box(0));
goto v___jp_294_;
}
}
v___jp_628_:
{
if (v_a_630_ == 0)
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
goto v___jp_291_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_631_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_632_ = lean_string_append(v_name_285_, v___x_631_);
v___x_633_ = lean_string_append(v___x_632_, v_repo_286_);
lean_dec_ref(v_repo_286_);
v___x_634_ = 2;
v___x_635_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_634_);
lean_inc_ref(v___y_629_);
v___x_636_ = lean_apply_2(v___y_629_, v___x_635_, lean_box(0));
goto v___jp_291_;
}
}
v___jp_637_:
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_array_get_size(v___y_638_);
v___x_643_ = lean_nat_dec_lt(v___y_640_, v___x_642_);
if (v___x_643_ == 0)
{
v___y_620_ = v___y_639_;
v_a_621_ = v_val_641_;
goto v___jp_619_;
}
else
{
lean_object* v___x_644_; size_t v___x_645_; size_t v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_box(0);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = lean_usize_of_nat(v___x_642_);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_638_, v___x_645_, v___x_646_, v___x_644_, v___y_639_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
v___y_620_ = v___y_639_;
v_a_621_ = v_val_641_;
goto v___jp_619_;
}
else
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
goto v___jp_294_;
}
else
{
return v___x_647_;
}
}
}
}
v___jp_648_:
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_654_ = l_Lake_GitRepo_hasNoDiff(v_repo_286_);
if (v___x_654_ == 0)
{
v___y_638_ = v___x_653_;
v___y_639_ = v___y_649_;
v___y_640_ = v___x_652_;
v_val_641_ = v___y_650_;
goto v___jp_637_;
}
else
{
v___y_638_ = v___x_653_;
v___y_639_ = v___y_649_;
v___y_640_ = v___x_652_;
v_val_641_ = v___y_651_;
goto v___jp_637_;
}
}
v___jp_655_:
{
if (lean_obj_tag(v___y_659_) == 0)
{
lean_dec_ref_known(v___y_659_, 1);
v___y_649_ = v___y_656_;
v___y_650_ = v___y_657_;
v___y_651_ = v___y_658_;
goto v___jp_648_;
}
else
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_659_;
}
}
v___jp_660_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_666_ = l_Lake_GitRepo_clean(v_repo_286_, v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 1);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 2);
v___x_668_ = lean_array_get_size(v_a_667_);
v___x_669_ = lean_nat_dec_lt(v___x_664_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v_a_667_);
v___y_649_ = v___y_661_;
v___y_650_ = v___y_662_;
v___y_651_ = v___y_663_;
goto v___jp_648_;
}
else
{
lean_object* v___x_670_; size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_box(0);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_668_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_667_, v___x_671_, v___x_672_, v___x_670_, v___y_661_);
lean_dec(v_a_667_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_dec_ref_known(v___x_673_, 1);
v___y_649_ = v___y_661_;
v___y_650_ = v___y_662_;
v___y_651_ = v___y_663_;
goto v___jp_648_;
}
else
{
v___y_656_ = v___y_661_;
v___y_657_ = v___y_662_;
v___y_658_ = v___y_663_;
v___y_659_ = v___x_673_;
goto v___jp_655_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_a_674_ = lean_ctor_get(v___x_666_, 1);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_666_, 2);
v___x_675_ = lean_array_get_size(v_a_674_);
v___x_676_ = lean_nat_dec_lt(v___x_664_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_a_674_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_box(0);
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_675_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_674_, v___x_680_, v___x_681_, v___x_679_, v___y_661_);
lean_dec(v_a_674_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_682_, 0);
lean_dec(v_unused_690_);
v___x_684_ = v___x_682_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_dec(v___x_682_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 1);
lean_ctor_set(v___x_684_, 0, v___x_679_);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_679_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
v___y_656_ = v___y_661_;
v___y_657_ = v___y_662_;
v___y_658_ = v___y_663_;
v___y_659_ = v___x_682_;
goto v___jp_655_;
}
}
}
}
v___jp_691_:
{
if (lean_obj_tag(v___y_695_) == 0)
{
lean_dec_ref_known(v___y_695_, 1);
v___y_661_ = v___y_692_;
v___y_662_ = v___y_693_;
v___y_663_ = v___y_694_;
goto v___jp_660_;
}
else
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_695_;
}
}
v___jp_696_:
{
if (lean_obj_tag(v_a_703_) == 0)
{
v___y_537_ = v___y_697_;
v___y_538_ = v___y_699_;
v___y_539_ = v___y_702_;
v___y_540_ = v___y_698_;
goto v___jp_536_;
}
else
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_744_; 
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_703_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_a_703_, 0);
lean_dec(v_unused_745_);
v___x_705_ = v_a_703_;
v_isShared_706_ = v_isSharedCheck_744_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_a_703_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_744_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
if (v___y_700_ == 0)
{
lean_del_object(v___x_705_);
v___y_537_ = v___y_697_;
v___y_538_ = v___y_699_;
v___y_539_ = v___y_702_;
v___y_540_ = v___y_698_;
goto v___jp_536_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v___y_702_);
v___x_707_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_285_);
v___x_708_ = lean_string_append(v_name_285_, v___x_707_);
v___x_709_ = lean_string_append(v___x_708_, v___y_699_);
v___x_710_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_711_ = lean_string_append(v___x_709_, v___x_710_);
v___x_712_ = 1;
v___x_713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set_uint8(v___x_713_, sizeof(void*)*1, v___x_712_);
lean_inc_ref(v___y_698_);
v___x_714_ = lean_apply_2(v___y_698_, v___x_713_, lean_box(0));
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_717_ = l_Lake_GitRepo_checkoutDetach(v___y_699_, v_repo_286_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
lean_del_object(v___x_705_);
v_a_718_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 2);
v___x_719_ = lean_array_get_size(v_a_718_);
v___x_720_ = lean_nat_dec_lt(v___x_715_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec(v_a_718_);
v___y_661_ = v___y_698_;
v___y_662_ = v___y_700_;
v___y_663_ = v___y_701_;
goto v___jp_660_;
}
else
{
lean_object* v___x_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v___x_721_ = lean_box(0);
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_719_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_718_, v___x_722_, v___x_723_, v___x_721_, v___y_698_);
lean_dec(v_a_718_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_dec_ref_known(v___x_724_, 1);
v___y_661_ = v___y_698_;
v___y_662_ = v___y_700_;
v___y_663_ = v___y_701_;
goto v___jp_660_;
}
else
{
v___y_692_ = v___y_698_;
v___y_693_ = v___y_700_;
v___y_694_ = v___y_701_;
v___y_695_ = v___x_724_;
goto v___jp_691_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_a_725_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_717_, 2);
v___x_726_ = lean_array_get_size(v_a_725_);
v___x_727_ = lean_nat_dec_lt(v___x_715_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_dec(v_a_725_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_728_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_728_);
v___x_730_ = v___x_705_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v___x_732_; size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; 
lean_del_object(v___x_705_);
v___x_732_ = lean_box(0);
v___x_733_ = ((size_t)0ULL);
v___x_734_ = lean_usize_of_nat(v___x_726_);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_725_, v___x_733_, v___x_734_, v___x_732_, v___y_698_);
lean_dec(v_a_725_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_735_, 0);
lean_dec(v_unused_743_);
v___x_737_ = v___x_735_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_dec(v___x_735_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 1);
lean_ctor_set(v___x_737_, 0, v___x_732_);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_732_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
v___y_692_ = v___y_698_;
v___y_693_ = v___y_700_;
v___y_694_ = v___y_701_;
v___y_695_ = v___x_735_;
goto v___jp_691_;
}
}
}
}
}
}
}
v___jp_746_:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v___y_749_);
v___x_752_ = lean_nat_dec_lt(v___y_747_, v___x_751_);
if (v___x_752_ == 0)
{
v___y_629_ = v___y_748_;
v_a_630_ = v_val_750_;
goto v___jp_628_;
}
else
{
lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_box(0);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_of_nat(v___x_751_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_749_, v___x_754_, v___x_755_, v___x_753_, v___y_748_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_dec_ref_known(v___x_756_, 1);
v___y_629_ = v___y_748_;
v_a_630_ = v_val_750_;
goto v___jp_628_;
}
else
{
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_dec_ref_known(v___x_756_, 1);
goto v___jp_291_;
}
else
{
return v___x_756_;
}
}
}
}
v___jp_757_:
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_763_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_760_);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v___y_760_);
v___x_765_ = l_Option_instDecidableEq___redArg(v___x_763_, v_a_762_, v___x_764_);
if (v___x_765_ == 0)
{
uint8_t v___x_766_; 
v___x_766_ = l_Lake_GitRev_isFullSha1(v___y_760_);
if (v___x_766_ == 0)
{
v___y_537_ = v___y_758_;
v___y_538_ = v___y_760_;
v___y_539_ = v___y_761_;
v___y_540_ = v___y_759_;
goto v___jp_536_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
lean_inc_ref(v___y_760_);
v___x_768_ = l_Lake_GitRepo_findCommit_x3f(v___y_760_, v_repo_286_);
v___x_769_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_769_ == 0)
{
v___y_697_ = v___y_758_;
v___y_698_ = v___y_759_;
v___y_699_ = v___y_760_;
v___y_700_ = v___x_766_;
v___y_701_ = v___x_765_;
v___y_702_ = v___y_761_;
v_a_703_ = v___x_768_;
goto v___jp_696_;
}
else
{
lean_object* v___x_770_; size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_770_ = lean_box(0);
v___x_771_ = ((size_t)0ULL);
v___x_772_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_767_, v___x_771_, v___x_772_, v___x_770_, v___y_759_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_dec_ref_known(v___x_773_, 1);
v___y_697_ = v___y_758_;
v___y_698_ = v___y_759_;
v___y_699_ = v___y_760_;
v___y_700_ = v___x_766_;
v___y_701_ = v___x_765_;
v___y_702_ = v___y_761_;
v_a_703_ = v___x_768_;
goto v___jp_696_;
}
else
{
lean_dec(v___x_768_);
lean_dec_ref(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_773_;
}
}
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
lean_dec_ref(v___y_761_);
lean_dec_ref(v___y_760_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_776_ = l_Lake_GitRepo_hasNoDiff(v_repo_286_);
if (v___x_776_ == 0)
{
v___y_747_ = v___x_774_;
v___y_748_ = v___y_759_;
v___y_749_ = v___x_775_;
v_val_750_ = v___x_765_;
goto v___jp_746_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = 0;
v___y_747_ = v___x_774_;
v___y_748_ = v___y_759_;
v___y_749_ = v___x_775_;
v_val_750_ = v___x_777_;
goto v___jp_746_;
}
}
}
v___jp_778_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_783_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_784_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_286_);
v___x_785_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_784_, v_repo_286_);
v___x_786_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_786_ == 0)
{
v___y_758_ = v___y_779_;
v___y_759_ = v___y_782_;
v___y_760_ = v___y_780_;
v___y_761_ = v___y_781_;
v_a_762_ = v___x_785_;
goto v___jp_757_;
}
else
{
lean_object* v___x_787_; size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_787_ = lean_box(0);
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_783_, v___x_788_, v___x_789_, v___x_787_, v___y_782_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_dec_ref_known(v___x_790_, 1);
v___y_758_ = v___y_779_;
v___y_759_ = v___y_782_;
v___y_760_ = v___y_780_;
v___y_761_ = v___y_781_;
v_a_762_ = v___x_785_;
goto v___jp_757_;
}
else
{
lean_dec(v___x_785_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_790_;
}
}
}
v___jp_791_:
{
if (lean_obj_tag(v___y_795_) == 0)
{
lean_dec_ref_known(v___y_795_, 1);
v___y_779_ = v___y_792_;
v___y_780_ = v___y_793_;
v___y_781_ = v___y_794_;
v___y_782_ = v_a_289_;
goto v___jp_778_;
}
else
{
lean_dec_ref(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_795_;
}
}
v___jp_796_:
{
if (lean_obj_tag(v___y_800_) == 0)
{
lean_dec_ref_known(v___y_800_, 1);
v___y_779_ = v___y_797_;
v___y_780_ = v___y_798_;
v___y_781_ = v___y_799_;
v___y_782_ = v_a_289_;
goto v___jp_778_;
}
else
{
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___y_800_;
}
}
v___jp_801_:
{
if (lean_obj_tag(v_a_805_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_849_; 
v_val_806_ = lean_ctor_get(v_a_805_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_849_ == 0)
{
v___x_808_ = v_a_805_;
v_isShared_809_ = v_isSharedCheck_849_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_val_806_);
lean_dec(v_a_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_849_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
uint8_t v___x_810_; 
v___x_810_ = lean_string_dec_eq(v_val_806_, v___y_804_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_811_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_285_);
v___x_812_ = lean_string_append(v_name_285_, v___x_811_);
v___x_813_ = lean_string_append(v___x_812_, v_val_806_);
lean_dec(v_val_806_);
v___x_814_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_815_ = lean_string_append(v___x_813_, v___x_814_);
v___x_816_ = lean_string_append(v___x_815_, v___y_804_);
v___x_817_ = 1;
v___x_818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_817_);
lean_inc_ref(v_a_289_);
v___x_819_ = lean_apply_2(v_a_289_, v___x_818_, lean_box(0));
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
lean_inc_ref(v___y_804_);
lean_inc_ref(v___y_802_);
v___x_822_ = l_Lake_GitRepo_setRemoteUrl(v___y_802_, v___y_804_, v_repo_286_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
lean_del_object(v___x_808_);
v_a_823_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 2);
v___x_824_ = lean_array_get_size(v_a_823_);
v___x_825_ = lean_nat_dec_lt(v___x_820_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec(v_a_823_);
v___y_779_ = v___y_802_;
v___y_780_ = v___y_803_;
v___y_781_ = v___y_804_;
v___y_782_ = v_a_289_;
goto v___jp_778_;
}
else
{
lean_object* v___x_826_; size_t v___x_827_; size_t v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_box(0);
v___x_827_ = ((size_t)0ULL);
v___x_828_ = lean_usize_of_nat(v___x_824_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_823_, v___x_827_, v___x_828_, v___x_826_, v_a_289_);
lean_dec(v_a_823_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec_ref_known(v___x_829_, 1);
v___y_779_ = v___y_802_;
v___y_780_ = v___y_803_;
v___y_781_ = v___y_804_;
v___y_782_ = v_a_289_;
goto v___jp_778_;
}
else
{
v___y_797_ = v___y_802_;
v___y_798_ = v___y_803_;
v___y_799_ = v___y_804_;
v___y_800_ = v___x_829_;
goto v___jp_796_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_a_830_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_822_, 2);
v___x_831_ = lean_array_get_size(v_a_830_);
v___x_832_ = lean_nat_dec_lt(v___x_820_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_a_830_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_833_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_833_);
v___x_835_ = v___x_808_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
lean_del_object(v___x_808_);
v___x_837_ = lean_box(0);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = lean_usize_of_nat(v___x_831_);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_830_, v___x_838_, v___x_839_, v___x_837_, v_a_289_);
lean_dec(v_a_830_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v___x_840_, 0);
lean_dec(v_unused_848_);
v___x_842_ = v___x_840_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_dec(v___x_840_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 1);
lean_ctor_set(v___x_842_, 0, v___x_837_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_837_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
v___y_797_ = v___y_802_;
v___y_798_ = v___y_803_;
v___y_799_ = v___y_804_;
v___y_800_ = v___x_840_;
goto v___jp_796_;
}
}
}
}
else
{
lean_del_object(v___x_808_);
lean_dec(v_val_806_);
v___y_779_ = v___y_802_;
v___y_780_ = v___y_803_;
v___y_781_ = v___y_804_;
v___y_782_ = v_a_289_;
goto v___jp_778_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_a_805_);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
lean_inc_ref(v___y_804_);
lean_inc_ref(v___y_802_);
v___x_852_ = l_Lake_GitRepo_addRemote(v___y_802_, v___y_804_, v_repo_286_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_a_853_ = lean_ctor_get(v___x_852_, 1);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 2);
v___x_854_ = lean_array_get_size(v_a_853_);
v___x_855_ = lean_nat_dec_lt(v___x_850_, v___x_854_);
if (v___x_855_ == 0)
{
lean_dec(v_a_853_);
v___y_779_ = v___y_802_;
v___y_780_ = v___y_803_;
v___y_781_ = v___y_804_;
v___y_782_ = v_a_289_;
goto v___jp_778_;
}
else
{
lean_object* v___x_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_854_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_853_, v___x_857_, v___x_858_, v___x_856_, v_a_289_);
lean_dec(v_a_853_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_dec_ref_known(v___x_859_, 1);
v___y_779_ = v___y_802_;
v___y_780_ = v___y_803_;
v___y_781_ = v___y_804_;
v___y_782_ = v_a_289_;
goto v___jp_778_;
}
else
{
v___y_792_ = v___y_802_;
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___x_859_;
goto v___jp_791_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_a_860_ = lean_ctor_get(v___x_852_, 1);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_852_, 2);
v___x_861_ = lean_array_get_size(v_a_860_);
v___x_862_ = lean_nat_dec_lt(v___x_850_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_a_860_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
else
{
lean_object* v___x_865_; size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
v___x_865_ = lean_box(0);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = lean_usize_of_nat(v___x_861_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_860_, v___x_866_, v___x_867_, v___x_865_, v_a_289_);
lean_dec(v_a_860_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v___x_868_, 0);
lean_dec(v_unused_876_);
v___x_870_ = v___x_868_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_dec(v___x_868_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 1);
lean_ctor_set(v___x_870_, 0, v___x_865_);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_865_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
v___y_792_ = v___y_802_;
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___x_868_;
goto v___jp_791_;
}
}
}
}
}
v___jp_877_:
{
if (v_a_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_882_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_285_);
v___x_883_ = lean_string_append(v_name_285_, v___x_882_);
v___x_884_ = 1;
v___x_885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1, v___x_884_);
lean_inc_ref(v_a_289_);
v___x_886_ = lean_apply_2(v_a_289_, v___x_885_, lean_box(0));
lean_inc_ref(v_repo_286_);
v___x_887_ = l_IO_FS_createDirAll(v_repo_286_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_920_; 
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_887_, 0);
lean_dec(v_unused_921_);
v___x_889_ = v___x_887_;
v_isShared_890_ = v_isSharedCheck_920_;
goto v_resetjp_888_;
}
else
{
lean_dec(v___x_887_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_920_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
v___x_893_ = l_Lake_GitRepo_quietInit(v_repo_286_, v___x_892_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
lean_del_object(v___x_889_);
v_a_894_ = lean_ctor_get(v___x_893_, 1);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 2);
v___x_895_ = lean_array_get_size(v_a_894_);
v___x_896_ = lean_nat_dec_lt(v___x_891_, v___x_895_);
if (v___x_896_ == 0)
{
lean_dec(v_a_894_);
v___y_584_ = v___y_878_;
v___y_585_ = v___y_879_;
v___y_586_ = v___y_880_;
goto v___jp_583_;
}
else
{
lean_object* v___x_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; 
v___x_897_ = lean_box(0);
v___x_898_ = ((size_t)0ULL);
v___x_899_ = lean_usize_of_nat(v___x_895_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_894_, v___x_898_, v___x_899_, v___x_897_, v_a_289_);
lean_dec(v_a_894_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_dec_ref_known(v___x_900_, 1);
v___y_584_ = v___y_878_;
v___y_585_ = v___y_879_;
v___y_586_ = v___y_880_;
goto v___jp_583_;
}
else
{
v___y_615_ = v___y_878_;
v___y_616_ = v___y_879_;
v___y_617_ = v___y_880_;
v___y_618_ = v___x_900_;
goto v___jp_614_;
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_a_901_ = lean_ctor_get(v___x_893_, 1);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_893_, 2);
v___x_902_ = lean_array_get_size(v_a_901_);
v___x_903_ = lean_nat_dec_lt(v___x_891_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_906_; 
lean_dec(v_a_901_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v___x_904_ = lean_box(0);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 1);
lean_ctor_set(v___x_889_, 0, v___x_904_);
v___x_906_ = v___x_889_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_object* v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
lean_del_object(v___x_889_);
v___x_908_ = lean_box(0);
v___x_909_ = ((size_t)0ULL);
v___x_910_ = lean_usize_of_nat(v___x_902_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_901_, v___x_909_, v___x_910_, v___x_908_, v_a_289_);
lean_dec(v_a_901_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_919_);
v___x_913_ = v___x_911_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_911_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 1);
lean_ctor_set(v___x_913_, 0, v___x_908_);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_908_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
v___y_615_ = v___y_878_;
v___y_616_ = v___y_879_;
v___y_617_ = v___y_880_;
v___y_618_ = v___x_911_;
goto v___jp_614_;
}
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
v_a_922_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_934_ == 0)
{
v___x_924_ = v___x_887_;
v_isShared_925_ = v_isSharedCheck_934_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_887_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_934_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_926_ = lean_io_error_to_string(v_a_922_);
v___x_927_ = 3;
v___x_928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_927_);
lean_inc_ref(v_a_289_);
v___x_929_ = lean_apply_2(v_a_289_, v___x_928_, lean_box(0));
v___x_930_ = lean_box(0);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_930_);
v___x_932_ = v___x_924_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_286_);
lean_inc_ref(v___y_878_);
v___x_936_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_878_, v_repo_286_);
v___x_937_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_937_ == 0)
{
v___y_802_ = v___y_878_;
v___y_803_ = v___y_879_;
v___y_804_ = v___y_880_;
v_a_805_ = v___x_936_;
goto v___jp_801_;
}
else
{
lean_object* v___x_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; 
v___x_938_ = lean_box(0);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_935_, v___x_939_, v___x_940_, v___x_938_, v_a_289_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_dec_ref_known(v___x_941_, 1);
v___y_802_ = v___y_878_;
v___y_803_ = v___y_879_;
v___y_804_ = v___y_880_;
v_a_805_ = v___x_936_;
goto v___jp_801_;
}
else
{
lean_dec(v___x_936_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_941_;
}
}
}
}
v___jp_942_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; 
v___x_946_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_947_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_286_);
v___x_948_ = l_System_FilePath_join(v_repo_286_, v___x_947_);
v___x_949_ = l_System_FilePath_pathExists(v___x_948_);
lean_dec_ref(v___x_948_);
v___x_950_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_950_ == 0)
{
v___y_878_ = v___y_943_;
v___y_879_ = v___y_944_;
v___y_880_ = v_a_945_;
v_a_881_ = v___x_949_;
goto v___jp_877_;
}
else
{
lean_object* v___x_951_; size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v___x_951_ = lean_box(0);
v___x_952_ = ((size_t)0ULL);
v___x_953_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_946_, v___x_952_, v___x_953_, v___x_951_, v_a_289_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_dec_ref_known(v___x_954_, 1);
v___y_878_ = v___y_943_;
v___y_879_ = v___y_944_;
v___y_880_ = v_a_945_;
v_a_881_ = v___x_949_;
goto v___jp_877_;
}
else
{
lean_dec_ref(v_a_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_954_;
}
}
}
v___jp_955_:
{
if (lean_obj_tag(v_a_958_) == 1)
{
lean_object* v_val_959_; 
lean_dec_ref(v_url_287_);
v_val_959_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_val_959_);
lean_dec_ref_known(v_a_958_, 1);
v___y_943_ = v___y_956_;
v___y_944_ = v___y_957_;
v_a_945_ = v_val_959_;
goto v___jp_942_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v_a_958_);
lean_dec_ref(v___y_957_);
lean_dec_ref(v_repo_286_);
v___x_960_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_961_ = lean_string_append(v_name_285_, v___x_960_);
v___x_962_ = lean_string_append(v___x_961_, v_url_287_);
lean_dec_ref(v_url_287_);
v___x_963_ = 3;
v___x_964_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*1, v___x_963_);
lean_inc_ref(v_a_289_);
v___x_965_ = lean_apply_2(v_a_289_, v___x_964_, lean_box(0));
v___x_966_ = lean_box(0);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
v___jp_968_:
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = lean_array_get_size(v___y_970_);
v___x_975_ = lean_nat_dec_lt(v___y_972_, v___x_974_);
if (v___x_975_ == 0)
{
v___y_956_ = v___y_969_;
v___y_957_ = v___y_971_;
v_a_958_ = v_val_973_;
goto v___jp_955_;
}
else
{
lean_object* v___x_976_; size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
v___x_976_ = lean_box(0);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_974_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_970_, v___x_977_, v___x_978_, v___x_976_, v_a_289_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec_ref_known(v___x_979_, 1);
v___y_956_ = v___y_969_;
v___y_957_ = v___y_971_;
v_a_958_ = v_val_973_;
goto v___jp_955_;
}
else
{
lean_dec(v_val_973_);
lean_dec_ref(v___y_971_);
lean_dec_ref(v_url_287_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_979_;
}
}
}
v___jp_980_:
{
if (v_a_983_ == 0)
{
v___y_943_ = v___y_981_;
v___y_944_ = v___y_982_;
v_a_945_ = v_url_287_;
goto v___jp_942_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_287_);
v___x_986_ = l_Lake_resolvePath(v_url_287_);
v___x_987_ = lean_string_utf8_byte_size(v___x_986_);
v___x_988_ = lean_nat_dec_eq(v___x_987_, v___x_984_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_986_);
v___y_969_ = v___y_981_;
v___y_970_ = v___x_985_;
v___y_971_ = v___y_982_;
v___y_972_ = v___x_984_;
v_val_973_ = v___x_989_;
goto v___jp_968_;
}
else
{
lean_object* v___x_990_; 
lean_dec_ref(v___x_986_);
v___x_990_ = lean_box(0);
v___y_969_ = v___y_981_;
v___y_970_ = v___x_985_;
v___y_971_ = v___y_982_;
v___y_972_ = v___x_984_;
v_val_973_ = v___x_990_;
goto v___jp_968_;
}
}
}
v___jp_991_:
{
lean_object* v_remote_993_; lean_object* v___x_994_; uint8_t v___x_995_; uint8_t v___x_996_; 
v_remote_993_ = l_Lake_Git_defaultRemote;
v___x_994_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_995_ = l_System_FilePath_pathExists(v_url_287_);
v___x_996_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_996_ == 0)
{
v___y_981_ = v_remote_993_;
v___y_982_ = v___y_992_;
v_a_983_ = v___x_995_;
goto v___jp_980_;
}
else
{
lean_object* v___x_997_; size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v___x_997_ = lean_box(0);
v___x_998_ = ((size_t)0ULL);
v___x_999_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_994_, v___x_998_, v___x_999_, v___x_997_, v_a_289_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_dec_ref_known(v___x_1000_, 1);
v___y_981_ = v_remote_993_;
v___y_982_ = v___y_992_;
v_a_983_ = v___x_995_;
goto v___jp_980_;
}
else
{
lean_dec_ref(v___y_992_);
lean_dec_ref(v_url_287_);
lean_dec_ref(v_repo_286_);
lean_dec_ref(v_name_285_);
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* v_name_1003_, lean_object* v_repo_1004_, lean_object* v_url_1005_, lean_object* v_rev_x3f_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(v_name_1003_, v_repo_1004_, v_url_1005_, v_rev_x3f_1006_, v_a_1007_);
lean_dec_ref(v_a_1007_);
return v_res_1009_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__4(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1016_ = l_Lake_instInhabitedPackageEntry_default;
v___x_1017_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__3));
v___x_1018_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___x_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_ctor_set(v___x_1019_, 2, v___x_1018_);
lean_ctor_set(v___x_1019_, 3, v___x_1017_);
lean_ctor_set(v___x_1019_, 4, v___x_1016_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default(void){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_obj_once(&l_Lake_instInhabitedMaterializedDep_default___closed__4, &l_Lake_instInhabitedMaterializedDep_default___closed__4_once, _init_l_Lake_instInhabitedMaterializedDep_default___closed__4);
return v___x_1020_;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep(void){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lake_instInhabitedMaterializedDep_default;
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* v_self_1022_){
_start:
{
lean_object* v_manifestEntry_1023_; lean_object* v_name_1024_; 
v_manifestEntry_1023_ = lean_ctor_get(v_self_1022_, 4);
v_name_1024_ = lean_ctor_get(v_manifestEntry_1023_, 0);
lean_inc(v_name_1024_);
return v_name_1024_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* v_self_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lake_MaterializedDep_name(v_self_1025_);
lean_dec_ref(v_self_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_prettyName(lean_object* v_self_1027_){
_start:
{
lean_object* v_manifestEntry_1028_; lean_object* v_name_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; 
v_manifestEntry_1028_ = lean_ctor_get(v_self_1027_, 4);
lean_inc_ref(v_manifestEntry_1028_);
lean_dec_ref(v_self_1027_);
v_name_1029_ = lean_ctor_get(v_manifestEntry_1028_, 0);
lean_inc(v_name_1029_);
lean_dec_ref(v_manifestEntry_1028_);
v___x_1030_ = 0;
v___x_1031_ = l_Lean_Name_toString(v_name_1029_, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* v_self_1032_){
_start:
{
lean_object* v_manifestEntry_1033_; lean_object* v_scope_1034_; 
v_manifestEntry_1033_ = lean_ctor_get(v_self_1032_, 4);
v_scope_1034_ = lean_ctor_get(v_manifestEntry_1033_, 1);
lean_inc_ref(v_scope_1034_);
return v_scope_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* v_self_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lake_MaterializedDep_scope(v_self_1035_);
lean_dec_ref(v_self_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f(lean_object* v_self_1037_){
_start:
{
lean_object* v_manifestEntry_1038_; lean_object* v_manifestFile_x3f_1039_; 
v_manifestEntry_1038_ = lean_ctor_get(v_self_1037_, 4);
v_manifestFile_x3f_1039_ = lean_ctor_get(v_manifestEntry_1038_, 3);
lean_inc(v_manifestFile_x3f_1039_);
return v_manifestFile_x3f_1039_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile_x3f___boxed(lean_object* v_self_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_1040_);
lean_dec_ref(v_self_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile(lean_object* v_self_1042_){
_start:
{
lean_object* v_manifestEntry_1043_; lean_object* v_manifestFile_x3f_1044_; 
v_manifestEntry_1043_ = lean_ctor_get(v_self_1042_, 4);
v_manifestFile_x3f_1044_ = lean_ctor_get(v_manifestEntry_1043_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1044_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lake_defaultManifestFile;
return v___x_1045_;
}
else
{
lean_object* v_val_1046_; 
v_val_1046_ = lean_ctor_get(v_manifestFile_x3f_1044_, 0);
lean_inc(v_val_1046_);
return v_val_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relManifestFile___boxed(lean_object* v_self_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lake_MaterializedDep_relManifestFile(v_self_1047_);
lean_dec_ref(v_self_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile(lean_object* v_self_1049_){
_start:
{
lean_object* v_manifestEntry_1050_; lean_object* v_manifestFile_x3f_1051_; 
v_manifestEntry_1050_ = lean_ctor_get(v_self_1049_, 4);
v_manifestFile_x3f_1051_ = lean_ctor_get(v_manifestEntry_1050_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1051_) == 0)
{
lean_object* v_pkgDir_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_pkgDir_1052_ = lean_ctor_get(v_self_1049_, 0);
lean_inc_ref(v_pkgDir_1052_);
lean_dec_ref(v_self_1049_);
v___x_1053_ = l_Lake_defaultManifestFile;
v___x_1054_ = l_Lake_joinRelative(v_pkgDir_1052_, v___x_1053_);
return v___x_1054_;
}
else
{
lean_object* v_pkgDir_1055_; lean_object* v_val_1056_; lean_object* v___x_1057_; 
lean_inc_ref(v_manifestFile_x3f_1051_);
v_pkgDir_1055_ = lean_ctor_get(v_self_1049_, 0);
lean_inc_ref(v_pkgDir_1055_);
lean_dec_ref(v_self_1049_);
v_val_1056_ = lean_ctor_get(v_manifestFile_x3f_1051_, 0);
lean_inc(v_val_1056_);
lean_dec_ref_known(v_manifestFile_x3f_1051_, 1);
v___x_1057_ = l_Lake_joinRelative(v_pkgDir_1055_, v_val_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile(lean_object* v_self_1058_){
_start:
{
lean_object* v_manifestEntry_1059_; lean_object* v_configFile_1060_; 
v_manifestEntry_1059_ = lean_ctor_get(v_self_1058_, 4);
v_configFile_1060_ = lean_ctor_get(v_manifestEntry_1059_, 2);
lean_inc_ref(v_configFile_1060_);
return v_configFile_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_relConfigFile___boxed(lean_object* v_self_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lake_MaterializedDep_relConfigFile(v_self_1061_);
lean_dec_ref(v_self_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* v_self_1063_){
_start:
{
lean_object* v_manifestEntry_1064_; lean_object* v_pkgDir_1065_; lean_object* v_configFile_1066_; lean_object* v___x_1067_; 
v_manifestEntry_1064_ = lean_ctor_get(v_self_1063_, 4);
lean_inc_ref(v_manifestEntry_1064_);
v_pkgDir_1065_ = lean_ctor_get(v_self_1063_, 0);
lean_inc_ref(v_pkgDir_1065_);
lean_dec_ref(v_self_1063_);
v_configFile_1066_ = lean_ctor_get(v_manifestEntry_1064_, 2);
lean_inc_ref(v_configFile_1066_);
lean_dec_ref(v_manifestEntry_1064_);
v___x_1067_ = l_Lake_joinRelative(v_pkgDir_1065_, v_configFile_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object* v_self_1068_){
_start:
{
lean_object* v_manifest_x3f_1069_; 
v_manifest_x3f_1069_ = lean_ctor_get(v_self_1068_, 3);
if (lean_obj_tag(v_manifest_x3f_1069_) == 1)
{
lean_object* v_a_1070_; uint8_t v_fixedToolchain_1071_; 
v_a_1070_ = lean_ctor_get(v_manifest_x3f_1069_, 0);
v_fixedToolchain_1071_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*4);
return v_fixedToolchain_1071_;
}
else
{
uint8_t v___x_1072_; 
v___x_1072_ = 0;
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_fixedToolchain___boxed(lean_object* v_self_1073_){
_start:
{
uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_res_1074_ = l_Lake_MaterializedDep_fixedToolchain(v_self_1073_);
lean_dec_ref(v_self_1073_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object* v_dep_1084_){
_start:
{
lean_object* v_name_1085_; lean_object* v_scope_1086_; lean_object* v_version_1087_; lean_object* v_fst_1089_; lean_object* v_snd_1090_; 
v_name_1085_ = lean_ctor_get(v_dep_1084_, 0);
lean_inc(v_name_1085_);
v_scope_1086_ = lean_ctor_get(v_dep_1084_, 1);
lean_inc_ref(v_scope_1086_);
v_version_1087_ = lean_ctor_get(v_dep_1084_, 2);
lean_inc(v_version_1087_);
lean_dec_ref(v_dep_1084_);
switch(lean_obj_tag(v_version_1087_))
{
case 0:
{
lean_object* v___x_1113_; 
v___x_1113_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v_fst_1089_ = v___x_1113_;
v_snd_1090_ = v___x_1113_;
goto v___jp_1088_;
}
case 1:
{
lean_object* v_rev_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1129_; 
v_rev_1114_ = lean_ctor_get(v_version_1087_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_version_1087_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1116_ = v_version_1087_;
v_isShared_1117_ = v_isSharedCheck_1129_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_rev_1114_);
lean_dec(v_version_1087_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1129_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1118_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1119_ = l_String_quote(v_rev_1114_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 3);
lean_ctor_set(v___x_1116_, 0, v___x_1119_);
v___x_1121_ = v___x_1116_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1122_ = l_Std_Format_defWidth;
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = l_Std_Format_pretty(v___x_1121_, v___x_1122_, v___x_1123_, v___x_1123_);
v___x_1125_ = lean_string_append(v___x_1118_, v___x_1124_);
v___x_1126_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6));
v___x_1127_ = lean_string_append(v___x_1126_, v___x_1124_);
lean_dec_ref(v___x_1124_);
v_fst_1089_ = v___x_1125_;
v_snd_1090_ = v___x_1127_;
goto v___jp_1088_;
}
}
}
default: 
{
lean_object* v_ver_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1146_; 
v_ver_1130_ = lean_ctor_get(v_version_1087_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_version_1087_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1132_ = v_version_1087_;
v_isShared_1133_ = v_isSharedCheck_1146_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_ver_1130_);
lean_dec(v_version_1087_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1146_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_toString_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v_toString_1134_ = lean_ctor_get(v_ver_1130_, 0);
lean_inc_ref(v_toString_1134_);
lean_dec_ref(v_ver_1130_);
v___x_1135_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5));
v___x_1136_ = l_String_quote(v_toString_1134_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 3);
lean_ctor_set(v___x_1132_, 0, v___x_1136_);
v___x_1138_ = v___x_1132_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = l_Std_Format_defWidth;
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = l_Std_Format_pretty(v___x_1138_, v___x_1139_, v___x_1140_, v___x_1140_);
v___x_1142_ = lean_string_append(v___x_1135_, v___x_1141_);
v___x_1143_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7));
v___x_1144_ = lean_string_append(v___x_1143_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v_fst_1089_ = v___x_1142_;
v_snd_1090_ = v___x_1144_;
goto v___jp_1088_;
}
}
}
}
v___jp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1091_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_1086_);
v___x_1092_ = lean_string_append(v_scope_1086_, v___x_1091_);
v___x_1093_ = 0;
v___x_1094_ = l_Lean_Name_toString(v_name_1085_, v___x_1093_);
v___x_1095_ = lean_string_append(v___x_1092_, v___x_1094_);
v___x_1096_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1));
v___x_1097_ = lean_string_append(v___x_1095_, v___x_1096_);
v___x_1098_ = lean_string_append(v___x_1097_, v_scope_1086_);
v___x_1099_ = lean_string_append(v___x_1098_, v___x_1091_);
v___x_1100_ = lean_string_append(v___x_1099_, v___x_1094_);
v___x_1101_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2));
v___x_1102_ = lean_string_append(v___x_1100_, v___x_1101_);
v___x_1103_ = lean_string_append(v___x_1102_, v_fst_1089_);
lean_dec_ref(v_fst_1089_);
v___x_1104_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3));
v___x_1105_ = lean_string_append(v___x_1103_, v___x_1104_);
v___x_1106_ = lean_string_append(v___x_1105_, v_scope_1086_);
lean_dec_ref(v_scope_1086_);
v___x_1107_ = lean_string_append(v___x_1106_, v___x_1091_);
v___x_1108_ = lean_string_append(v___x_1107_, v___x_1094_);
lean_dec_ref(v___x_1094_);
v___x_1109_ = lean_string_append(v___x_1108_, v___x_1101_);
v___x_1110_ = lean_string_append(v___x_1109_, v_snd_1090_);
lean_dec_ref(v_snd_1090_);
v___x_1111_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4));
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath(lean_object* v_wsDir_1147_, lean_object* v_relPkgsDir_1148_, lean_object* v_relSrc_1149_, lean_object* v_dirName_1150_, uint8_t v_copy_1151_, uint8_t v_update_1152_){
_start:
{
if (v_copy_1151_ == 0)
{
lean_object* v___x_1154_; 
lean_dec_ref(v_dirName_1150_);
lean_dec_ref(v_relPkgsDir_1148_);
lean_dec_ref(v_wsDir_1147_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_relSrc_1149_);
return v___x_1154_;
}
else
{
lean_object* v_relDst_1155_; lean_object* v_dst_1156_; 
v_relDst_1155_ = l_Lake_joinRelative(v_relPkgsDir_1148_, v_dirName_1150_);
lean_inc_ref(v_relDst_1155_);
lean_inc_ref(v_wsDir_1147_);
v_dst_1156_ = l_Lake_joinRelative(v_wsDir_1147_, v_relDst_1155_);
if (v_update_1152_ == 0)
{
uint8_t v___x_1176_; 
v___x_1176_ = l_System_FilePath_pathExists(v_dst_1156_);
if (v___x_1176_ == 0)
{
goto v___jp_1157_;
}
else
{
lean_object* v___x_1177_; 
lean_dec_ref(v_dst_1156_);
lean_dec_ref(v_relSrc_1149_);
lean_dec_ref(v_wsDir_1147_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_relDst_1155_);
return v___x_1177_;
}
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lake_removeDirAllIfExists(v_dst_1156_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_dec_ref_known(v___x_1178_, 1);
goto v___jp_1157_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_dst_1156_);
lean_dec_ref(v_relDst_1155_);
lean_dec_ref(v_relSrc_1149_);
lean_dec_ref(v_wsDir_1147_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
v___jp_1157_:
{
lean_object* v_src_1158_; lean_object* v___x_1159_; 
v_src_1158_ = l_Lake_joinRelative(v_wsDir_1147_, v_relSrc_1149_);
v___x_1159_ = l_Lake_copyDirAll(v_src_1158_, v_dst_1156_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1167_);
v___x_1161_ = v___x_1159_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v___x_1159_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v_relDst_1155_);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_relDst_1155_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_relDst_1155_);
v_a_1168_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1159_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1159_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_mkPath___boxed(lean_object* v_wsDir_1187_, lean_object* v_relPkgsDir_1188_, lean_object* v_relSrc_1189_, lean_object* v_dirName_1190_, lean_object* v_copy_1191_, lean_object* v_update_1192_, lean_object* v_a_1193_){
_start:
{
uint8_t v_copy_boxed_1194_; uint8_t v_update_boxed_1195_; lean_object* v_res_1196_; 
v_copy_boxed_1194_ = lean_unbox(v_copy_1191_);
v_update_boxed_1195_ = lean_unbox(v_update_1192_);
v_res_1196_ = l___private_Lake_Load_Materialize_0__Lake_mkPath(v_wsDir_1187_, v_relPkgsDir_1188_, v_relSrc_1189_, v_dirName_1190_, v_copy_boxed_1194_, v_update_boxed_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1198_, uint8_t v_inherited_1199_, lean_object* v_wsDir_1200_, lean_object* v_name_1201_, lean_object* v_relPkgDir_1202_, lean_object* v_remoteUrl_1203_, lean_object* v_src_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___y_1208_; lean_object* v_a_1209_; lean_object* v___f_1226_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v_val_1232_; lean_object* v_pkgDir_1248_; lean_object* v_a_1250_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_val_1286_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___f_1226_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_1202_);
v_pkgDir_1248_ = l_Lake_joinRelative(v_wsDir_1200_, v_relPkgDir_1202_);
v___x_1282_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_1248_);
v___x_1301_ = l_Lake_resolvePath(v_pkgDir_1248_);
v___x_1302_ = lean_string_utf8_byte_size(v___x_1301_);
v___x_1303_ = lean_nat_dec_eq(v___x_1302_, v___x_1283_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1301_);
v_val_1286_ = v___x_1304_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1305_; 
lean_dec_ref(v___x_1301_);
v___x_1305_ = lean_box(0);
v_val_1286_ = v___x_1305_;
goto v___jp_1285_;
}
v___jp_1207_:
{
lean_object* v_name_1210_; lean_object* v_scope_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1222_; 
v_name_1210_ = lean_ctor_get(v_dep_1198_, 0);
v_scope_1211_ = lean_ctor_get(v_dep_1198_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_dep_1198_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; lean_object* v_unused_1224_; lean_object* v_unused_1225_; 
v_unused_1223_ = lean_ctor_get(v_dep_1198_, 4);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_dep_1198_, 3);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_dep_1198_, 2);
lean_dec(v_unused_1225_);
v___x_1213_ = v_dep_1198_;
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_scope_1211_);
lean_inc(v_name_1210_);
lean_dec(v_dep_1198_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1215_ = l_Lake_defaultConfigFile;
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1217_, 0, v_name_1210_);
lean_ctor_set(v___x_1217_, 1, v_scope_1211_);
lean_ctor_set(v___x_1217_, 2, v___x_1215_);
lean_ctor_set(v___x_1217_, 3, v___x_1216_);
lean_ctor_set(v___x_1217_, 4, v_src_1204_);
lean_ctor_set_uint8(v___x_1217_, sizeof(void*)*5, v_inherited_1199_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1217_);
lean_ctor_set(v___x_1213_, 3, v_a_1209_);
lean_ctor_set(v___x_1213_, 2, v_remoteUrl_1203_);
lean_ctor_set(v___x_1213_, 1, v_relPkgDir_1202_);
lean_ctor_set(v___x_1213_, 0, v___y_1208_);
v___x_1219_ = v___x_1213_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___y_1208_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_relPkgDir_1202_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_remoteUrl_1203_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_a_1209_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
v___jp_1227_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v___y_1230_);
v___x_1234_ = lean_nat_dec_lt(v___y_1229_, v___x_1233_);
if (v___x_1234_ == 0)
{
v___y_1208_ = v___y_1231_;
v_a_1209_ = v_val_1232_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1819__overap_1238_; lean_object* v___x_1239_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = ((size_t)0ULL);
v___x_1237_ = lean_usize_of_nat(v___x_1233_);
lean_inc_ref(v___y_1230_);
lean_inc_ref(v___y_1228_);
v___x_1819__overap_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1228_, v___f_1226_, v___y_1230_, v___x_1236_, v___x_1237_, v___x_1235_);
lean_inc_ref(v_a_1205_);
v___x_1239_ = lean_apply_2(v___x_1819__overap_1238_, v_a_1205_, lean_box(0));
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_dec_ref_known(v___x_1239_, 1);
v___y_1208_ = v___y_1231_;
v_a_1209_ = v_val_1232_;
goto v___jp_1207_;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_val_1232_);
lean_dec_ref(v___y_1231_);
lean_dec_ref(v_src_1204_);
lean_dec_ref(v_remoteUrl_1203_);
lean_dec_ref(v_relPkgDir_1202_);
lean_dec_ref(v_dep_1198_);
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
v___jp_1249_:
{
if (lean_obj_tag(v_a_1250_) == 1)
{
lean_object* v_val_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v_pkgDir_1248_);
lean_dec_ref(v_name_1201_);
v_val_1251_ = lean_ctor_get(v_a_1250_, 0);
lean_inc_n(v_val_1251_, 2);
lean_dec_ref_known(v_a_1250_, 1);
v___x_1252_ = l_Lake_defaultManifestFile;
v___x_1253_ = l_Lake_joinRelative(v_val_1251_, v___x_1252_);
v___x_1254_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1257_ = l_Lake_Manifest_load(v___x_1253_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v___y_1228_ = v___x_1254_;
v___y_1229_ = v___x_1255_;
v___y_1230_ = v___x_1256_;
v___y_1231_ = v_val_1251_;
v_val_1232_ = v___x_1263_;
goto v___jp_1227_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_a_1266_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1257_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 0);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v___y_1228_ = v___x_1254_;
v___y_1229_ = v___x_1255_;
v___y_1230_ = v___x_1256_;
v___y_1231_ = v_val_1251_;
v_val_1232_ = v___x_1271_;
goto v___jp_1227_;
}
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v_a_1250_);
lean_dec_ref(v_src_1204_);
lean_dec_ref(v_remoteUrl_1203_);
lean_dec_ref(v_relPkgDir_1202_);
lean_dec_ref(v_dep_1198_);
v___x_1274_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1275_ = lean_string_append(v_name_1201_, v___x_1274_);
v___x_1276_ = lean_string_append(v___x_1275_, v_pkgDir_1248_);
lean_dec_ref(v_pkgDir_1248_);
v___x_1277_ = 3;
v___x_1278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v___x_1277_);
lean_inc_ref(v_a_1205_);
v___x_1279_ = lean_apply_2(v_a_1205_, v___x_1278_, lean_box(0));
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
v___jp_1285_:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1287_ == 0)
{
v_a_1250_ = v_val_1286_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1865__overap_1291_; lean_object* v___x_1292_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1865__overap_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1282_, v___f_1226_, v___x_1284_, v___x_1289_, v___x_1290_, v___x_1288_);
lean_inc_ref(v_a_1205_);
v___x_1292_ = lean_apply_2(v___x_1865__overap_1291_, v_a_1205_, lean_box(0));
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_dec_ref_known(v___x_1292_, 1);
v_a_1250_ = v_val_1286_;
goto v___jp_1249_;
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_val_1286_);
lean_dec_ref(v_pkgDir_1248_);
lean_dec_ref(v_src_1204_);
lean_dec_ref(v_remoteUrl_1203_);
lean_dec_ref(v_relPkgDir_1202_);
lean_dec_ref(v_name_1201_);
lean_dec_ref(v_dep_1198_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1306_, lean_object* v_inherited_1307_, lean_object* v_wsDir_1308_, lean_object* v_name_1309_, lean_object* v_relPkgDir_1310_, lean_object* v_remoteUrl_1311_, lean_object* v_src_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v_inherited_boxed_1315_; lean_object* v_res_1316_; 
v_inherited_boxed_1315_ = lean_unbox(v_inherited_1307_);
v_res_1316_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1306_, v_inherited_boxed_1315_, v_wsDir_1308_, v_name_1309_, v_relPkgDir_1310_, v_remoteUrl_1311_, v_src_1312_, v_a_1313_);
lean_dec_ref(v_a_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1317_, lean_object* v_name_1318_, lean_object* v_repo_1319_, lean_object* v_url_1320_, lean_object* v_rev_x3f_1321_){
_start:
{
lean_object* v___y_1333_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v_a_1407_; lean_object* v___y_1415_; uint8_t v_a_1416_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; uint8_t v_val_1428_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v___y_1438_; lean_object* v___y_1444_; lean_object* v___y_1445_; uint8_t v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1449_; lean_object* v___y_1450_; uint8_t v___y_1451_; lean_object* v___y_1480_; lean_object* v___y_1481_; uint8_t v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; uint8_t v_val_1488_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v_a_1500_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v_a_1547_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1652_; uint8_t v_a_1653_; lean_object* v___y_1661_; uint8_t v_a_1662_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; uint8_t v_val_1673_; uint8_t v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; uint8_t v___y_1688_; lean_object* v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1691_; uint8_t v___y_1693_; lean_object* v___y_1694_; uint8_t v___y_1695_; uint8_t v___y_1724_; lean_object* v___y_1725_; uint8_t v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1729_; lean_object* v___y_1730_; uint8_t v___y_1731_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1734_; lean_object* v_a_1735_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; uint8_t v_val_1782_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v_a_1794_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v_a_1837_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v_a_1913_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v_a_1977_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v_a_1990_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v_val_2005_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v_a_2015_; lean_object* v___y_2024_; 
if (lean_obj_tag(v_rev_x3f_1321_) == 0)
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lake_Git_upstreamBranch;
v___y_2024_ = v___x_2033_;
goto v___jp_2023_;
}
else
{
lean_object* v_val_2034_; 
v_val_2034_ = lean_ctor_get(v_rev_x3f_1321_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v_rev_x3f_1321_, 1);
v___y_2024_ = v_val_2034_;
goto v___jp_2023_;
}
v___jp_1323_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
v___jp_1326_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
v___jp_1329_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
v___jp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1336_ = l_Lake_GitRepo_gcAuto(v_repo_1319_, v___x_1335_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
v_a_1338_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1336_, 2);
v___x_1339_ = lean_array_get_size(v_a_1338_);
v___x_1340_ = lean_nat_dec_lt(v___x_1334_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec(v_a_1338_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_a_1337_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = lean_usize_of_nat(v___x_1339_);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1338_, v___x_1343_, v___x_1344_, v___x_1342_, v___y_1333_);
lean_dec(v_a_1338_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v___x_1345_, 0);
lean_dec(v_unused_1353_);
v___x_1347_ = v___x_1345_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_dec(v___x_1345_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v_a_1337_);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1337_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_dec(v_a_1337_);
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_a_1354_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1336_, 2);
v___x_1355_ = lean_array_get_size(v_a_1354_);
v___x_1356_ = lean_nat_dec_lt(v___x_1334_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_a_1354_);
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = lean_usize_of_nat(v___x_1355_);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1354_, v___x_1360_, v___x_1361_, v___x_1359_, v___y_1333_);
lean_dec(v_a_1354_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1370_);
v___x_1364_ = v___x_1362_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v___x_1362_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set_tag(v___x_1364_, 1);
lean_ctor_set(v___x_1364_, 0, v___x_1359_);
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1359_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
return v___x_1362_;
}
}
}
}
v___jp_1371_:
{
if (lean_obj_tag(v___y_1373_) == 0)
{
lean_dec_ref_known(v___y_1373_, 1);
v___y_1333_ = v___y_1372_;
goto v___jp_1332_;
}
else
{
lean_dec_ref(v_repo_1319_);
return v___y_1373_;
}
}
v___jp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
lean_inc_ref(v___y_1375_);
v___x_1379_ = l_Lake_GitRepo_pruneRemote(v___y_1375_, v_repo_1319_, v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 2);
v___x_1381_ = lean_array_get_size(v_a_1380_);
v___x_1382_ = lean_nat_dec_lt(v___x_1377_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_dec(v_a_1380_);
v___y_1333_ = v___y_1376_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = lean_usize_of_nat(v___x_1381_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1380_, v___x_1384_, v___x_1385_, v___x_1383_, v___y_1376_);
lean_dec(v_a_1380_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_dec_ref_known(v___x_1386_, 1);
v___y_1333_ = v___y_1376_;
goto v___jp_1332_;
}
else
{
v___y_1372_ = v___y_1376_;
v___y_1373_ = v___x_1386_;
goto v___jp_1371_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_a_1387_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1379_, 2);
v___x_1388_ = lean_array_get_size(v_a_1387_);
v___x_1389_ = lean_nat_dec_lt(v___x_1377_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
lean_dec(v_a_1387_);
lean_dec_ref(v_repo_1319_);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
else
{
lean_object* v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = lean_box(0);
v___x_1393_ = ((size_t)0ULL);
v___x_1394_ = lean_usize_of_nat(v___x_1388_);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1387_, v___x_1393_, v___x_1394_, v___x_1392_, v___y_1376_);
lean_dec(v_a_1387_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec_ref(v_repo_1319_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1395_, 0);
lean_dec(v_unused_1403_);
v___x_1397_ = v___x_1395_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_dec(v___x_1395_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 1);
lean_ctor_set(v___x_1397_, 0, v___x_1392_);
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1392_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
else
{
v___y_1372_ = v___y_1376_;
v___y_1373_ = v___x_1395_;
goto v___jp_1371_;
}
}
}
}
v___jp_1404_:
{
if (v_a_1407_ == 0)
{
lean_dec_ref(v_name_1318_);
v___y_1375_ = v___y_1405_;
v___y_1376_ = v___y_1406_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1408_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1409_ = lean_string_append(v_name_1318_, v___x_1408_);
v___x_1410_ = lean_string_append(v___x_1409_, v_repo_1319_);
v___x_1411_ = 2;
v___x_1412_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*1, v___x_1411_);
lean_inc_ref(v___y_1406_);
v___x_1413_ = lean_apply_2(v___y_1406_, v___x_1412_, lean_box(0));
v___y_1375_ = v___y_1405_;
v___y_1376_ = v___y_1406_;
goto v___jp_1374_;
}
}
v___jp_1414_:
{
if (v_a_1416_ == 0)
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
goto v___jp_1329_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1417_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1418_ = lean_string_append(v_name_1318_, v___x_1417_);
v___x_1419_ = lean_string_append(v___x_1418_, v_repo_1319_);
lean_dec_ref(v_repo_1319_);
v___x_1420_ = 2;
v___x_1421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*1, v___x_1420_);
lean_inc_ref(v___y_1415_);
v___x_1422_ = lean_apply_2(v___y_1415_, v___x_1421_, lean_box(0));
goto v___jp_1329_;
}
}
v___jp_1423_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_array_get_size(v___y_1427_);
v___x_1430_ = lean_nat_dec_lt(v___y_1425_, v___x_1429_);
if (v___x_1430_ == 0)
{
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1426_;
v_a_1407_ = v_val_1428_;
goto v___jp_1404_;
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
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1426_;
v_a_1407_ = v_val_1428_;
goto v___jp_1404_;
}
else
{
lean_dec_ref(v_name_1318_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref_known(v___x_1434_, 1);
v___y_1375_ = v___y_1424_;
v___y_1376_ = v___y_1426_;
goto v___jp_1374_;
}
else
{
lean_dec_ref(v_repo_1319_);
return v___x_1434_;
}
}
}
}
v___jp_1435_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1441_ = l_Lake_GitRepo_hasNoDiff(v_repo_1319_);
if (v___x_1441_ == 0)
{
uint8_t v___x_1442_; 
v___x_1442_ = 1;
v___y_1424_ = v___y_1436_;
v___y_1425_ = v___x_1439_;
v___y_1426_ = v___y_1437_;
v___y_1427_ = v___x_1440_;
v_val_1428_ = v___x_1442_;
goto v___jp_1423_;
}
else
{
v___y_1424_ = v___y_1436_;
v___y_1425_ = v___x_1439_;
v___y_1426_ = v___y_1437_;
v___y_1427_ = v___x_1440_;
v_val_1428_ = v___y_1438_;
goto v___jp_1423_;
}
}
v___jp_1443_:
{
if (lean_obj_tag(v___y_1447_) == 0)
{
lean_dec_ref_known(v___y_1447_, 1);
v___y_1436_ = v___y_1444_;
v___y_1437_ = v___y_1445_;
v___y_1438_ = v___y_1446_;
goto v___jp_1435_;
}
else
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1447_;
}
}
v___jp_1448_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1454_ = l_Lake_GitRepo_clean(v_repo_1319_, v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 1);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 2);
v___x_1456_ = lean_array_get_size(v_a_1455_);
v___x_1457_ = lean_nat_dec_lt(v___x_1452_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_dec(v_a_1455_);
v___y_1436_ = v___y_1449_;
v___y_1437_ = v___y_1450_;
v___y_1438_ = v___y_1451_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_box(0);
v___x_1459_ = ((size_t)0ULL);
v___x_1460_ = lean_usize_of_nat(v___x_1456_);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1455_, v___x_1459_, v___x_1460_, v___x_1458_, v___y_1450_);
lean_dec(v_a_1455_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_dec_ref_known(v___x_1461_, 1);
v___y_1436_ = v___y_1449_;
v___y_1437_ = v___y_1450_;
v___y_1438_ = v___y_1451_;
goto v___jp_1435_;
}
else
{
v___y_1444_ = v___y_1449_;
v___y_1445_ = v___y_1450_;
v___y_1446_ = v___y_1451_;
v___y_1447_ = v___x_1461_;
goto v___jp_1443_;
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1454_, 1);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1454_, 2);
v___x_1463_ = lean_array_get_size(v_a_1462_);
v___x_1464_ = lean_nat_dec_lt(v___x_1452_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v_a_1462_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1463_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1462_, v___x_1468_, v___x_1469_, v___x_1467_, v___y_1450_);
lean_dec(v_a_1462_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v___x_1470_, 0);
lean_dec(v_unused_1478_);
v___x_1472_ = v___x_1470_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v___x_1470_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 1);
lean_ctor_set(v___x_1472_, 0, v___x_1467_);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1467_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
v___y_1444_ = v___y_1449_;
v___y_1445_ = v___y_1450_;
v___y_1446_ = v___y_1451_;
v___y_1447_ = v___x_1470_;
goto v___jp_1443_;
}
}
}
}
v___jp_1479_:
{
if (lean_obj_tag(v___y_1483_) == 0)
{
lean_dec_ref_known(v___y_1483_, 1);
v___y_1449_ = v___y_1480_;
v___y_1450_ = v___y_1481_;
v___y_1451_ = v___y_1482_;
goto v___jp_1448_;
}
else
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1483_;
}
}
v___jp_1484_:
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = lean_array_get_size(v___y_1487_);
v___x_1490_ = lean_nat_dec_lt(v___y_1486_, v___x_1489_);
if (v___x_1490_ == 0)
{
v___y_1415_ = v___y_1485_;
v_a_1416_ = v_val_1488_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1491_; size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = lean_usize_of_nat(v___x_1489_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1487_, v___x_1492_, v___x_1493_, v___x_1491_, v___y_1485_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_dec_ref_known(v___x_1494_, 1);
v___y_1415_ = v___y_1485_;
v_a_1416_ = v_val_1488_;
goto v___jp_1414_;
}
else
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_dec_ref_known(v___x_1494_, 1);
goto v___jp_1329_;
}
else
{
return v___x_1494_;
}
}
}
}
v___jp_1495_:
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_1502_ = l_Option_instDecidableEq___redArg(v___x_1501_, v_a_1500_, v___y_1499_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1503_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1318_);
v___x_1504_ = lean_string_append(v_name_1318_, v___x_1503_);
v___x_1505_ = lean_string_append(v___x_1504_, v___y_1498_);
v___x_1506_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1507_ = lean_string_append(v___x_1505_, v___x_1506_);
v___x_1508_ = 1;
v___x_1509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*1, v___x_1508_);
lean_inc_ref(v___y_1497_);
v___x_1510_ = lean_apply_2(v___y_1497_, v___x_1509_, lean_box(0));
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1513_ = l_Lake_GitRepo_checkoutDetach(v___y_1498_, v_repo_1319_, v___x_1512_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 1);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 2);
v___x_1515_ = lean_array_get_size(v_a_1514_);
v___x_1516_ = lean_nat_dec_lt(v___x_1511_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_dec(v_a_1514_);
v___y_1449_ = v___y_1496_;
v___y_1450_ = v___y_1497_;
v___y_1451_ = v___x_1502_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = ((size_t)0ULL);
v___x_1519_ = lean_usize_of_nat(v___x_1515_);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1514_, v___x_1518_, v___x_1519_, v___x_1517_, v___y_1497_);
lean_dec(v_a_1514_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_dec_ref_known(v___x_1520_, 1);
v___y_1449_ = v___y_1496_;
v___y_1450_ = v___y_1497_;
v___y_1451_ = v___x_1502_;
goto v___jp_1448_;
}
else
{
v___y_1480_ = v___y_1496_;
v___y_1481_ = v___y_1497_;
v___y_1482_ = v___x_1502_;
v___y_1483_ = v___x_1520_;
goto v___jp_1479_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_a_1521_ = lean_ctor_get(v___x_1513_, 1);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1513_, 2);
v___x_1522_ = lean_array_get_size(v_a_1521_);
v___x_1523_ = lean_nat_dec_lt(v___x_1511_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_a_1521_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = lean_usize_of_nat(v___x_1522_);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1521_, v___x_1527_, v___x_1528_, v___x_1526_, v___y_1497_);
lean_dec(v_a_1521_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v___x_1529_, 0);
lean_dec(v_unused_1537_);
v___x_1531_ = v___x_1529_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_dec(v___x_1529_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 1);
lean_ctor_set(v___x_1531_, 0, v___x_1526_);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1526_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
v___y_1480_ = v___y_1496_;
v___y_1481_ = v___y_1497_;
v___y_1482_ = v___x_1502_;
v___y_1483_ = v___x_1529_;
goto v___jp_1479_;
}
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
lean_dec_ref(v___y_1498_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1540_ = l_Lake_GitRepo_hasNoDiff(v_repo_1319_);
if (v___x_1540_ == 0)
{
v___y_1485_ = v___y_1497_;
v___y_1486_ = v___x_1538_;
v___y_1487_ = v___x_1539_;
v_val_1488_ = v___x_1502_;
goto v___jp_1484_;
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = 0;
v___y_1485_ = v___y_1497_;
v___y_1486_ = v___x_1538_;
v___y_1487_ = v___x_1539_;
v_val_1488_ = v___x_1541_;
goto v___jp_1484_;
}
}
}
v___jp_1542_:
{
if (lean_obj_tag(v_a_1547_) == 1)
{
lean_object* v_val_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
lean_dec_ref(v___y_1546_);
lean_dec_ref(v___y_1545_);
v_val_1548_ = lean_ctor_get(v_a_1547_, 0);
lean_inc(v_val_1548_);
v___x_1549_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1550_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1319_);
v___x_1551_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1550_, v_repo_1319_);
v___x_1552_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1552_ == 0)
{
v___y_1496_ = v___y_1543_;
v___y_1497_ = v___y_1544_;
v___y_1498_ = v_val_1548_;
v___y_1499_ = v_a_1547_;
v_a_1500_ = v___x_1551_;
goto v___jp_1495_;
}
else
{
lean_object* v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = ((size_t)0ULL);
v___x_1555_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1549_, v___x_1554_, v___x_1555_, v___x_1553_, v___y_1544_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_dec_ref_known(v___x_1556_, 1);
v___y_1496_ = v___y_1543_;
v___y_1497_ = v___y_1544_;
v___y_1498_ = v_val_1548_;
v___y_1499_ = v_a_1547_;
v_a_1500_ = v___x_1551_;
goto v___jp_1495_;
}
else
{
lean_dec(v___x_1551_);
lean_dec_ref_known(v_a_1547_, 1);
lean_dec(v_val_1548_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_1556_;
}
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec(v_a_1547_);
lean_dec_ref(v_repo_1319_);
v___x_1557_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_1558_ = lean_string_append(v_name_1318_, v___x_1557_);
v___x_1559_ = lean_string_append(v___x_1558_, v___y_1546_);
lean_dec_ref(v___y_1546_);
v___x_1560_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_1561_ = lean_string_append(v___x_1559_, v___x_1560_);
v___x_1562_ = lean_string_append(v___x_1561_, v___y_1545_);
lean_dec_ref(v___y_1545_);
v___x_1563_ = 3;
v___x_1564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set_uint8(v___x_1564_, sizeof(void*)*1, v___x_1563_);
lean_inc_ref(v___y_1544_);
v___x_1565_ = lean_apply_2(v___y_1544_, v___x_1564_, lean_box(0));
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
v___jp_1568_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1573_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_1318_);
v___x_1574_ = lean_string_append(v_name_1318_, v___x_1573_);
v___x_1575_ = lean_string_append(v___x_1574_, v___y_1571_);
v___x_1576_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_1577_ = lean_string_append(v___x_1575_, v___x_1576_);
v___x_1578_ = lean_string_append(v___x_1577_, v___y_1570_);
v___x_1579_ = 1;
v___x_1580_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*1, v___x_1579_);
lean_inc_ref(v___y_1572_);
v___x_1581_ = lean_apply_2(v___y_1572_, v___x_1580_, lean_box(0));
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_1571_);
lean_inc_ref(v___y_1569_);
lean_inc_ref(v_repo_1319_);
v___x_1584_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_1319_, v___y_1569_, v___y_1571_, v___x_1583_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_a_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
v_a_1586_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1584_, 2);
v___x_1587_ = lean_array_get_size(v_a_1586_);
v___x_1588_ = lean_nat_dec_lt(v___x_1582_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_dec(v_a_1586_);
v___y_1543_ = v___y_1569_;
v___y_1544_ = v___y_1572_;
v___y_1545_ = v___y_1570_;
v___y_1546_ = v___y_1571_;
v_a_1547_ = v_a_1585_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = lean_usize_of_nat(v___x_1587_);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1586_, v___x_1590_, v___x_1591_, v___x_1589_, v___y_1572_);
lean_dec(v_a_1586_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_dec_ref_known(v___x_1592_, 1);
v___y_1543_ = v___y_1569_;
v___y_1544_ = v___y_1572_;
v___y_1545_ = v___y_1570_;
v___y_1546_ = v___y_1571_;
v_a_1547_ = v_a_1585_;
goto v___jp_1542_;
}
else
{
lean_dec(v_a_1585_);
lean_dec_ref(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
lean_dec_ref(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_a_1593_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1584_, 2);
v___x_1594_ = lean_array_get_size(v_a_1593_);
v___x_1595_ = lean_nat_dec_lt(v___x_1582_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_a_1593_);
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = lean_usize_of_nat(v___x_1594_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1593_, v___x_1599_, v___x_1600_, v___x_1598_, v___y_1572_);
lean_dec(v_a_1593_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1601_, 0);
lean_dec(v_unused_1609_);
v___x_1603_ = v___x_1601_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v___x_1601_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 1);
lean_ctor_set(v___x_1603_, 0, v___x_1598_);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1598_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
return v___x_1601_;
}
}
}
}
v___jp_1610_:
{
if (lean_obj_tag(v___y_1614_) == 0)
{
lean_dec_ref_known(v___y_1614_, 1);
v___y_1569_ = v___y_1611_;
v___y_1570_ = v___y_1612_;
v___y_1571_ = v___y_1613_;
v___y_1572_ = v_a_1317_;
goto v___jp_1568_;
}
else
{
lean_dec_ref(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1614_;
}
}
v___jp_1615_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
lean_inc_ref(v___y_1617_);
lean_inc_ref(v___y_1616_);
v___x_1621_ = l_Lake_GitRepo_addRemote(v___y_1616_, v___y_1617_, v_repo_1319_, v___x_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 2);
v___x_1623_ = lean_array_get_size(v_a_1622_);
v___x_1624_ = lean_nat_dec_lt(v___x_1619_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_dec(v_a_1622_);
v___y_1569_ = v___y_1616_;
v___y_1570_ = v___y_1617_;
v___y_1571_ = v___y_1618_;
v___y_1572_ = v_a_1317_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v___x_1625_ = lean_box(0);
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1623_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1622_, v___x_1626_, v___x_1627_, v___x_1625_, v_a_1317_);
lean_dec(v_a_1622_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_dec_ref_known(v___x_1628_, 1);
v___y_1569_ = v___y_1616_;
v___y_1570_ = v___y_1617_;
v___y_1571_ = v___y_1618_;
v___y_1572_ = v_a_1317_;
goto v___jp_1568_;
}
else
{
v___y_1611_ = v___y_1616_;
v___y_1612_ = v___y_1617_;
v___y_1613_ = v___y_1618_;
v___y_1614_ = v___x_1628_;
goto v___jp_1610_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_a_1629_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1621_, 2);
v___x_1630_ = lean_array_get_size(v_a_1629_);
v___x_1631_ = lean_nat_dec_lt(v___x_1619_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v_a_1629_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = lean_box(0);
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = lean_usize_of_nat(v___x_1630_);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1629_, v___x_1635_, v___x_1636_, v___x_1634_, v_a_1317_);
lean_dec(v_a_1629_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v___x_1637_, 0);
lean_dec(v_unused_1645_);
v___x_1639_ = v___x_1637_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_dec(v___x_1637_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set_tag(v___x_1639_, 1);
lean_ctor_set(v___x_1639_, 0, v___x_1634_);
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1634_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
v___y_1611_ = v___y_1616_;
v___y_1612_ = v___y_1617_;
v___y_1613_ = v___y_1618_;
v___y_1614_ = v___x_1637_;
goto v___jp_1610_;
}
}
}
}
v___jp_1646_:
{
if (lean_obj_tag(v___y_1650_) == 0)
{
lean_dec_ref_known(v___y_1650_, 1);
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1649_;
goto v___jp_1615_;
}
else
{
lean_dec_ref(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1650_;
}
}
v___jp_1651_:
{
if (v_a_1653_ == 0)
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
goto v___jp_1326_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1654_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1655_ = lean_string_append(v_name_1318_, v___x_1654_);
v___x_1656_ = lean_string_append(v___x_1655_, v_repo_1319_);
lean_dec_ref(v_repo_1319_);
v___x_1657_ = 2;
v___x_1658_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*1, v___x_1657_);
lean_inc_ref(v___y_1652_);
v___x_1659_ = lean_apply_2(v___y_1652_, v___x_1658_, lean_box(0));
goto v___jp_1326_;
}
}
v___jp_1660_:
{
if (v_a_1662_ == 0)
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
goto v___jp_1323_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1663_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1664_ = lean_string_append(v_name_1318_, v___x_1663_);
v___x_1665_ = lean_string_append(v___x_1664_, v_repo_1319_);
lean_dec_ref(v_repo_1319_);
v___x_1666_ = 2;
v___x_1667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*1, v___x_1666_);
lean_inc_ref(v___y_1661_);
v___x_1668_ = lean_apply_2(v___y_1661_, v___x_1667_, lean_box(0));
goto v___jp_1323_;
}
}
v___jp_1669_:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_array_get_size(v___y_1671_);
v___x_1675_ = lean_nat_dec_lt(v___y_1670_, v___x_1674_);
if (v___x_1675_ == 0)
{
v___y_1652_ = v___y_1672_;
v_a_1653_ = v_val_1673_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1676_; size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = lean_usize_of_nat(v___x_1674_);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1671_, v___x_1677_, v___x_1678_, v___x_1676_, v___y_1672_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_dec_ref_known(v___x_1679_, 1);
v___y_1652_ = v___y_1672_;
v_a_1653_ = v_val_1673_;
goto v___jp_1651_;
}
else
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_dec_ref_known(v___x_1679_, 1);
goto v___jp_1326_;
}
else
{
return v___x_1679_;
}
}
}
}
v___jp_1680_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1686_ = l_Lake_GitRepo_hasNoDiff(v_repo_1319_);
if (v___x_1686_ == 0)
{
v___y_1670_ = v___x_1684_;
v___y_1671_ = v___x_1685_;
v___y_1672_ = v___y_1682_;
v_val_1673_ = v___y_1681_;
goto v___jp_1669_;
}
else
{
v___y_1670_ = v___x_1684_;
v___y_1671_ = v___x_1685_;
v___y_1672_ = v___y_1682_;
v_val_1673_ = v___y_1683_;
goto v___jp_1669_;
}
}
v___jp_1687_:
{
if (lean_obj_tag(v___y_1691_) == 0)
{
lean_dec_ref_known(v___y_1691_, 1);
v___y_1681_ = v___y_1688_;
v___y_1682_ = v___y_1689_;
v___y_1683_ = v___y_1690_;
goto v___jp_1680_;
}
else
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1691_;
}
}
v___jp_1692_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1698_ = l_Lake_GitRepo_clean(v_repo_1319_, v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 1);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 2);
v___x_1700_ = lean_array_get_size(v_a_1699_);
v___x_1701_ = lean_nat_dec_lt(v___x_1696_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_dec(v_a_1699_);
v___y_1681_ = v___y_1693_;
v___y_1682_ = v___y_1694_;
v___y_1683_ = v___y_1695_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1700_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1699_, v___x_1703_, v___x_1704_, v___x_1702_, v___y_1694_);
lean_dec(v_a_1699_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec_ref_known(v___x_1705_, 1);
v___y_1681_ = v___y_1693_;
v___y_1682_ = v___y_1694_;
v___y_1683_ = v___y_1695_;
goto v___jp_1680_;
}
else
{
v___y_1688_ = v___y_1693_;
v___y_1689_ = v___y_1694_;
v___y_1690_ = v___y_1695_;
v___y_1691_ = v___x_1705_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_a_1706_ = lean_ctor_get(v___x_1698_, 1);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1698_, 2);
v___x_1707_ = lean_array_get_size(v_a_1706_);
v___x_1708_ = lean_nat_dec_lt(v___x_1696_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v_a_1706_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = lean_usize_of_nat(v___x_1707_);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1706_, v___x_1712_, v___x_1713_, v___x_1711_, v___y_1694_);
lean_dec(v_a_1706_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v___x_1714_, 0);
lean_dec(v_unused_1722_);
v___x_1716_ = v___x_1714_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_dec(v___x_1714_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set_tag(v___x_1716_, 1);
lean_ctor_set(v___x_1716_, 0, v___x_1711_);
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1711_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
v___y_1688_ = v___y_1693_;
v___y_1689_ = v___y_1694_;
v___y_1690_ = v___y_1695_;
v___y_1691_ = v___x_1714_;
goto v___jp_1687_;
}
}
}
}
v___jp_1723_:
{
if (lean_obj_tag(v___y_1727_) == 0)
{
lean_dec_ref_known(v___y_1727_, 1);
v___y_1693_ = v___y_1724_;
v___y_1694_ = v___y_1725_;
v___y_1695_ = v___y_1726_;
goto v___jp_1692_;
}
else
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1727_;
}
}
v___jp_1728_:
{
if (lean_obj_tag(v_a_1735_) == 0)
{
v___y_1569_ = v___y_1729_;
v___y_1570_ = v___y_1730_;
v___y_1571_ = v___y_1734_;
v___y_1572_ = v___y_1732_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1776_; 
v_isSharedCheck_1776_ = !lean_is_exclusive(v_a_1735_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v_a_1735_, 0);
lean_dec(v_unused_1777_);
v___x_1737_ = v_a_1735_;
v_isShared_1738_ = v_isSharedCheck_1776_;
goto v_resetjp_1736_;
}
else
{
lean_dec(v_a_1735_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1776_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
if (v___y_1731_ == 0)
{
lean_del_object(v___x_1737_);
v___y_1569_ = v___y_1729_;
v___y_1570_ = v___y_1730_;
v___y_1571_ = v___y_1734_;
v___y_1572_ = v___y_1732_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref(v___y_1730_);
v___x_1739_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1318_);
v___x_1740_ = lean_string_append(v_name_1318_, v___x_1739_);
v___x_1741_ = lean_string_append(v___x_1740_, v___y_1734_);
v___x_1742_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1743_ = lean_string_append(v___x_1741_, v___x_1742_);
v___x_1744_ = 1;
v___x_1745_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*1, v___x_1744_);
lean_inc_ref(v___y_1732_);
v___x_1746_ = lean_apply_2(v___y_1732_, v___x_1745_, lean_box(0));
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1749_ = l_Lake_GitRepo_checkoutDetach(v___y_1734_, v_repo_1319_, v___x_1748_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
lean_del_object(v___x_1737_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 1);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 2);
v___x_1751_ = lean_array_get_size(v_a_1750_);
v___x_1752_ = lean_nat_dec_lt(v___x_1747_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec(v_a_1750_);
v___y_1693_ = v___y_1731_;
v___y_1694_ = v___y_1732_;
v___y_1695_ = v___y_1733_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1753_; size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1753_ = lean_box(0);
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = lean_usize_of_nat(v___x_1751_);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1750_, v___x_1754_, v___x_1755_, v___x_1753_, v___y_1732_);
lean_dec(v_a_1750_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_dec_ref_known(v___x_1756_, 1);
v___y_1693_ = v___y_1731_;
v___y_1694_ = v___y_1732_;
v___y_1695_ = v___y_1733_;
goto v___jp_1692_;
}
else
{
v___y_1724_ = v___y_1731_;
v___y_1725_ = v___y_1732_;
v___y_1726_ = v___y_1733_;
v___y_1727_ = v___x_1756_;
goto v___jp_1723_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_a_1757_ = lean_ctor_get(v___x_1749_, 1);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1749_, 2);
v___x_1758_ = lean_array_get_size(v_a_1757_);
v___x_1759_ = lean_nat_dec_lt(v___x_1747_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
lean_dec(v_a_1757_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1760_ = lean_box(0);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1760_);
v___x_1762_ = v___x_1737_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
else
{
lean_object* v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
lean_del_object(v___x_1737_);
v___x_1764_ = lean_box(0);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = lean_usize_of_nat(v___x_1758_);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1757_, v___x_1765_, v___x_1766_, v___x_1764_, v___y_1732_);
lean_dec(v_a_1757_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v___x_1767_, 0);
lean_dec(v_unused_1775_);
v___x_1769_ = v___x_1767_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_dec(v___x_1767_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 1);
lean_ctor_set(v___x_1769_, 0, v___x_1764_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1764_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
else
{
v___y_1724_ = v___y_1731_;
v___y_1725_ = v___y_1732_;
v___y_1726_ = v___y_1733_;
v___y_1727_ = v___x_1767_;
goto v___jp_1723_;
}
}
}
}
}
}
}
v___jp_1778_:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_array_get_size(v___y_1781_);
v___x_1784_ = lean_nat_dec_lt(v___y_1779_, v___x_1783_);
if (v___x_1784_ == 0)
{
v___y_1661_ = v___y_1780_;
v_a_1662_ = v_val_1782_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1785_; size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = lean_box(0);
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = lean_usize_of_nat(v___x_1783_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1781_, v___x_1786_, v___x_1787_, v___x_1785_, v___y_1780_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_dec_ref_known(v___x_1788_, 1);
v___y_1661_ = v___y_1780_;
v_a_1662_ = v_val_1782_;
goto v___jp_1660_;
}
else
{
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_dec_ref_known(v___x_1788_, 1);
goto v___jp_1323_;
}
else
{
return v___x_1788_;
}
}
}
}
v___jp_1789_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_1793_);
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___y_1793_);
v___x_1797_ = l_Option_instDecidableEq___redArg(v___x_1795_, v_a_1794_, v___x_1796_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Lake_GitRev_isFullSha1(v___y_1793_);
if (v___x_1798_ == 0)
{
v___y_1569_ = v___y_1790_;
v___y_1570_ = v___y_1791_;
v___y_1571_ = v___y_1793_;
v___y_1572_ = v___y_1792_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1799_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
lean_inc_ref(v___y_1793_);
v___x_1800_ = l_Lake_GitRepo_findCommit_x3f(v___y_1793_, v_repo_1319_);
v___x_1801_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1801_ == 0)
{
v___y_1729_ = v___y_1790_;
v___y_1730_ = v___y_1791_;
v___y_1731_ = v___x_1798_;
v___y_1732_ = v___y_1792_;
v___y_1733_ = v___x_1797_;
v___y_1734_ = v___y_1793_;
v_a_1735_ = v___x_1800_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = lean_box(0);
v___x_1803_ = ((size_t)0ULL);
v___x_1804_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1799_, v___x_1803_, v___x_1804_, v___x_1802_, v___y_1792_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_dec_ref_known(v___x_1805_, 1);
v___y_1729_ = v___y_1790_;
v___y_1730_ = v___y_1791_;
v___y_1731_ = v___x_1798_;
v___y_1732_ = v___y_1792_;
v___y_1733_ = v___x_1797_;
v___y_1734_ = v___y_1793_;
v_a_1735_ = v___x_1800_;
goto v___jp_1728_;
}
else
{
lean_dec(v___x_1800_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_1805_;
}
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1791_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1808_ = l_Lake_GitRepo_hasNoDiff(v_repo_1319_);
if (v___x_1808_ == 0)
{
v___y_1779_ = v___x_1806_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___x_1807_;
v_val_1782_ = v___x_1797_;
goto v___jp_1778_;
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = 0;
v___y_1779_ = v___x_1806_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___x_1807_;
v_val_1782_ = v___x_1809_;
goto v___jp_1778_;
}
}
}
v___jp_1810_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1816_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1319_);
v___x_1817_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1816_, v_repo_1319_);
v___x_1818_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1818_ == 0)
{
v___y_1790_ = v___y_1811_;
v___y_1791_ = v___y_1812_;
v___y_1792_ = v___y_1814_;
v___y_1793_ = v___y_1813_;
v_a_1794_ = v___x_1817_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1819_ = lean_box(0);
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1815_, v___x_1820_, v___x_1821_, v___x_1819_, v___y_1814_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_dec_ref_known(v___x_1822_, 1);
v___y_1790_ = v___y_1811_;
v___y_1791_ = v___y_1812_;
v___y_1792_ = v___y_1814_;
v___y_1793_ = v___y_1813_;
v_a_1794_ = v___x_1817_;
goto v___jp_1789_;
}
else
{
lean_dec(v___x_1817_);
lean_dec_ref(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_1822_;
}
}
}
v___jp_1823_:
{
if (lean_obj_tag(v___y_1827_) == 0)
{
lean_dec_ref_known(v___y_1827_, 1);
v___y_1811_ = v___y_1824_;
v___y_1812_ = v___y_1825_;
v___y_1813_ = v___y_1826_;
v___y_1814_ = v_a_1317_;
goto v___jp_1810_;
}
else
{
lean_dec_ref(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1827_;
}
}
v___jp_1828_:
{
if (lean_obj_tag(v___y_1832_) == 0)
{
lean_dec_ref_known(v___y_1832_, 1);
v___y_1811_ = v___y_1829_;
v___y_1812_ = v___y_1830_;
v___y_1813_ = v___y_1831_;
v___y_1814_ = v_a_1317_;
goto v___jp_1810_;
}
else
{
lean_dec_ref(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___y_1832_;
}
}
v___jp_1833_:
{
if (lean_obj_tag(v_a_1837_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1881_; 
v_val_1838_ = lean_ctor_get(v_a_1837_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1840_ = v_a_1837_;
v_isShared_1841_ = v_isSharedCheck_1881_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v_a_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1881_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_string_dec_eq(v_val_1838_, v___y_1835_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1843_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_1318_);
v___x_1844_ = lean_string_append(v_name_1318_, v___x_1843_);
v___x_1845_ = lean_string_append(v___x_1844_, v_val_1838_);
lean_dec(v_val_1838_);
v___x_1846_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_1847_ = lean_string_append(v___x_1845_, v___x_1846_);
v___x_1848_ = lean_string_append(v___x_1847_, v___y_1835_);
v___x_1849_ = 1;
v___x_1850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*1, v___x_1849_);
lean_inc_ref(v_a_1317_);
v___x_1851_ = lean_apply_2(v_a_1317_, v___x_1850_, lean_box(0));
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
lean_inc_ref(v___y_1835_);
lean_inc_ref(v___y_1834_);
v___x_1854_ = l_Lake_GitRepo_setRemoteUrl(v___y_1834_, v___y_1835_, v_repo_1319_, v___x_1853_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
lean_del_object(v___x_1840_);
v_a_1855_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 2);
v___x_1856_ = lean_array_get_size(v_a_1855_);
v___x_1857_ = lean_nat_dec_lt(v___x_1852_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_dec(v_a_1855_);
v___y_1811_ = v___y_1834_;
v___y_1812_ = v___y_1835_;
v___y_1813_ = v___y_1836_;
v___y_1814_ = v_a_1317_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = lean_box(0);
v___x_1859_ = ((size_t)0ULL);
v___x_1860_ = lean_usize_of_nat(v___x_1856_);
v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1855_, v___x_1859_, v___x_1860_, v___x_1858_, v_a_1317_);
lean_dec(v_a_1855_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref_known(v___x_1861_, 1);
v___y_1811_ = v___y_1834_;
v___y_1812_ = v___y_1835_;
v___y_1813_ = v___y_1836_;
v___y_1814_ = v_a_1317_;
goto v___jp_1810_;
}
else
{
v___y_1829_ = v___y_1834_;
v___y_1830_ = v___y_1835_;
v___y_1831_ = v___y_1836_;
v___y_1832_ = v___x_1861_;
goto v___jp_1828_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_a_1862_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1854_, 2);
v___x_1863_ = lean_array_get_size(v_a_1862_);
v___x_1864_ = lean_nat_dec_lt(v___x_1852_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec(v_a_1862_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1865_ = lean_box(0);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1865_);
v___x_1867_ = v___x_1840_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v___x_1869_; size_t v___x_1870_; size_t v___x_1871_; lean_object* v___x_1872_; 
lean_del_object(v___x_1840_);
v___x_1869_ = lean_box(0);
v___x_1870_ = ((size_t)0ULL);
v___x_1871_ = lean_usize_of_nat(v___x_1863_);
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1862_, v___x_1870_, v___x_1871_, v___x_1869_, v_a_1317_);
lean_dec(v_a_1862_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v___x_1872_, 0);
lean_dec(v_unused_1880_);
v___x_1874_ = v___x_1872_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v___x_1872_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 1);
lean_ctor_set(v___x_1874_, 0, v___x_1869_);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1869_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
v___y_1829_ = v___y_1834_;
v___y_1830_ = v___y_1835_;
v___y_1831_ = v___y_1836_;
v___y_1832_ = v___x_1872_;
goto v___jp_1828_;
}
}
}
}
else
{
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
v___y_1811_ = v___y_1834_;
v___y_1812_ = v___y_1835_;
v___y_1813_ = v___y_1836_;
v___y_1814_ = v_a_1317_;
goto v___jp_1810_;
}
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec(v_a_1837_);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
lean_inc_ref(v___y_1835_);
lean_inc_ref(v___y_1834_);
v___x_1884_ = l_Lake_GitRepo_addRemote(v___y_1834_, v___y_1835_, v_repo_1319_, v___x_1883_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 1);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 2);
v___x_1886_ = lean_array_get_size(v_a_1885_);
v___x_1887_ = lean_nat_dec_lt(v___x_1882_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_dec(v_a_1885_);
v___y_1811_ = v___y_1834_;
v___y_1812_ = v___y_1835_;
v___y_1813_ = v___y_1836_;
v___y_1814_ = v_a_1317_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = lean_usize_of_nat(v___x_1886_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1885_, v___x_1889_, v___x_1890_, v___x_1888_, v_a_1317_);
lean_dec(v_a_1885_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_dec_ref_known(v___x_1891_, 1);
v___y_1811_ = v___y_1834_;
v___y_1812_ = v___y_1835_;
v___y_1813_ = v___y_1836_;
v___y_1814_ = v_a_1317_;
goto v___jp_1810_;
}
else
{
v___y_1824_ = v___y_1834_;
v___y_1825_ = v___y_1835_;
v___y_1826_ = v___y_1836_;
v___y_1827_ = v___x_1891_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_a_1892_ = lean_ctor_get(v___x_1884_, 1);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1884_, 2);
v___x_1893_ = lean_array_get_size(v_a_1892_);
v___x_1894_ = lean_nat_dec_lt(v___x_1882_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_a_1892_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = lean_usize_of_nat(v___x_1893_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1892_, v___x_1898_, v___x_1899_, v___x_1897_, v_a_1317_);
lean_dec(v_a_1892_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___x_1900_, 0);
lean_dec(v_unused_1908_);
v___x_1902_ = v___x_1900_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v___x_1900_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 1);
lean_ctor_set(v___x_1902_, 0, v___x_1897_);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1897_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
v___y_1824_ = v___y_1834_;
v___y_1825_ = v___y_1835_;
v___y_1826_ = v___y_1836_;
v___y_1827_ = v___x_1900_;
goto v___jp_1823_;
}
}
}
}
}
v___jp_1909_:
{
if (v_a_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1914_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_1318_);
v___x_1915_ = lean_string_append(v_name_1318_, v___x_1914_);
v___x_1916_ = 1;
v___x_1917_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*1, v___x_1916_);
lean_inc_ref(v_a_1317_);
v___x_1918_ = lean_apply_2(v_a_1317_, v___x_1917_, lean_box(0));
lean_inc_ref(v_repo_1319_);
v___x_1919_ = l_IO_FS_createDirAll(v_repo_1319_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1952_; 
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; 
v_unused_1953_ = lean_ctor_get(v___x_1919_, 0);
lean_dec(v_unused_1953_);
v___x_1921_ = v___x_1919_;
v_isShared_1922_ = v_isSharedCheck_1952_;
goto v_resetjp_1920_;
}
else
{
lean_dec(v___x_1919_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1952_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
v___x_1925_ = l_Lake_GitRepo_quietInit(v_repo_1319_, v___x_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
lean_del_object(v___x_1921_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 1);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 2);
v___x_1927_ = lean_array_get_size(v_a_1926_);
v___x_1928_ = lean_nat_dec_lt(v___x_1923_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_dec(v_a_1926_);
v___y_1616_ = v___y_1910_;
v___y_1617_ = v___y_1911_;
v___y_1618_ = v___y_1912_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1929_ = lean_box(0);
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = lean_usize_of_nat(v___x_1927_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1926_, v___x_1930_, v___x_1931_, v___x_1929_, v_a_1317_);
lean_dec(v_a_1926_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_dec_ref_known(v___x_1932_, 1);
v___y_1616_ = v___y_1910_;
v___y_1617_ = v___y_1911_;
v___y_1618_ = v___y_1912_;
goto v___jp_1615_;
}
else
{
v___y_1647_ = v___y_1910_;
v___y_1648_ = v___y_1911_;
v___y_1649_ = v___y_1912_;
v___y_1650_ = v___x_1932_;
goto v___jp_1646_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_a_1933_ = lean_ctor_get(v___x_1925_, 1);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1925_, 2);
v___x_1934_ = lean_array_get_size(v_a_1933_);
v___x_1935_ = lean_nat_dec_lt(v___x_1923_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_dec(v_a_1933_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v___x_1936_ = lean_box(0);
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 1);
lean_ctor_set(v___x_1921_, 0, v___x_1936_);
v___x_1938_ = v___x_1921_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
else
{
lean_object* v___x_1940_; size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
lean_del_object(v___x_1921_);
v___x_1940_ = lean_box(0);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = lean_usize_of_nat(v___x_1934_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1933_, v___x_1941_, v___x_1942_, v___x_1940_, v_a_1317_);
lean_dec(v_a_1933_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set_tag(v___x_1945_, 1);
lean_ctor_set(v___x_1945_, 0, v___x_1940_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1940_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
v___y_1647_ = v___y_1910_;
v___y_1648_ = v___y_1911_;
v___y_1649_ = v___y_1912_;
v___y_1650_ = v___x_1943_;
goto v___jp_1646_;
}
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
v_a_1954_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1956_ = v___x_1919_;
v_isShared_1957_ = v_isSharedCheck_1966_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1919_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1966_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1958_ = lean_io_error_to_string(v_a_1954_);
v___x_1959_ = 3;
v___x_1960_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set_uint8(v___x_1960_, sizeof(void*)*1, v___x_1959_);
lean_inc_ref(v_a_1317_);
v___x_1961_ = lean_apply_2(v_a_1317_, v___x_1960_, lean_box(0));
v___x_1962_ = lean_box(0);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1962_);
v___x_1964_ = v___x_1956_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
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
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1967_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1319_);
lean_inc_ref(v___y_1910_);
v___x_1968_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_1910_, v_repo_1319_);
v___x_1969_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1969_ == 0)
{
v___y_1834_ = v___y_1910_;
v___y_1835_ = v___y_1911_;
v___y_1836_ = v___y_1912_;
v_a_1837_ = v___x_1968_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1970_ = lean_box(0);
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1967_, v___x_1971_, v___x_1972_, v___x_1970_, v_a_1317_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_dec_ref_known(v___x_1973_, 1);
v___y_1834_ = v___y_1910_;
v___y_1835_ = v___y_1911_;
v___y_1836_ = v___y_1912_;
v_a_1837_ = v___x_1968_;
goto v___jp_1833_;
}
else
{
lean_dec(v___x_1968_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_1973_;
}
}
}
}
v___jp_1974_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; uint8_t v___x_1982_; 
v___x_1978_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1979_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_1319_);
v___x_1980_ = l_System_FilePath_join(v_repo_1319_, v___x_1979_);
v___x_1981_ = l_System_FilePath_pathExists(v___x_1980_);
lean_dec_ref(v___x_1980_);
v___x_1982_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1982_ == 0)
{
v___y_1910_ = v___y_1975_;
v___y_1911_ = v_a_1977_;
v___y_1912_ = v___y_1976_;
v_a_1913_ = v___x_1981_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1983_; size_t v___x_1984_; size_t v___x_1985_; lean_object* v___x_1986_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = ((size_t)0ULL);
v___x_1985_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1978_, v___x_1984_, v___x_1985_, v___x_1983_, v_a_1317_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_dec_ref_known(v___x_1986_, 1);
v___y_1910_ = v___y_1975_;
v___y_1911_ = v_a_1977_;
v___y_1912_ = v___y_1976_;
v_a_1913_ = v___x_1981_;
goto v___jp_1909_;
}
else
{
lean_dec_ref(v_a_1977_);
lean_dec_ref(v___y_1976_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_1986_;
}
}
}
v___jp_1987_:
{
if (lean_obj_tag(v_a_1990_) == 1)
{
lean_object* v_val_1991_; 
lean_dec_ref(v_url_1320_);
v_val_1991_ = lean_ctor_get(v_a_1990_, 0);
lean_inc(v_val_1991_);
lean_dec_ref_known(v_a_1990_, 1);
v___y_1975_ = v___y_1988_;
v___y_1976_ = v___y_1989_;
v_a_1977_ = v_val_1991_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec(v_a_1990_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v_repo_1319_);
v___x_1992_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_1993_ = lean_string_append(v_name_1318_, v___x_1992_);
v___x_1994_ = lean_string_append(v___x_1993_, v_url_1320_);
lean_dec_ref(v_url_1320_);
v___x_1995_ = 3;
v___x_1996_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set_uint8(v___x_1996_, sizeof(void*)*1, v___x_1995_);
lean_inc_ref(v_a_1317_);
v___x_1997_ = lean_apply_2(v_a_1317_, v___x_1996_, lean_box(0));
v___x_1998_ = lean_box(0);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
}
v___jp_2000_:
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = lean_array_get_size(v___y_2003_);
v___x_2007_ = lean_nat_dec_lt(v___y_2002_, v___x_2006_);
if (v___x_2007_ == 0)
{
v___y_1988_ = v___y_2001_;
v___y_1989_ = v___y_2004_;
v_a_1990_ = v_val_2005_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2008_; size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_of_nat(v___x_2006_);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2003_, v___x_2009_, v___x_2010_, v___x_2008_, v_a_1317_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
v___y_1988_ = v___y_2001_;
v___y_1989_ = v___y_2004_;
v_a_1990_ = v_val_2005_;
goto v___jp_1987_;
}
else
{
lean_dec(v_val_2005_);
lean_dec_ref(v___y_2004_);
lean_dec_ref(v_url_1320_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_2011_;
}
}
}
v___jp_2012_:
{
if (v_a_2015_ == 0)
{
v___y_1975_ = v___y_2013_;
v___y_1976_ = v___y_2014_;
v_a_1977_ = v_url_1320_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_1320_);
v___x_2018_ = l_Lake_resolvePath(v_url_1320_);
v___x_2019_ = lean_string_utf8_byte_size(v___x_2018_);
v___x_2020_ = lean_nat_dec_eq(v___x_2019_, v___x_2016_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2018_);
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___x_2016_;
v___y_2003_ = v___x_2017_;
v___y_2004_ = v___y_2014_;
v_val_2005_ = v___x_2021_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v___x_2018_);
v___x_2022_ = lean_box(0);
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___x_2016_;
v___y_2003_ = v___x_2017_;
v___y_2004_ = v___y_2014_;
v_val_2005_ = v___x_2022_;
goto v___jp_2000_;
}
}
}
v___jp_2023_:
{
lean_object* v_remote_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; uint8_t v___x_2028_; 
v_remote_2025_ = l_Lake_Git_defaultRemote;
v___x_2026_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2027_ = l_System_FilePath_pathExists(v_url_1320_);
v___x_2028_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2028_ == 0)
{
v___y_2013_ = v_remote_2025_;
v___y_2014_ = v___y_2024_;
v_a_2015_ = v___x_2027_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = ((size_t)0ULL);
v___x_2031_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2026_, v___x_2030_, v___x_2031_, v___x_2029_, v_a_1317_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_dec_ref_known(v___x_2032_, 1);
v___y_2013_ = v_remote_2025_;
v___y_2014_ = v___y_2024_;
v_a_2015_ = v___x_2027_;
goto v___jp_2012_;
}
else
{
lean_dec_ref(v___y_2024_);
lean_dec_ref(v_url_1320_);
lean_dec_ref(v_repo_1319_);
lean_dec_ref(v_name_1318_);
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_2035_, lean_object* v_name_2036_, lean_object* v_repo_2037_, lean_object* v_url_2038_, lean_object* v_rev_x3f_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2035_, v_name_2036_, v_repo_2037_, v_url_2038_, v_rev_x3f_2039_);
lean_dec_ref(v_a_2035_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_2042_, uint8_t v_inherited_2043_, lean_object* v_lakeEnv_2044_, lean_object* v_wsDir_2045_, lean_object* v_name_2046_, lean_object* v_relPkgDir_2047_, lean_object* v_gitUrl_2048_, lean_object* v_remoteUrl_2049_, lean_object* v_inputRev_x3f_2050_, lean_object* v_subDir_x3f_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_pkgUrlMap_2054_; lean_object* v_name_2055_; lean_object* v_scope_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2232_; 
v_pkgUrlMap_2054_ = lean_ctor_get(v_lakeEnv_2044_, 5);
v_name_2055_ = lean_ctor_get(v_dep_2042_, 0);
v_scope_2056_ = lean_ctor_get(v_dep_2042_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_dep_2042_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; 
v_unused_2233_ = lean_ctor_get(v_dep_2042_, 4);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_dep_2042_, 3);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_dep_2042_, 2);
lean_dec(v_unused_2235_);
v___x_2058_ = v_dep_2042_;
v_isShared_2059_ = v_isSharedCheck_2232_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_scope_2056_);
lean_inc(v_name_2055_);
lean_dec(v_dep_2042_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2232_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v_a_2064_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v_val_2078_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v_a_2097_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v_val_2134_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2163_; lean_object* v_a_2164_; lean_object* v_gitDir_2167_; lean_object* v___y_2169_; lean_object* v___x_2230_; 
lean_inc_ref(v_relPkgDir_2047_);
lean_inc_ref(v_wsDir_2045_);
v_gitDir_2167_ = l_Lake_joinRelative(v_wsDir_2045_, v_relPkgDir_2047_);
v___x_2230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2054_, v_name_2055_);
if (lean_obj_tag(v___x_2230_) == 0)
{
v___y_2169_ = v_gitUrl_2048_;
goto v___jp_2168_;
}
else
{
lean_object* v_val_2231_; 
lean_dec_ref(v_gitUrl_2048_);
v_val_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___y_2169_ = v_val_2231_;
goto v___jp_2168_;
}
v___jp_2060_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2065_ = l_Lake_defaultConfigFile;
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2067_, 0, v_name_2055_);
lean_ctor_set(v___x_2067_, 1, v_scope_2056_);
lean_ctor_set(v___x_2067_, 2, v___x_2065_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
lean_ctor_set(v___x_2067_, 4, v___y_2063_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5, v_inherited_2043_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 4, v___x_2067_);
lean_ctor_set(v___x_2058_, 3, v_a_2064_);
lean_ctor_set(v___x_2058_, 2, v_remoteUrl_2049_);
lean_ctor_set(v___x_2058_, 1, v___y_2061_);
lean_ctor_set(v___x_2058_, 0, v___y_2062_);
v___x_2069_ = v___x_2058_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___y_2062_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___y_2061_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_remoteUrl_2049_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_a_2064_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
v___jp_2072_:
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = lean_array_get_size(v___y_2077_);
v___x_2080_ = lean_nat_dec_lt(v___y_2074_, v___x_2079_);
if (v___x_2080_ == 0)
{
v___y_2061_ = v___y_2073_;
v___y_2062_ = v___y_2075_;
v___y_2063_ = v___y_2076_;
v_a_2064_ = v_val_2078_;
goto v___jp_2060_;
}
else
{
lean_object* v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2079_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2077_, v___x_2082_, v___x_2083_, v___x_2081_, v_a_2052_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_dec_ref_known(v___x_2084_, 1);
v___y_2061_ = v___y_2073_;
v___y_2062_ = v___y_2075_;
v___y_2063_ = v___y_2076_;
v_a_2064_ = v_val_2078_;
goto v___jp_2060_;
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_val_2078_);
lean_dec_ref(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec_ref(v___y_2073_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_scope_2056_);
lean_dec(v_name_2055_);
lean_dec_ref(v_remoteUrl_2049_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
v___jp_2093_:
{
if (lean_obj_tag(v_a_2097_) == 1)
{
lean_object* v_val_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_name_2046_);
v_val_2098_ = lean_ctor_get(v_a_2097_, 0);
lean_inc_n(v_val_2098_, 2);
lean_dec_ref_known(v_a_2097_, 1);
v___x_2099_ = l_Lake_defaultManifestFile;
v___x_2100_ = l_Lake_joinRelative(v_val_2098_, v___x_2099_);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2103_ = l_Lake_Manifest_load(v___x_2100_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 1);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
v___y_2073_ = v___y_2094_;
v___y_2074_ = v___x_2101_;
v___y_2075_ = v_val_2098_;
v___y_2076_ = v___y_2096_;
v___y_2077_ = v___x_2102_;
v_val_2078_ = v___x_2109_;
goto v___jp_2072_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2103_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2103_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 0);
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
v___y_2073_ = v___y_2094_;
v___y_2074_ = v___x_2101_;
v___y_2075_ = v_val_2098_;
v___y_2076_ = v___y_2096_;
v___y_2077_ = v___x_2102_;
v_val_2078_ = v___x_2117_;
goto v___jp_2072_;
}
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec(v_a_2097_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v___y_2094_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_scope_2056_);
lean_dec(v_name_2055_);
lean_dec_ref(v_remoteUrl_2049_);
v___x_2120_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2121_ = lean_string_append(v_name_2046_, v___x_2120_);
v___x_2122_ = lean_string_append(v___x_2121_, v___y_2095_);
lean_dec_ref(v___y_2095_);
v___x_2123_ = 3;
v___x_2124_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1, v___x_2123_);
lean_inc_ref(v_a_2052_);
v___x_2125_ = lean_apply_2(v_a_2052_, v___x_2124_, lean_box(0));
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
v___jp_2128_:
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = lean_array_get_size(v___y_2133_);
v___x_2136_ = lean_nat_dec_lt(v___y_2132_, v___x_2135_);
if (v___x_2136_ == 0)
{
v___y_2094_ = v___y_2129_;
v___y_2095_ = v___y_2131_;
v___y_2096_ = v___y_2130_;
v_a_2097_ = v_val_2134_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = lean_usize_of_nat(v___x_2135_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2133_, v___x_2138_, v___x_2139_, v___x_2137_, v_a_2052_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_dec_ref_known(v___x_2140_, 1);
v___y_2094_ = v___y_2129_;
v___y_2095_ = v___y_2131_;
v___y_2096_ = v___y_2130_;
v_a_2097_ = v_val_2134_;
goto v___jp_2093_;
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_val_2134_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_scope_2056_);
lean_dec(v_name_2055_);
lean_dec_ref(v_remoteUrl_2049_);
lean_dec_ref(v_name_2046_);
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
v___jp_2149_:
{
lean_object* v___x_2153_; lean_object* v_pkgDir_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2153_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2153_, 0, v___y_2151_);
lean_ctor_set(v___x_2153_, 1, v___y_2150_);
lean_ctor_set(v___x_2153_, 2, v_inputRev_x3f_2050_);
lean_ctor_set(v___x_2153_, 3, v_subDir_x3f_2051_);
lean_inc_ref(v___y_2152_);
v_pkgDir_2154_ = l_Lake_joinRelative(v_wsDir_2045_, v___y_2152_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2154_);
v___x_2157_ = l_Lake_resolvePath(v_pkgDir_2154_);
v___x_2158_ = lean_string_utf8_byte_size(v___x_2157_);
v___x_2159_ = lean_nat_dec_eq(v___x_2158_, v___x_2155_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
v___y_2129_ = v___y_2152_;
v___y_2130_ = v___x_2153_;
v___y_2131_ = v_pkgDir_2154_;
v___y_2132_ = v___x_2155_;
v___y_2133_ = v___x_2156_;
v_val_2134_ = v___x_2160_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2161_; 
lean_dec_ref(v___x_2157_);
v___x_2161_ = lean_box(0);
v___y_2129_ = v___y_2152_;
v___y_2130_ = v___x_2153_;
v___y_2131_ = v_pkgDir_2154_;
v___y_2132_ = v___x_2155_;
v___y_2133_ = v___x_2156_;
v_val_2134_ = v___x_2161_;
goto v___jp_2128_;
}
}
v___jp_2162_:
{
if (lean_obj_tag(v_subDir_x3f_2051_) == 1)
{
lean_object* v_val_2165_; lean_object* v___x_2166_; 
v_val_2165_ = lean_ctor_get(v_subDir_x3f_2051_, 0);
lean_inc(v_val_2165_);
v___x_2166_ = l_Lake_joinRelative(v_relPkgDir_2047_, v_val_2165_);
v___y_2150_ = v_a_2164_;
v___y_2151_ = v___y_2163_;
v___y_2152_ = v___x_2166_;
goto v___jp_2149_;
}
else
{
v___y_2150_ = v_a_2164_;
v___y_2151_ = v___y_2163_;
v___y_2152_ = v_relPkgDir_2047_;
goto v___jp_2149_;
}
}
v___jp_2168_:
{
lean_object* v___x_2170_; 
lean_inc(v_inputRev_x3f_2050_);
lean_inc_ref(v___y_2169_);
lean_inc_ref(v_gitDir_2167_);
lean_inc_ref(v_name_2046_);
v___x_2170_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2052_, v_name_2046_, v_gitDir_2167_, v___y_2169_, v_inputRev_x3f_2050_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2220_; 
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2170_, 0);
lean_dec(v_unused_2221_);
v___x_2172_ = v___x_2170_;
v_isShared_2173_ = v_isSharedCheck_2220_;
goto v_resetjp_2171_;
}
else
{
lean_dec(v___x_2170_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2220_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2176_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2167_, v___x_2175_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v_a_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
lean_del_object(v___x_2172_);
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
v_a_2178_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2176_, 2);
v___x_2179_ = lean_array_get_size(v_a_2178_);
v___x_2180_ = lean_nat_dec_lt(v___x_2174_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec(v_a_2178_);
v___y_2163_ = v___y_2169_;
v_a_2164_ = v_a_2177_;
goto v___jp_2162_;
}
else
{
lean_object* v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2181_ = lean_box(0);
v___x_2182_ = ((size_t)0ULL);
v___x_2183_ = lean_usize_of_nat(v___x_2179_);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2178_, v___x_2182_, v___x_2183_, v___x_2181_, v_a_2052_);
lean_dec(v_a_2178_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_dec_ref_known(v___x_2184_, 1);
v___y_2163_ = v___y_2169_;
v_a_2164_ = v_a_2177_;
goto v___jp_2162_;
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2177_);
lean_dec_ref(v___y_2169_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_scope_2056_);
lean_dec(v_name_2055_);
lean_dec(v_subDir_x3f_2051_);
lean_dec(v_inputRev_x3f_2050_);
lean_dec_ref(v_remoteUrl_2049_);
lean_dec_ref(v_relPkgDir_2047_);
lean_dec_ref(v_name_2046_);
lean_dec_ref(v_wsDir_2045_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
lean_dec_ref(v___y_2169_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_scope_2056_);
lean_dec(v_name_2055_);
lean_dec(v_subDir_x3f_2051_);
lean_dec(v_inputRev_x3f_2050_);
lean_dec_ref(v_remoteUrl_2049_);
lean_dec_ref(v_relPkgDir_2047_);
lean_dec_ref(v_name_2046_);
lean_dec_ref(v_wsDir_2045_);
v_a_2193_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2176_, 2);
v___x_2194_ = lean_array_get_size(v_a_2193_);
v___x_2195_ = lean_nat_dec_lt(v___x_2174_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
lean_dec(v_a_2193_);
v___x_2196_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 1);
lean_ctor_set(v___x_2172_, 0, v___x_2196_);
v___x_2198_ = v___x_2172_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
else
{
lean_object* v___x_2200_; size_t v___x_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
lean_del_object(v___x_2172_);
v___x_2200_ = lean_box(0);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = lean_usize_of_nat(v___x_2194_);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2193_, v___x_2201_, v___x_2202_, v___x_2200_, v_a_2052_);
lean_dec(v_a_2193_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2211_);
v___x_2205_ = v___x_2203_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2203_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set_tag(v___x_2205_, 1);
lean_ctor_set(v___x_2205_, 0, v___x_2200_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2200_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2212_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2203_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2203_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v___y_2169_);
lean_dec_ref(v_gitDir_2167_);
lean_del_object(v___x_2058_);
lean_dec_ref(v_scope_2056_);
lean_dec(v_name_2055_);
lean_dec(v_subDir_x3f_2051_);
lean_dec(v_inputRev_x3f_2050_);
lean_dec_ref(v_remoteUrl_2049_);
lean_dec_ref(v_relPkgDir_2047_);
lean_dec_ref(v_name_2046_);
lean_dec_ref(v_wsDir_2045_);
v_a_2222_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2170_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2170_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
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
return v___x_2227_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_2236_, lean_object* v_inherited_2237_, lean_object* v_lakeEnv_2238_, lean_object* v_wsDir_2239_, lean_object* v_name_2240_, lean_object* v_relPkgDir_2241_, lean_object* v_gitUrl_2242_, lean_object* v_remoteUrl_2243_, lean_object* v_inputRev_x3f_2244_, lean_object* v_subDir_x3f_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
uint8_t v_inherited_boxed_2248_; lean_object* v_res_2249_; 
v_inherited_boxed_2248_ = lean_unbox(v_inherited_2237_);
v_res_2249_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_2236_, v_inherited_boxed_2248_, v_lakeEnv_2238_, v_wsDir_2239_, v_name_2240_, v_relPkgDir_2241_, v_gitUrl_2242_, v_remoteUrl_2243_, v_inputRev_x3f_2244_, v_subDir_x3f_2245_, v_a_2246_);
lean_dec_ref(v_a_2246_);
lean_dec_ref(v_lakeEnv_2238_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_2250_, lean_object* v_dep_2251_, uint8_t v_inherited_2252_, lean_object* v_lakeEnv_2253_, lean_object* v_wsDir_2254_, lean_object* v_name_2255_, lean_object* v_relPkgDir_2256_, lean_object* v_gitUrl_2257_, lean_object* v_remoteUrl_2258_, lean_object* v_inputRev_x3f_2259_, lean_object* v_subDir_x3f_2260_){
_start:
{
lean_object* v_pkgUrlMap_2262_; lean_object* v_name_2263_; lean_object* v_scope_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2440_; 
v_pkgUrlMap_2262_ = lean_ctor_get(v_lakeEnv_2253_, 5);
v_name_2263_ = lean_ctor_get(v_dep_2251_, 0);
v_scope_2264_ = lean_ctor_get(v_dep_2251_, 1);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_dep_2251_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; lean_object* v_unused_2442_; lean_object* v_unused_2443_; 
v_unused_2441_ = lean_ctor_get(v_dep_2251_, 4);
lean_dec(v_unused_2441_);
v_unused_2442_ = lean_ctor_get(v_dep_2251_, 3);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_dep_2251_, 2);
lean_dec(v_unused_2443_);
v___x_2266_ = v_dep_2251_;
v_isShared_2267_ = v_isSharedCheck_2440_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_scope_2264_);
lean_inc(v_name_2263_);
lean_dec(v_dep_2251_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2440_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v_a_2272_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v_val_2286_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v_a_2305_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v_val_2342_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2371_; lean_object* v_a_2372_; lean_object* v_gitDir_2375_; lean_object* v___y_2377_; lean_object* v___x_2438_; 
lean_inc_ref(v_relPkgDir_2256_);
lean_inc_ref(v_wsDir_2254_);
v_gitDir_2375_ = l_Lake_joinRelative(v_wsDir_2254_, v_relPkgDir_2256_);
v___x_2438_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2262_, v_name_2263_);
if (lean_obj_tag(v___x_2438_) == 0)
{
v___y_2377_ = v_gitUrl_2257_;
goto v___jp_2376_;
}
else
{
lean_object* v_val_2439_; 
lean_dec_ref(v_gitUrl_2257_);
v_val_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_val_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___y_2377_ = v_val_2439_;
goto v___jp_2376_;
}
v___jp_2268_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2273_ = l_Lake_defaultConfigFile;
v___x_2274_ = lean_box(0);
v___x_2275_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2275_, 0, v_name_2263_);
lean_ctor_set(v___x_2275_, 1, v_scope_2264_);
lean_ctor_set(v___x_2275_, 2, v___x_2273_);
lean_ctor_set(v___x_2275_, 3, v___x_2274_);
lean_ctor_set(v___x_2275_, 4, v___y_2270_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*5, v_inherited_2252_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v___x_2275_);
lean_ctor_set(v___x_2266_, 3, v_a_2272_);
lean_ctor_set(v___x_2266_, 2, v_remoteUrl_2258_);
lean_ctor_set(v___x_2266_, 1, v___y_2269_);
lean_ctor_set(v___x_2266_, 0, v___y_2271_);
v___x_2277_ = v___x_2266_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___y_2271_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___y_2269_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_remoteUrl_2258_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_a_2272_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
v___jp_2280_:
{
lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = lean_array_get_size(v___y_2281_);
v___x_2288_ = lean_nat_dec_lt(v___y_2285_, v___x_2287_);
if (v___x_2288_ == 0)
{
v___y_2269_ = v___y_2282_;
v___y_2270_ = v___y_2283_;
v___y_2271_ = v___y_2284_;
v_a_2272_ = v_val_2286_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2289_; size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = lean_usize_of_nat(v___x_2287_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2281_, v___x_2290_, v___x_2291_, v___x_2289_, v_a_2250_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_dec_ref_known(v___x_2292_, 1);
v___y_2269_ = v___y_2282_;
v___y_2270_ = v___y_2283_;
v___y_2271_ = v___y_2284_;
v_a_2272_ = v_val_2286_;
goto v___jp_2268_;
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_val_2286_);
lean_dec_ref(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_del_object(v___x_2266_);
lean_dec_ref(v_scope_2264_);
lean_dec(v_name_2263_);
lean_dec_ref(v_remoteUrl_2258_);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
v___jp_2301_:
{
if (lean_obj_tag(v_a_2305_) == 1)
{
lean_object* v_val_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec_ref(v___y_2302_);
lean_dec_ref(v_name_2255_);
v_val_2306_ = lean_ctor_get(v_a_2305_, 0);
lean_inc_n(v_val_2306_, 2);
lean_dec_ref_known(v_a_2305_, 1);
v___x_2307_ = l_Lake_defaultManifestFile;
v___x_2308_ = l_Lake_joinRelative(v_val_2306_, v___x_2307_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2311_ = l_Lake_Manifest_load(v___x_2308_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set_tag(v___x_2314_, 1);
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
v___y_2281_ = v___x_2310_;
v___y_2282_ = v___y_2303_;
v___y_2283_ = v___y_2304_;
v___y_2284_ = v_val_2306_;
v___y_2285_ = v___x_2309_;
v_val_2286_ = v___x_2317_;
goto v___jp_2280_;
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
v_a_2320_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2311_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2311_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set_tag(v___x_2322_, 0);
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
v___y_2281_ = v___x_2310_;
v___y_2282_ = v___y_2303_;
v___y_2283_ = v___y_2304_;
v___y_2284_ = v_val_2306_;
v___y_2285_ = v___x_2309_;
v_val_2286_ = v___x_2325_;
goto v___jp_2280_;
}
}
}
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec(v_a_2305_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_del_object(v___x_2266_);
lean_dec_ref(v_scope_2264_);
lean_dec(v_name_2263_);
lean_dec_ref(v_remoteUrl_2258_);
v___x_2328_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2329_ = lean_string_append(v_name_2255_, v___x_2328_);
v___x_2330_ = lean_string_append(v___x_2329_, v___y_2302_);
lean_dec_ref(v___y_2302_);
v___x_2331_ = 3;
v___x_2332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*1, v___x_2331_);
lean_inc_ref(v_a_2250_);
v___x_2333_ = lean_apply_2(v_a_2250_, v___x_2332_, lean_box(0));
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
}
v___jp_2336_:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_array_get_size(v___y_2340_);
v___x_2344_ = lean_nat_dec_lt(v___y_2341_, v___x_2343_);
if (v___x_2344_ == 0)
{
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2338_;
v___y_2304_ = v___y_2339_;
v_a_2305_ = v_val_2342_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2345_ = lean_box(0);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = lean_usize_of_nat(v___x_2343_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2340_, v___x_2346_, v___x_2347_, v___x_2345_, v_a_2250_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_dec_ref_known(v___x_2348_, 1);
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2338_;
v___y_2304_ = v___y_2339_;
v_a_2305_ = v_val_2342_;
goto v___jp_2301_;
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_val_2342_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_del_object(v___x_2266_);
lean_dec_ref(v_scope_2264_);
lean_dec(v_name_2263_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_name_2255_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
v___jp_2357_:
{
lean_object* v___x_2361_; lean_object* v_pkgDir_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2361_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2361_, 0, v___y_2358_);
lean_ctor_set(v___x_2361_, 1, v___y_2359_);
lean_ctor_set(v___x_2361_, 2, v_inputRev_x3f_2259_);
lean_ctor_set(v___x_2361_, 3, v_subDir_x3f_2260_);
lean_inc_ref(v___y_2360_);
v_pkgDir_2362_ = l_Lake_joinRelative(v_wsDir_2254_, v___y_2360_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2362_);
v___x_2365_ = l_Lake_resolvePath(v_pkgDir_2362_);
v___x_2366_ = lean_string_utf8_byte_size(v___x_2365_);
v___x_2367_ = lean_nat_dec_eq(v___x_2366_, v___x_2363_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2365_);
v___y_2337_ = v_pkgDir_2362_;
v___y_2338_ = v___y_2360_;
v___y_2339_ = v___x_2361_;
v___y_2340_ = v___x_2364_;
v___y_2341_ = v___x_2363_;
v_val_2342_ = v___x_2368_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2369_; 
lean_dec_ref(v___x_2365_);
v___x_2369_ = lean_box(0);
v___y_2337_ = v_pkgDir_2362_;
v___y_2338_ = v___y_2360_;
v___y_2339_ = v___x_2361_;
v___y_2340_ = v___x_2364_;
v___y_2341_ = v___x_2363_;
v_val_2342_ = v___x_2369_;
goto v___jp_2336_;
}
}
v___jp_2370_:
{
if (lean_obj_tag(v_subDir_x3f_2260_) == 1)
{
lean_object* v_val_2373_; lean_object* v___x_2374_; 
v_val_2373_ = lean_ctor_get(v_subDir_x3f_2260_, 0);
lean_inc(v_val_2373_);
v___x_2374_ = l_Lake_joinRelative(v_relPkgDir_2256_, v_val_2373_);
v___y_2358_ = v___y_2371_;
v___y_2359_ = v_a_2372_;
v___y_2360_ = v___x_2374_;
goto v___jp_2357_;
}
else
{
v___y_2358_ = v___y_2371_;
v___y_2359_ = v_a_2372_;
v___y_2360_ = v_relPkgDir_2256_;
goto v___jp_2357_;
}
}
v___jp_2376_:
{
lean_object* v___x_2378_; 
lean_inc(v_inputRev_x3f_2259_);
lean_inc_ref(v___y_2377_);
lean_inc_ref(v_gitDir_2375_);
lean_inc_ref(v_name_2255_);
v___x_2378_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2250_, v_name_2255_, v_gitDir_2375_, v___y_2377_, v_inputRev_x3f_2259_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2428_; 
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; 
v_unused_2429_ = lean_ctor_get(v___x_2378_, 0);
lean_dec(v_unused_2429_);
v___x_2380_ = v___x_2378_;
v_isShared_2381_ = v_isSharedCheck_2428_;
goto v_resetjp_2379_;
}
else
{
lean_dec(v___x_2378_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2428_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2384_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2375_, v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v_a_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
lean_del_object(v___x_2380_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
v_a_2386_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2384_, 2);
v___x_2387_ = lean_array_get_size(v_a_2386_);
v___x_2388_ = lean_nat_dec_lt(v___x_2382_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_dec(v_a_2386_);
v___y_2371_ = v___y_2377_;
v_a_2372_ = v_a_2385_;
goto v___jp_2370_;
}
else
{
lean_object* v___x_2389_; size_t v___x_2390_; size_t v___x_2391_; lean_object* v___x_2392_; 
v___x_2389_ = lean_box(0);
v___x_2390_ = ((size_t)0ULL);
v___x_2391_ = lean_usize_of_nat(v___x_2387_);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2386_, v___x_2390_, v___x_2391_, v___x_2389_, v_a_2250_);
lean_dec(v_a_2386_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_dec_ref_known(v___x_2392_, 1);
v___y_2371_ = v___y_2377_;
v_a_2372_ = v_a_2385_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_a_2385_);
lean_dec_ref(v___y_2377_);
lean_del_object(v___x_2266_);
lean_dec_ref(v_scope_2264_);
lean_dec(v_name_2263_);
lean_dec(v_subDir_x3f_2260_);
lean_dec(v_inputRev_x3f_2259_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2256_);
lean_dec_ref(v_name_2255_);
lean_dec_ref(v_wsDir_2254_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
lean_dec_ref(v___y_2377_);
lean_del_object(v___x_2266_);
lean_dec_ref(v_scope_2264_);
lean_dec(v_name_2263_);
lean_dec(v_subDir_x3f_2260_);
lean_dec(v_inputRev_x3f_2259_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2256_);
lean_dec_ref(v_name_2255_);
lean_dec_ref(v_wsDir_2254_);
v_a_2401_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2384_, 2);
v___x_2402_ = lean_array_get_size(v_a_2401_);
v___x_2403_ = lean_nat_dec_lt(v___x_2382_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_dec(v_a_2401_);
v___x_2404_ = lean_box(0);
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 1);
lean_ctor_set(v___x_2380_, 0, v___x_2404_);
v___x_2406_ = v___x_2380_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
else
{
lean_object* v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; lean_object* v___x_2411_; 
lean_del_object(v___x_2380_);
v___x_2408_ = lean_box(0);
v___x_2409_ = ((size_t)0ULL);
v___x_2410_ = lean_usize_of_nat(v___x_2402_);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2401_, v___x_2409_, v___x_2410_, v___x_2408_, v_a_2250_);
lean_dec(v_a_2401_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; 
v_unused_2419_ = lean_ctor_get(v___x_2411_, 0);
lean_dec(v_unused_2419_);
v___x_2413_ = v___x_2411_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_dec(v___x_2411_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 1);
lean_ctor_set(v___x_2413_, 0, v___x_2408_);
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2408_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
v_a_2420_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2411_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2411_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v___y_2377_);
lean_dec_ref(v_gitDir_2375_);
lean_del_object(v___x_2266_);
lean_dec_ref(v_scope_2264_);
lean_dec(v_name_2263_);
lean_dec(v_subDir_x3f_2260_);
lean_dec(v_inputRev_x3f_2259_);
lean_dec_ref(v_remoteUrl_2258_);
lean_dec_ref(v_relPkgDir_2256_);
lean_dec_ref(v_name_2255_);
lean_dec_ref(v_wsDir_2254_);
v_a_2430_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2378_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2378_);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_2444_, lean_object* v_dep_2445_, lean_object* v_inherited_2446_, lean_object* v_lakeEnv_2447_, lean_object* v_wsDir_2448_, lean_object* v_name_2449_, lean_object* v_relPkgDir_2450_, lean_object* v_gitUrl_2451_, lean_object* v_remoteUrl_2452_, lean_object* v_inputRev_x3f_2453_, lean_object* v_subDir_x3f_2454_, lean_object* v_a_2455_){
_start:
{
uint8_t v_inherited_boxed_2456_; lean_object* v_res_2457_; 
v_inherited_boxed_2456_ = lean_unbox(v_inherited_2446_);
v_res_2457_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2444_, v_dep_2445_, v_inherited_boxed_2456_, v_lakeEnv_2447_, v_wsDir_2448_, v_name_2449_, v_relPkgDir_2450_, v_gitUrl_2451_, v_remoteUrl_2452_, v_inputRev_x3f_2453_, v_subDir_x3f_2454_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_a_2444_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_2461_, lean_object* v_as_2462_, size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_b_2465_){
_start:
{
uint8_t v___x_2466_; 
v___x_2466_ = lean_usize_dec_lt(v_i_2464_, v_sz_2463_);
if (v___x_2466_ == 0)
{
lean_inc_ref(v_b_2465_);
return v_b_2465_;
}
else
{
lean_object* v_a_2467_; lean_object* v_version_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_a_2467_ = lean_array_uget_borrowed(v_as_2462_, v_i_2464_);
v_version_2468_ = lean_ctor_get(v_a_2467_, 0);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Lake_VerRange_test(v_ver_2461_, v_version_2468_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; size_t v___x_2472_; size_t v___x_2473_; 
v___x_2471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_2472_ = ((size_t)1ULL);
v___x_2473_ = lean_usize_add(v_i_2464_, v___x_2472_);
v_i_2464_ = v___x_2473_;
v_b_2465_ = v___x_2471_;
goto _start;
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_inc(v_a_2467_);
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2467_);
v___x_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
lean_ctor_set(v___x_2477_, 1, v___x_2469_);
return v___x_2477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_2478_, lean_object* v_as_2479_, lean_object* v_sz_2480_, lean_object* v_i_2481_, lean_object* v_b_2482_){
_start:
{
size_t v_sz_boxed_2483_; size_t v_i_boxed_2484_; lean_object* v_res_2485_; 
v_sz_boxed_2483_ = lean_unbox_usize(v_sz_2480_);
lean_dec(v_sz_2480_);
v_i_boxed_2484_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_res_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_2478_, v_as_2479_, v_sz_boxed_2483_, v_i_boxed_2484_, v_b_2482_);
lean_dec_ref(v_b_2482_);
lean_dec_ref(v_as_2479_);
lean_dec_ref(v_ver_2478_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_2495_, uint8_t v_inherited_2496_, lean_object* v_lakeEnv_2497_, lean_object* v_wsDir_2498_, lean_object* v_relPkgsDir_2499_, lean_object* v_relParentDir_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v_a_2529_; lean_object* v_a_2533_; lean_object* v_name_2540_; lean_object* v_scope_2541_; lean_object* v_version_2542_; lean_object* v_src_x3f_2543_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v_a_2549_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v_val_2562_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v_a_2583_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v_val_2622_; 
v_name_2540_ = lean_ctor_get(v_dep_2495_, 0);
v_scope_2541_ = lean_ctor_get(v_dep_2495_, 1);
v_version_2542_ = lean_ctor_get(v_dep_2495_, 2);
v_src_x3f_2543_ = lean_ctor_get(v_dep_2495_, 3);
lean_inc(v_src_x3f_2543_);
if (lean_obj_tag(v_src_x3f_2543_) == 1)
{
lean_object* v_val_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2687_; 
v_val_2637_ = lean_ctor_get(v_src_x3f_2543_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_src_x3f_2543_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2639_ = v_src_x3f_2543_;
v_isShared_2640_ = v_isSharedCheck_2687_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_val_2637_);
lean_dec(v_src_x3f_2543_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2687_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
if (lean_obj_tag(v_val_2637_) == 0)
{
lean_object* v_dir_2641_; uint8_t v_copy_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2674_; 
lean_inc_ref(v_scope_2541_);
lean_inc(v_name_2540_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v_dir_2641_ = lean_ctor_get(v_val_2637_, 0);
v_copy_2642_ = lean_ctor_get_uint8(v_val_2637_, sizeof(void*)*1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_val_2637_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2644_ = v_val_2637_;
v_isShared_2645_ = v_isSharedCheck_2674_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_dir_2641_);
lean_dec(v_val_2637_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2674_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_relSrc_2646_; lean_object* v_a_2648_; 
v_relSrc_2646_ = l_Lake_joinRelative(v_relParentDir_2500_, v_dir_2641_);
if (v_copy_2642_ == 0)
{
lean_dec_ref(v_relPkgsDir_2499_);
lean_inc_ref(v_relSrc_2646_);
v_a_2648_ = v_relSrc_2646_;
goto v___jp_2647_;
}
else
{
uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v_relDst_2667_; lean_object* v_dst_2668_; lean_object* v___x_2669_; 
v___x_2665_ = 0;
lean_inc(v_name_2540_);
v___x_2666_ = l_Lean_Name_toString(v_name_2540_, v___x_2665_);
v_relDst_2667_ = l_Lake_joinRelative(v_relPkgsDir_2499_, v___x_2666_);
lean_inc_ref(v_relDst_2667_);
lean_inc_ref(v_wsDir_2498_);
v_dst_2668_ = l_Lake_joinRelative(v_wsDir_2498_, v_relDst_2667_);
v___x_2669_ = l_Lake_removeDirAllIfExists(v_dst_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_src_2670_; lean_object* v___x_2671_; 
lean_dec_ref_known(v___x_2669_, 1);
lean_inc_ref(v_relSrc_2646_);
lean_inc_ref(v_wsDir_2498_);
v_src_2670_ = l_Lake_joinRelative(v_wsDir_2498_, v_relSrc_2646_);
v___x_2671_ = l_Lake_copyDirAll(v_src_2670_, v_dst_2668_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_dec_ref_known(v___x_2671_, 1);
v_a_2648_ = v_relDst_2667_;
goto v___jp_2647_;
}
else
{
lean_object* v_a_2672_; 
lean_dec_ref(v_relDst_2667_);
lean_dec_ref(v_relSrc_2646_);
lean_del_object(v___x_2644_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_scope_2541_);
lean_dec(v_name_2540_);
lean_dec_ref(v_wsDir_2498_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v_a_2533_ = v_a_2672_;
goto v___jp_2532_;
}
}
else
{
lean_object* v_a_2673_; 
lean_dec_ref(v_dst_2668_);
lean_dec_ref(v_relDst_2667_);
lean_dec_ref(v_relSrc_2646_);
lean_del_object(v___x_2644_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_scope_2541_);
lean_dec(v_name_2540_);
lean_dec_ref(v_wsDir_2498_);
v_a_2673_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2669_, 1);
v_a_2533_ = v_a_2673_;
goto v___jp_2532_;
}
}
v___jp_2647_:
{
uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2649_ = 0;
lean_inc(v_name_2540_);
v___x_2650_ = l_Lean_Name_toString(v_name_2540_, v___x_2649_);
v___x_2651_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_relSrc_2646_);
v___x_2653_ = v___x_2644_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_relSrc_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2664_, sizeof(void*)*1, v_copy_2642_);
v___x_2653_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v_pkgDir_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
lean_inc_ref(v_a_2648_);
v_pkgDir_2654_ = l_Lake_joinRelative(v_wsDir_2498_, v_a_2648_);
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2654_);
v___x_2657_ = l_Lake_resolvePath(v_pkgDir_2654_);
v___x_2658_ = lean_string_utf8_byte_size(v___x_2657_);
v___x_2659_ = lean_nat_dec_eq(v___x_2658_, v___x_2655_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2661_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2657_);
v___x_2661_ = v___x_2639_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2657_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v___y_2615_ = v_pkgDir_2654_;
v___y_2616_ = v___x_2651_;
v___y_2617_ = v_a_2648_;
v___y_2618_ = v___x_2656_;
v___y_2619_ = v___x_2655_;
v___y_2620_ = v___x_2653_;
v___y_2621_ = v___x_2650_;
v_val_2622_ = v___x_2661_;
goto v___jp_2614_;
}
}
else
{
lean_object* v___x_2663_; 
lean_dec_ref(v___x_2657_);
lean_del_object(v___x_2639_);
v___x_2663_ = lean_box(0);
v___y_2615_ = v_pkgDir_2654_;
v___y_2616_ = v___x_2651_;
v___y_2617_ = v_a_2648_;
v___y_2618_ = v___x_2656_;
v___y_2619_ = v___x_2655_;
v___y_2620_ = v___x_2653_;
v___y_2621_ = v___x_2650_;
v_val_2622_ = v___x_2663_;
goto v___jp_2614_;
}
}
}
}
}
else
{
lean_object* v_url_2675_; lean_object* v_rev_2676_; lean_object* v_subDir_2677_; lean_object* v___y_2679_; lean_object* v___x_2684_; 
lean_del_object(v___x_2639_);
lean_dec_ref(v_relParentDir_2500_);
v_url_2675_ = lean_ctor_get(v_val_2637_, 0);
lean_inc_ref_n(v_url_2675_, 2);
v_rev_2676_ = lean_ctor_get(v_val_2637_, 1);
lean_inc(v_rev_2676_);
v_subDir_2677_ = lean_ctor_get(v_val_2637_, 2);
lean_inc(v_subDir_2677_);
lean_dec_ref_known(v_val_2637_, 3);
v___x_2684_ = l_Lake_Git_filterUrl_x3f(v_url_2675_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2685_; 
v___x_2685_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2679_ = v___x_2685_;
goto v___jp_2678_;
}
else
{
lean_object* v_val_2686_; 
v_val_2686_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_val_2686_);
lean_dec_ref_known(v___x_2684_, 1);
v___y_2679_ = v_val_2686_;
goto v___jp_2678_;
}
v___jp_2678_:
{
uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2680_ = 0;
lean_inc(v_name_2540_);
v___x_2681_ = l_Lean_Name_toString(v_name_2540_, v___x_2680_);
lean_inc_ref(v___x_2681_);
v___x_2682_ = l_Lake_joinRelative(v_relPkgsDir_2499_, v___x_2681_);
v___x_2683_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2501_, v_dep_2495_, v_inherited_2496_, v_lakeEnv_2497_, v_wsDir_2498_, v___x_2681_, v___x_2682_, v_url_2675_, v___y_2679_, v_rev_2676_, v_subDir_2677_);
lean_dec_ref(v_lakeEnv_2497_);
return v___x_2683_;
}
}
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
lean_dec(v_src_x3f_2543_);
lean_dec_ref(v_relParentDir_2500_);
v___x_2688_ = lean_string_utf8_byte_size(v_scope_2541_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_nat_dec_eq(v___x_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___y_2693_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v_a_2715_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v_fst_2765_; lean_object* v_snd_2766_; lean_object* v_a_2782_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v_fst_2889_; lean_object* v_snd_2890_; 
lean_inc(v_name_2540_);
v___x_2691_ = l_Lean_Name_toString(v_name_2540_, v___x_2690_);
v___x_2886_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2541_);
lean_inc_ref(v_lakeEnv_2497_);
v___x_2887_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_2497_, v_scope_2541_, v___x_2691_, v___x_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2905_; lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2905_);
v_a_2906_ = lean_ctor_get(v___x_2887_, 1);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2887_, 2);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_a_2905_);
v_fst_2889_ = v___x_2907_;
v_snd_2890_ = v_a_2906_;
goto v___jp_2888_;
}
else
{
lean_object* v_a_2908_; lean_object* v_a_2909_; lean_object* v___x_2910_; 
v_a_2908_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2908_);
v_a_2909_ = lean_ctor_get(v___x_2887_, 1);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2887_, 2);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_a_2908_);
v_fst_2889_ = v___x_2910_;
v_snd_2890_ = v_a_2909_;
goto v___jp_2888_;
}
v___jp_2692_:
{
lean_object* v_toString_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_toString_2694_ = lean_ctor_get(v___y_2693_, 0);
lean_inc_ref(v_toString_2694_);
lean_dec_ref(v___y_2693_);
v___x_2695_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2696_ = lean_string_append(v_scope_2541_, v___x_2695_);
v___x_2697_ = lean_string_append(v___x_2696_, v___x_2691_);
lean_dec_ref(v___x_2691_);
v___x_2698_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_2699_ = lean_string_append(v___x_2697_, v___x_2698_);
v___x_2700_ = lean_string_append(v___x_2699_, v_toString_2694_);
lean_dec_ref(v_toString_2694_);
v___x_2701_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_2702_ = lean_string_append(v___x_2700_, v___x_2701_);
v___x_2703_ = 3;
v___x_2704_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*1, v___x_2703_);
lean_inc_ref(v_a_2501_);
v___x_2705_ = lean_apply_2(v_a_2501_, v___x_2704_, lean_box(0));
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
v___jp_2708_:
{
if (lean_obj_tag(v_a_2715_) == 0)
{
lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2731_; 
lean_inc_ref(v_scope_2541_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_a_2715_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v_a_2715_, 0);
lean_dec(v_unused_2732_);
v___x_2717_ = v_a_2715_;
v_isShared_2718_ = v_isSharedCheck_2731_;
goto v_resetjp_2716_;
}
else
{
lean_dec(v_a_2715_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2731_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2719_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2720_ = lean_string_append(v_scope_2541_, v___x_2719_);
v___x_2721_ = lean_string_append(v___x_2720_, v___x_2691_);
lean_dec_ref(v___x_2691_);
v___x_2722_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_2723_ = lean_string_append(v___x_2721_, v___x_2722_);
v___x_2724_ = 3;
v___x_2725_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*1, v___x_2724_);
lean_inc_ref(v_a_2501_);
v___x_2726_ = lean_apply_2(v_a_2501_, v___x_2725_, lean_box(0));
v___x_2727_ = lean_box(0);
if (v_isShared_2718_ == 0)
{
lean_ctor_set_tag(v___x_2717_, 1);
lean_ctor_set(v___x_2717_, 0, v___x_2727_);
v___x_2729_ = v___x_2717_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2734_; size_t v_sz_2735_; size_t v___x_2736_; lean_object* v___x_2737_; lean_object* v_fst_2738_; 
v_a_2733_ = lean_ctor_get(v_a_2715_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v_a_2715_, 1);
v___x_2734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_2735_ = lean_array_size(v_a_2733_);
v___x_2736_ = ((size_t)0ULL);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_2714_, v_a_2733_, v_sz_2735_, v___x_2736_, v___x_2734_);
lean_dec(v_a_2733_);
v_fst_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_fst_2738_);
lean_dec_ref(v___x_2737_);
if (lean_obj_tag(v_fst_2738_) == 0)
{
lean_inc_ref(v_scope_2541_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v___y_2693_ = v___y_2714_;
goto v___jp_2692_;
}
else
{
lean_object* v_val_2739_; 
v_val_2739_ = lean_ctor_get(v_fst_2738_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v_fst_2738_, 1);
if (lean_obj_tag(v_val_2739_) == 1)
{
lean_object* v_val_2740_; lean_object* v_version_2741_; lean_object* v_revision_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_dec_ref(v___y_2714_);
v_val_2740_ = lean_ctor_get(v_val_2739_, 0);
lean_inc(v_val_2740_);
lean_dec_ref_known(v_val_2739_, 1);
v_version_2741_ = lean_ctor_get(v_val_2740_, 0);
lean_inc_ref(v_version_2741_);
v_revision_2742_ = lean_ctor_get(v_val_2740_, 1);
lean_inc_ref(v_revision_2742_);
lean_dec(v_val_2740_);
v___x_2743_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_2541_);
v___x_2744_ = lean_string_append(v_scope_2541_, v___x_2743_);
v___x_2745_ = lean_string_append(v___x_2744_, v___x_2691_);
lean_dec_ref(v___x_2691_);
v___x_2746_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_2747_ = lean_string_append(v___x_2745_, v___x_2746_);
v___x_2748_ = l_Lake_StdVer_toString(v_version_2741_);
v___x_2749_ = lean_string_append(v___x_2747_, v___x_2748_);
lean_dec_ref(v___x_2748_);
v___x_2750_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_2751_ = lean_string_append(v___x_2749_, v___x_2750_);
v___x_2752_ = lean_string_append(v___x_2751_, v_revision_2742_);
v___x_2753_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_2754_ = lean_string_append(v___x_2752_, v___x_2753_);
v___x_2755_ = 1;
v___x_2756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set_uint8(v___x_2756_, sizeof(void*)*1, v___x_2755_);
lean_inc_ref(v_a_2501_);
v___x_2757_ = lean_apply_2(v_a_2501_, v___x_2756_, lean_box(0));
v___y_2524_ = v___y_2709_;
v___y_2525_ = v___y_2710_;
v___y_2526_ = v___y_2711_;
v___y_2527_ = v___y_2713_;
v___y_2528_ = v___y_2712_;
v_a_2529_ = v_revision_2742_;
goto v___jp_2523_;
}
else
{
lean_inc_ref(v_scope_2541_);
lean_dec(v_val_2739_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v___y_2693_ = v___y_2714_;
goto v___jp_2692_;
}
}
}
}
v___jp_2758_:
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = lean_array_get_size(v_snd_2766_);
v___x_2768_ = lean_nat_dec_lt(v___x_2689_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec_ref(v_snd_2766_);
v___y_2709_ = v___y_2759_;
v___y_2710_ = v___y_2760_;
v___y_2711_ = v___y_2761_;
v___y_2712_ = v___y_2763_;
v___y_2713_ = v___y_2762_;
v___y_2714_ = v___y_2764_;
v_a_2715_ = v_fst_2765_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2769_; size_t v___x_2770_; size_t v___x_2771_; lean_object* v___x_2772_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = ((size_t)0ULL);
v___x_2771_ = lean_usize_of_nat(v___x_2767_);
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2766_, v___x_2770_, v___x_2771_, v___x_2769_, v_a_2501_);
lean_dec_ref(v_snd_2766_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_dec_ref_known(v___x_2772_, 1);
v___y_2709_ = v___y_2759_;
v___y_2710_ = v___y_2760_;
v___y_2711_ = v___y_2761_;
v___y_2712_ = v___y_2763_;
v___y_2713_ = v___y_2762_;
v___y_2714_ = v___y_2764_;
v_a_2715_ = v_fst_2765_;
goto v___jp_2708_;
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_fst_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
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
v___jp_2781_:
{
if (lean_obj_tag(v_a_2782_) == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_inc_ref(v_scope_2541_);
lean_dec_ref_known(v_a_2782_, 1);
lean_dec_ref(v_relPkgsDir_2499_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v___x_2783_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2784_ = lean_string_append(v_scope_2541_, v___x_2783_);
v___x_2785_ = lean_string_append(v___x_2784_, v___x_2691_);
lean_dec_ref(v___x_2691_);
v___x_2786_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2787_ = lean_string_append(v___x_2785_, v___x_2786_);
v___x_2788_ = 3;
v___x_2789_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*1, v___x_2788_);
lean_inc_ref(v_a_2501_);
v___x_2790_ = lean_apply_2(v_a_2501_, v___x_2789_, lean_box(0));
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
return v___x_2792_;
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2885_; 
v_a_2793_ = lean_ctor_get(v_a_2782_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2782_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2795_ = v_a_2782_;
v_isShared_2796_ = v_isSharedCheck_2885_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v_a_2782_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2885_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
if (lean_obj_tag(v_a_2793_) == 0)
{
lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2795_);
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_relPkgsDir_2499_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
v___x_2797_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_2495_);
v___x_2798_ = 3;
v___x_2799_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*1, v___x_2798_);
lean_inc_ref(v_a_2501_);
v___x_2800_ = lean_apply_2(v_a_2501_, v___x_2799_, lean_box(0));
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
else
{
lean_object* v_val_2803_; lean_object* v___x_2804_; 
v_val_2803_ = lean_ctor_get(v_a_2793_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v_a_2793_, 1);
v___x_2804_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2803_);
if (lean_obj_tag(v___x_2804_) == 1)
{
lean_object* v_val_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2884_; 
v_val_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2884_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_val_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2884_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
if (lean_obj_tag(v_val_2805_) == 0)
{
lean_object* v_url_2809_; lean_object* v_githubUrl_x3f_2810_; lean_object* v_defaultBranch_x3f_2811_; lean_object* v_subDir_x3f_2812_; lean_object* v_name_2813_; lean_object* v_fullName_2814_; lean_object* v___x_2815_; 
v_url_2809_ = lean_ctor_get(v_val_2805_, 1);
lean_inc_ref(v_url_2809_);
v_githubUrl_x3f_2810_ = lean_ctor_get(v_val_2805_, 2);
lean_inc(v_githubUrl_x3f_2810_);
v_defaultBranch_x3f_2811_ = lean_ctor_get(v_val_2805_, 3);
lean_inc(v_defaultBranch_x3f_2811_);
v_subDir_x3f_2812_ = lean_ctor_get(v_val_2805_, 4);
lean_inc(v_subDir_x3f_2812_);
lean_dec_ref_known(v_val_2805_, 5);
v_name_2813_ = lean_ctor_get(v_val_2803_, 0);
lean_inc_ref(v_name_2813_);
v_fullName_2814_ = lean_ctor_get(v_val_2803_, 1);
lean_inc_ref(v_fullName_2814_);
lean_dec(v_val_2803_);
v___x_2815_ = l_Lake_joinRelative(v_relPkgsDir_2499_, v_name_2813_);
switch(lean_obj_tag(v_version_2542_))
{
case 0:
{
lean_object* v___x_2816_; 
lean_del_object(v___x_2795_);
lean_dec_ref(v___x_2691_);
v___x_2816_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_2811_) == 0)
{
uint8_t v___x_2817_; 
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_fullName_2814_);
lean_dec(v_subDir_x3f_2812_);
lean_dec(v_githubUrl_x3f_2810_);
lean_dec_ref(v_url_2809_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v___x_2817_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2818_ = lean_box(0);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2818_);
v___x_2820_ = v___x_2807_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
else
{
lean_object* v___x_2822_; size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
lean_del_object(v___x_2807_);
v___x_2822_ = lean_box(0);
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2816_, v___x_2823_, v___x_2824_, v___x_2822_, v_a_2501_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2825_, 0);
lean_dec(v_unused_2833_);
v___x_2827_ = v___x_2825_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v___x_2825_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
lean_ctor_set_tag(v___x_2827_, 1);
lean_ctor_set(v___x_2827_, 0, v___x_2822_);
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2822_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_a_2834_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2825_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2825_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_object* v_val_2842_; uint8_t v___x_2843_; 
lean_del_object(v___x_2807_);
v_val_2842_ = lean_ctor_get(v_defaultBranch_x3f_2811_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v_defaultBranch_x3f_2811_, 1);
v___x_2843_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2843_ == 0)
{
v___y_2524_ = v_url_2809_;
v___y_2525_ = v___x_2815_;
v___y_2526_ = v_githubUrl_x3f_2810_;
v___y_2527_ = v_fullName_2814_;
v___y_2528_ = v_subDir_x3f_2812_;
v_a_2529_ = v_val_2842_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2844_; size_t v___x_2845_; size_t v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = lean_box(0);
v___x_2845_ = ((size_t)0ULL);
v___x_2846_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2816_, v___x_2845_, v___x_2846_, v___x_2844_, v_a_2501_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_dec_ref_known(v___x_2847_, 1);
v___y_2524_ = v_url_2809_;
v___y_2525_ = v___x_2815_;
v___y_2526_ = v_githubUrl_x3f_2810_;
v___y_2527_ = v_fullName_2814_;
v___y_2528_ = v_subDir_x3f_2812_;
v_a_2529_ = v_val_2842_;
goto v___jp_2523_;
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_val_2842_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_fullName_2814_);
lean_dec(v_subDir_x3f_2812_);
lean_dec(v_githubUrl_x3f_2810_);
lean_dec_ref(v_url_2809_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
lean_dec(v_defaultBranch_x3f_2811_);
lean_del_object(v___x_2807_);
lean_del_object(v___x_2795_);
lean_dec_ref(v___x_2691_);
v_rev_2856_ = lean_ctor_get(v_version_2542_, 0);
v___x_2857_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2858_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2858_ == 0)
{
lean_inc_ref(v_rev_2856_);
v___y_2524_ = v_url_2809_;
v___y_2525_ = v___x_2815_;
v___y_2526_ = v_githubUrl_x3f_2810_;
v___y_2527_ = v_fullName_2814_;
v___y_2528_ = v_subDir_x3f_2812_;
v_a_2529_ = v_rev_2856_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2859_; size_t v___x_2860_; size_t v___x_2861_; lean_object* v___x_2862_; 
v___x_2859_ = lean_box(0);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2857_, v___x_2860_, v___x_2861_, v___x_2859_, v_a_2501_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_dec_ref_known(v___x_2862_, 1);
lean_inc_ref(v_rev_2856_);
v___y_2524_ = v_url_2809_;
v___y_2525_ = v___x_2815_;
v___y_2526_ = v_githubUrl_x3f_2810_;
v___y_2527_ = v_fullName_2814_;
v___y_2528_ = v_subDir_x3f_2812_;
v_a_2529_ = v_rev_2856_;
goto v___jp_2523_;
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_fullName_2814_);
lean_dec(v_subDir_x3f_2812_);
lean_dec(v_githubUrl_x3f_2810_);
lean_dec_ref(v_url_2809_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
default: 
{
lean_object* v_ver_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec(v_defaultBranch_x3f_2811_);
lean_del_object(v___x_2807_);
v_ver_2871_ = lean_ctor_get(v_version_2542_, 0);
v___x_2872_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2541_);
lean_inc_ref(v_lakeEnv_2497_);
v___x_2873_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_2497_, v_scope_2541_, v___x_2691_, v___x_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_a_2875_; lean_object* v___x_2877_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
v_a_2875_ = lean_ctor_get(v___x_2873_, 1);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2873_, 2);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_a_2874_);
v___x_2877_ = v___x_2795_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2874_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_inc_ref(v_ver_2871_);
v___y_2759_ = v_url_2809_;
v___y_2760_ = v___x_2815_;
v___y_2761_ = v_githubUrl_x3f_2810_;
v___y_2762_ = v_fullName_2814_;
v___y_2763_ = v_subDir_x3f_2812_;
v___y_2764_ = v_ver_2871_;
v_fst_2765_ = v___x_2877_;
v_snd_2766_ = v_a_2875_;
goto v___jp_2758_;
}
}
else
{
lean_object* v_a_2879_; lean_object* v_a_2880_; lean_object* v___x_2882_; 
v_a_2879_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2879_);
v_a_2880_ = lean_ctor_get(v___x_2873_, 1);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2873_, 2);
if (v_isShared_2796_ == 0)
{
lean_ctor_set_tag(v___x_2795_, 0);
lean_ctor_set(v___x_2795_, 0, v_a_2879_);
v___x_2882_ = v___x_2795_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2879_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_inc_ref(v_ver_2871_);
v___y_2759_ = v_url_2809_;
v___y_2760_ = v___x_2815_;
v___y_2761_ = v_githubUrl_x3f_2810_;
v___y_2762_ = v_fullName_2814_;
v___y_2763_ = v_subDir_x3f_2812_;
v___y_2764_ = v_ver_2871_;
v_fst_2765_ = v___x_2882_;
v_snd_2766_ = v_a_2880_;
goto v___jp_2758_;
}
}
}
}
}
else
{
lean_del_object(v___x_2807_);
lean_dec(v_val_2805_);
lean_del_object(v___x_2795_);
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_relPkgsDir_2499_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v___y_2504_ = v_val_2803_;
v___y_2505_ = v_a_2501_;
goto v___jp_2503_;
}
}
}
else
{
lean_dec(v___x_2804_);
lean_del_object(v___x_2795_);
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_relPkgsDir_2499_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v___y_2504_ = v_val_2803_;
v___y_2505_ = v_a_2501_;
goto v___jp_2503_;
}
}
}
}
}
v___jp_2888_:
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = lean_array_get_size(v_snd_2890_);
v___x_2892_ = lean_nat_dec_lt(v___x_2689_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_dec_ref(v_snd_2890_);
v_a_2782_ = v_fst_2889_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v___x_2893_ = lean_box(0);
v___x_2894_ = ((size_t)0ULL);
v___x_2895_ = lean_usize_of_nat(v___x_2891_);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2890_, v___x_2894_, v___x_2895_, v___x_2893_, v_a_2501_);
lean_dec_ref(v_snd_2890_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_dec_ref_known(v___x_2896_, 1);
v_a_2782_ = v_fst_2889_;
goto v___jp_2781_;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v_fst_2889_);
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_relPkgsDir_2499_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
else
{
uint8_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_inc(v_name_2540_);
lean_dec_ref(v_relPkgsDir_2499_);
lean_dec_ref(v_wsDir_2498_);
lean_dec_ref(v_lakeEnv_2497_);
lean_dec_ref(v_dep_2495_);
v___x_2911_ = 0;
v___x_2912_ = l_Lean_Name_toString(v_name_2540_, v___x_2911_);
v___x_2913_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2914_ = lean_string_append(v___x_2912_, v___x_2913_);
v___x_2915_ = 3;
v___x_2916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*1, v___x_2915_);
lean_inc_ref(v_a_2501_);
v___x_2917_ = lean_apply_2(v_a_2501_, v___x_2916_, lean_box(0));
v___x_2918_ = lean_box(0);
v___x_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
v___jp_2503_:
{
lean_object* v_fullName_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_fullName_2506_ = lean_ctor_get(v___y_2504_, 1);
lean_inc_ref(v_fullName_2506_);
lean_dec_ref(v___y_2504_);
v___x_2507_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_2508_ = lean_string_append(v_fullName_2506_, v___x_2507_);
v___x_2509_ = 3;
v___x_2510_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*1, v___x_2509_);
lean_inc_ref(v___y_2505_);
v___x_2511_ = lean_apply_2(v___y_2505_, v___x_2510_, lean_box(0));
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
v___jp_2514_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___y_2517_);
v___x_2522_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2501_, v_dep_2495_, v_inherited_2496_, v_lakeEnv_2497_, v_wsDir_2498_, v___y_2519_, v___y_2516_, v___y_2515_, v___y_2520_, v___x_2521_, v___y_2518_);
lean_dec_ref(v_lakeEnv_2497_);
return v___x_2522_;
}
v___jp_2523_:
{
if (lean_obj_tag(v___y_2526_) == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2515_ = v___y_2524_;
v___y_2516_ = v___y_2525_;
v___y_2517_ = v_a_2529_;
v___y_2518_ = v___y_2528_;
v___y_2519_ = v___y_2527_;
v___y_2520_ = v___x_2530_;
goto v___jp_2514_;
}
else
{
lean_object* v_val_2531_; 
v_val_2531_ = lean_ctor_get(v___y_2526_, 0);
lean_inc(v_val_2531_);
lean_dec_ref_known(v___y_2526_, 1);
v___y_2515_ = v___y_2524_;
v___y_2516_ = v___y_2525_;
v___y_2517_ = v_a_2529_;
v___y_2518_ = v___y_2528_;
v___y_2519_ = v___y_2527_;
v___y_2520_ = v_val_2531_;
goto v___jp_2514_;
}
}
v___jp_2532_:
{
lean_object* v___x_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2534_ = lean_io_error_to_string(v_a_2533_);
v___x_2535_ = 3;
v___x_2536_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set_uint8(v___x_2536_, sizeof(void*)*1, v___x_2535_);
lean_inc_ref(v_a_2501_);
v___x_2537_ = lean_apply_2(v_a_2501_, v___x_2536_, lean_box(0));
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
v___jp_2544_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2550_ = l_Lake_defaultConfigFile;
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2552_, 0, v_name_2540_);
lean_ctor_set(v___x_2552_, 1, v_scope_2541_);
lean_ctor_set(v___x_2552_, 2, v___x_2550_);
lean_ctor_set(v___x_2552_, 3, v___x_2551_);
lean_ctor_set(v___x_2552_, 4, v___y_2548_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*5, v_inherited_2496_);
lean_inc_ref(v___y_2545_);
v___x_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2553_, 0, v___y_2547_);
lean_ctor_set(v___x_2553_, 1, v___y_2546_);
lean_ctor_set(v___x_2553_, 2, v___y_2545_);
lean_ctor_set(v___x_2553_, 3, v_a_2549_);
lean_ctor_set(v___x_2553_, 4, v___x_2552_);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
v___jp_2555_:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = lean_array_get_size(v___y_2559_);
v___x_2564_ = lean_nat_dec_lt(v___y_2560_, v___x_2563_);
if (v___x_2564_ == 0)
{
v___y_2545_ = v___y_2556_;
v___y_2546_ = v___y_2557_;
v___y_2547_ = v___y_2558_;
v___y_2548_ = v___y_2561_;
v_a_2549_ = v_val_2562_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v___x_2565_ = lean_box(0);
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = lean_usize_of_nat(v___x_2563_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2559_, v___x_2566_, v___x_2567_, v___x_2565_, v_a_2501_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_dec_ref_known(v___x_2568_, 1);
v___y_2545_ = v___y_2556_;
v___y_2546_ = v___y_2557_;
v___y_2547_ = v___y_2558_;
v___y_2548_ = v___y_2561_;
v_a_2549_ = v_val_2562_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_val_2562_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v_scope_2541_);
lean_dec(v_name_2540_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
v___jp_2577_:
{
if (lean_obj_tag(v_a_2583_) == 1)
{
lean_object* v_val_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2578_);
v_val_2584_ = lean_ctor_get(v_a_2583_, 0);
lean_inc_n(v_val_2584_, 2);
lean_dec_ref_known(v_a_2583_, 1);
v___x_2585_ = l_Lake_defaultManifestFile;
v___x_2586_ = l_Lake_joinRelative(v_val_2584_, v___x_2585_);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2589_ = l_Lake_Manifest_load(v___x_2586_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 1);
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
v___y_2556_ = v___y_2579_;
v___y_2557_ = v___y_2580_;
v___y_2558_ = v_val_2584_;
v___y_2559_ = v___x_2588_;
v___y_2560_ = v___x_2587_;
v___y_2561_ = v___y_2582_;
v_val_2562_ = v___x_2595_;
goto v___jp_2555_;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_a_2598_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2589_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2589_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 0);
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
v___y_2556_ = v___y_2579_;
v___y_2557_ = v___y_2580_;
v___y_2558_ = v_val_2584_;
v___y_2559_ = v___x_2588_;
v___y_2560_ = v___x_2587_;
v___y_2561_ = v___y_2582_;
v_val_2562_ = v___x_2603_;
goto v___jp_2555_;
}
}
}
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_dec(v_a_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_scope_2541_);
lean_dec(v_name_2540_);
v___x_2606_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2607_ = lean_string_append(v___y_2581_, v___x_2606_);
v___x_2608_ = lean_string_append(v___x_2607_, v___y_2578_);
lean_dec_ref(v___y_2578_);
v___x_2609_ = 3;
v___x_2610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*1, v___x_2609_);
lean_inc_ref(v_a_2501_);
v___x_2611_ = lean_apply_2(v_a_2501_, v___x_2610_, lean_box(0));
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
v___jp_2614_:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = lean_array_get_size(v___y_2618_);
v___x_2624_ = lean_nat_dec_lt(v___y_2619_, v___x_2623_);
if (v___x_2624_ == 0)
{
v___y_2578_ = v___y_2615_;
v___y_2579_ = v___y_2616_;
v___y_2580_ = v___y_2617_;
v___y_2581_ = v___y_2621_;
v___y_2582_ = v___y_2620_;
v_a_2583_ = v_val_2622_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2625_; size_t v___x_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v___x_2625_ = lean_box(0);
v___x_2626_ = ((size_t)0ULL);
v___x_2627_ = lean_usize_of_nat(v___x_2623_);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2618_, v___x_2626_, v___x_2627_, v___x_2625_, v_a_2501_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_dec_ref_known(v___x_2628_, 1);
v___y_2578_ = v___y_2615_;
v___y_2579_ = v___y_2616_;
v___y_2580_ = v___y_2617_;
v___y_2581_ = v___y_2621_;
v___y_2582_ = v___y_2620_;
v_a_2583_ = v_val_2622_;
goto v___jp_2577_;
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_val_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2615_);
lean_dec_ref(v_scope_2541_);
lean_dec(v_name_2540_);
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2920_, lean_object* v_inherited_2921_, lean_object* v_lakeEnv_2922_, lean_object* v_wsDir_2923_, lean_object* v_relPkgsDir_2924_, lean_object* v_relParentDir_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
uint8_t v_inherited_boxed_2928_; lean_object* v_res_2929_; 
v_inherited_boxed_2928_ = lean_unbox(v_inherited_2921_);
v_res_2929_ = l_Lake_Dependency_materialize(v_dep_2920_, v_inherited_boxed_2928_, v_lakeEnv_2922_, v_wsDir_2923_, v_relPkgsDir_2924_, v_relParentDir_2925_, v_a_2926_);
lean_dec_ref(v_a_2926_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2935_, lean_object* v_wsDir_2936_, lean_object* v_relPkgDir_2937_, lean_object* v_remoteUrl_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v___y_2942_; lean_object* v_a_2943_; lean_object* v___f_2946_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v_val_2952_; lean_object* v_pkgDir_2968_; lean_object* v_a_2970_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_val_3012_; lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___f_2946_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_2937_);
v_pkgDir_2968_ = l_Lake_joinRelative(v_wsDir_2936_, v_relPkgDir_2937_);
v___x_3008_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2968_);
v___x_3027_ = l_Lake_resolvePath(v_pkgDir_2968_);
v___x_3028_ = lean_string_utf8_byte_size(v___x_3027_);
v___x_3029_ = lean_nat_dec_eq(v___x_3028_, v___x_3009_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3027_);
v_val_3012_ = v___x_3030_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3031_; 
lean_dec_ref(v___x_3027_);
v___x_3031_ = lean_box(0);
v_val_3012_ = v___x_3031_;
goto v___jp_3011_;
}
v___jp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2944_, 0, v___y_2942_);
lean_ctor_set(v___x_2944_, 1, v_relPkgDir_2937_);
lean_ctor_set(v___x_2944_, 2, v_remoteUrl_2938_);
lean_ctor_set(v___x_2944_, 3, v_a_2943_);
lean_ctor_set(v___x_2944_, 4, v_manifestEntry_2935_);
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
return v___x_2945_;
}
v___jp_2947_:
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = lean_array_get_size(v___y_2951_);
v___x_2954_ = lean_nat_dec_lt(v___y_2949_, v___x_2953_);
if (v___x_2954_ == 0)
{
v___y_2942_ = v___y_2950_;
v_a_2943_ = v_val_2952_;
goto v___jp_2941_;
}
else
{
lean_object* v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; lean_object* v___x_1877__overap_2958_; lean_object* v___x_2959_; 
v___x_2955_ = lean_box(0);
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = lean_usize_of_nat(v___x_2953_);
lean_inc_ref(v___y_2951_);
lean_inc_ref(v___y_2948_);
v___x_1877__overap_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2948_, v___f_2946_, v___y_2951_, v___x_2956_, v___x_2957_, v___x_2955_);
lean_inc_ref(v_a_2939_);
v___x_2959_ = lean_apply_2(v___x_1877__overap_2958_, v_a_2939_, lean_box(0));
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_dec_ref_known(v___x_2959_, 1);
v___y_2942_ = v___y_2950_;
v_a_2943_ = v_val_2952_;
goto v___jp_2941_;
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v_val_2952_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v_remoteUrl_2938_);
lean_dec_ref(v_relPkgDir_2937_);
lean_dec_ref(v_manifestEntry_2935_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
}
v___jp_2969_:
{
if (lean_obj_tag(v_a_2970_) == 1)
{
lean_object* v_manifestFile_x3f_2971_; 
lean_dec_ref(v_pkgDir_2968_);
v_manifestFile_x3f_2971_ = lean_ctor_get(v_manifestEntry_2935_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2971_) == 1)
{
lean_object* v_val_2972_; lean_object* v_val_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_val_2972_ = lean_ctor_get(v_a_2970_, 0);
lean_inc_n(v_val_2972_, 2);
lean_dec_ref_known(v_a_2970_, 1);
v_val_2973_ = lean_ctor_get(v_manifestFile_x3f_2971_, 0);
lean_inc(v_val_2973_);
v___x_2974_ = l_Lake_joinRelative(v_val_2972_, v_val_2973_);
v___x_2975_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2978_ = l_Lake_Manifest_load(v___x_2974_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set_tag(v___x_2981_, 1);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
v___y_2948_ = v___x_2975_;
v___y_2949_ = v___x_2976_;
v___y_2950_ = v_val_2972_;
v___y_2951_ = v___x_2977_;
v_val_2952_ = v___x_2984_;
goto v___jp_2947_;
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
v_a_2987_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2978_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2978_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 0);
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
v___y_2948_ = v___x_2975_;
v___y_2949_ = v___x_2976_;
v___y_2950_ = v_val_2972_;
v___y_2951_ = v___x_2977_;
v_val_2952_ = v___x_2992_;
goto v___jp_2947_;
}
}
}
}
else
{
lean_object* v_val_2995_; lean_object* v___x_2996_; 
v_val_2995_ = lean_ctor_get(v_a_2970_, 0);
lean_inc(v_val_2995_);
lean_dec_ref_known(v_a_2970_, 1);
v___x_2996_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2942_ = v_val_2995_;
v_a_2943_ = v___x_2996_;
goto v___jp_2941_;
}
}
else
{
lean_object* v_name_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec(v_a_2970_);
lean_dec_ref(v_remoteUrl_2938_);
lean_dec_ref(v_relPkgDir_2937_);
v_name_2997_ = lean_ctor_get(v_manifestEntry_2935_, 0);
lean_inc(v_name_2997_);
lean_dec_ref(v_manifestEntry_2935_);
v___x_2998_ = 0;
v___x_2999_ = l_Lean_Name_toString(v_name_2997_, v___x_2998_);
v___x_3000_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3001_ = lean_string_append(v___x_2999_, v___x_3000_);
v___x_3002_ = lean_string_append(v___x_3001_, v_pkgDir_2968_);
lean_dec_ref(v_pkgDir_2968_);
v___x_3003_ = 3;
v___x_3004_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set_uint8(v___x_3004_, sizeof(void*)*1, v___x_3003_);
lean_inc_ref(v_a_2939_);
v___x_3005_ = lean_apply_2(v_a_2939_, v___x_3004_, lean_box(0));
v___x_3006_ = lean_box(0);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
return v___x_3007_;
}
}
v___jp_3011_:
{
uint8_t v___x_3013_; 
v___x_3013_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3013_ == 0)
{
v_a_2970_ = v_val_3012_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; lean_object* v___x_1931__overap_3017_; lean_object* v___x_3018_; 
v___x_3014_ = lean_box(0);
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1931__overap_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3008_, v___f_2946_, v___x_3010_, v___x_3015_, v___x_3016_, v___x_3014_);
lean_inc_ref(v_a_2939_);
v___x_3018_ = lean_apply_2(v___x_1931__overap_3017_, v_a_2939_, lean_box(0));
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_dec_ref_known(v___x_3018_, 1);
v_a_2970_ = v_val_3012_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_val_3012_);
lean_dec_ref(v_pkgDir_2968_);
lean_dec_ref(v_remoteUrl_2938_);
lean_dec_ref(v_relPkgDir_2937_);
lean_dec_ref(v_manifestEntry_2935_);
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_3032_, lean_object* v_wsDir_3033_, lean_object* v_relPkgDir_3034_, lean_object* v_remoteUrl_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_3032_, v_wsDir_3033_, v_relPkgDir_3034_, v_remoteUrl_3035_, v_a_3036_);
lean_dec_ref(v_a_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object* v_t_3039_, lean_object* v_k_3040_, lean_object* v_fallback_3041_){
_start:
{
if (lean_obj_tag(v_t_3039_) == 0)
{
lean_object* v_k_3042_; lean_object* v_v_3043_; lean_object* v_l_3044_; lean_object* v_r_3045_; uint8_t v___x_3046_; 
v_k_3042_ = lean_ctor_get(v_t_3039_, 1);
v_v_3043_ = lean_ctor_get(v_t_3039_, 2);
v_l_3044_ = lean_ctor_get(v_t_3039_, 3);
v_r_3045_ = lean_ctor_get(v_t_3039_, 4);
v___x_3046_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3040_, v_k_3042_);
switch(v___x_3046_)
{
case 0:
{
v_t_3039_ = v_l_3044_;
goto _start;
}
case 1:
{
lean_inc(v_v_3043_);
return v_v_3043_;
}
default: 
{
v_t_3039_ = v_r_3045_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3041_);
return v_fallback_3041_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object* v_t_3049_, lean_object* v_k_3050_, lean_object* v_fallback_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3049_, v_k_3050_, v_fallback_3051_);
lean_dec(v_fallback_3051_);
lean_dec(v_k_3050_);
lean_dec(v_t_3049_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_3053_, lean_object* v_lakeEnv_3054_, lean_object* v_wsDir_3055_, lean_object* v_relPkgsDir_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v_a_3063_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v_val_3072_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v_a_3091_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v_val_3100_; lean_object* v_name_3115_; lean_object* v_manifestFile_x3f_3116_; lean_object* v_src_3117_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v_a_3122_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v_val_3171_; lean_object* v_a_3187_; 
v_name_3115_ = lean_ctor_get(v_manifestEntry_3053_, 0);
v_manifestFile_x3f_3116_ = lean_ctor_get(v_manifestEntry_3053_, 3);
v_src_3117_ = lean_ctor_get(v_manifestEntry_3053_, 4);
lean_inc_ref(v_src_3117_);
if (lean_obj_tag(v_src_3117_) == 0)
{
uint8_t v_copy_3197_; 
v_copy_3197_ = lean_ctor_get_uint8(v_src_3117_, sizeof(void*)*1);
if (v_copy_3197_ == 0)
{
lean_object* v_dir_3198_; 
lean_dec_ref(v_relPkgsDir_3056_);
v_dir_3198_ = lean_ctor_get(v_src_3117_, 0);
lean_inc_ref(v_dir_3198_);
lean_dec_ref_known(v_src_3117_, 1);
v_a_3187_ = v_dir_3198_;
goto v___jp_3186_;
}
else
{
lean_object* v_dir_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3225_; 
v_dir_3199_ = lean_ctor_get(v_src_3117_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_src_3117_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3201_ = v_src_3117_;
v_isShared_3202_ = v_isSharedCheck_3225_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_dir_3199_);
lean_dec(v_src_3117_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3225_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
uint8_t v___x_3203_; lean_object* v___x_3204_; lean_object* v_relDst_3205_; lean_object* v_dst_3206_; uint8_t v___x_3207_; 
v___x_3203_ = 0;
lean_inc(v_name_3115_);
v___x_3204_ = l_Lean_Name_toString(v_name_3115_, v___x_3203_);
v_relDst_3205_ = l_Lake_joinRelative(v_relPkgsDir_3056_, v___x_3204_);
lean_inc_ref(v_relDst_3205_);
lean_inc_ref(v_wsDir_3055_);
v_dst_3206_ = l_Lake_joinRelative(v_wsDir_3055_, v_relDst_3205_);
v___x_3207_ = l_System_FilePath_pathExists(v_dst_3206_);
if (v___x_3207_ == 0)
{
lean_object* v_src_3208_; lean_object* v___x_3209_; 
lean_inc_ref(v_wsDir_3055_);
v_src_3208_ = l_Lake_joinRelative(v_wsDir_3055_, v_dir_3199_);
v___x_3209_ = l_Lake_copyDirAll(v_src_3208_, v_dst_3206_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_dec_ref_known(v___x_3209_, 1);
lean_del_object(v___x_3201_);
v_a_3187_ = v_relDst_3205_;
goto v___jp_3186_;
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v_relDst_3205_);
lean_dec_ref(v_wsDir_3055_);
lean_dec_ref(v_manifestEntry_3053_);
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3224_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3224_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3217_; 
v___x_3214_ = lean_io_error_to_string(v_a_3210_);
v___x_3215_ = 3;
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3214_);
v___x_3217_ = v___x_3201_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3214_);
v___x_3217_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*1, v___x_3215_);
lean_inc_ref(v_a_3057_);
v___x_3218_ = lean_apply_2(v_a_3057_, v___x_3217_, lean_box(0));
v___x_3219_ = lean_box(0);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3219_);
v___x_3221_ = v___x_3212_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
else
{
lean_dec_ref(v_dst_3206_);
lean_del_object(v___x_3201_);
lean_dec_ref(v_dir_3199_);
v_a_3187_ = v_relDst_3205_;
goto v___jp_3186_;
}
}
}
}
else
{
lean_object* v_url_3226_; lean_object* v_rev_3227_; lean_object* v_subDir_x3f_3228_; lean_object* v_pkgUrlMap_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v_val_3275_; lean_object* v_relGitDir_3290_; lean_object* v_repo_3291_; lean_object* v_url_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_url_3226_ = lean_ctor_get(v_src_3117_, 0);
lean_inc_ref(v_url_3226_);
v_rev_3227_ = lean_ctor_get(v_src_3117_, 1);
lean_inc_ref(v_rev_3227_);
v_subDir_x3f_3228_ = lean_ctor_get(v_src_3117_, 3);
lean_inc(v_subDir_x3f_3228_);
lean_dec_ref_known(v_src_3117_, 4);
v_pkgUrlMap_3229_ = lean_ctor_get(v_lakeEnv_3054_, 5);
v___x_3230_ = 0;
lean_inc(v_name_3115_);
v___x_3231_ = l_Lean_Name_toString(v_name_3115_, v___x_3230_);
lean_inc_ref_n(v___x_3231_, 2);
v_relGitDir_3290_ = l_Lake_joinRelative(v_relPkgsDir_3056_, v___x_3231_);
lean_inc_ref(v_relGitDir_3290_);
lean_inc_ref(v_wsDir_3055_);
v_repo_3291_ = l_Lake_joinRelative(v_wsDir_3055_, v_relGitDir_3290_);
v_url_3292_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_pkgUrlMap_3229_, v_name_3115_, v_url_3226_);
lean_dec_ref(v_url_3226_);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v_rev_3227_);
lean_inc(v_url_3292_);
v___x_3294_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_3057_, v___x_3231_, v_repo_3291_, v_url_3292_, v___x_3293_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3307_; 
lean_dec_ref_known(v___x_3294_, 1);
if (lean_obj_tag(v_subDir_x3f_3228_) == 0)
{
v___y_3307_ = v_relGitDir_3290_;
goto v___jp_3306_;
}
else
{
lean_object* v_val_3311_; lean_object* v___x_3312_; 
v_val_3311_ = lean_ctor_get(v_subDir_x3f_3228_, 0);
lean_inc(v_val_3311_);
lean_dec_ref_known(v_subDir_x3f_3228_, 1);
v___x_3312_ = l_Lake_joinRelative(v_relGitDir_3290_, v_val_3311_);
v___y_3307_ = v___x_3312_;
goto v___jp_3306_;
}
v___jp_3295_:
{
lean_object* v_pkgDir_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
lean_inc_ref(v___y_3296_);
v_pkgDir_3298_ = l_Lake_joinRelative(v_wsDir_3055_, v___y_3296_);
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3298_);
v___x_3301_ = l_Lake_resolvePath(v_pkgDir_3298_);
v___x_3302_ = lean_string_utf8_byte_size(v___x_3301_);
v___x_3303_ = lean_nat_dec_eq(v___x_3302_, v___x_3299_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3301_);
v___y_3270_ = v_pkgDir_3298_;
v___y_3271_ = v___y_3296_;
v___y_3272_ = v___x_3299_;
v___y_3273_ = v___y_3297_;
v___y_3274_ = v___x_3300_;
v_val_3275_ = v___x_3304_;
goto v___jp_3269_;
}
else
{
lean_object* v___x_3305_; 
lean_dec_ref(v___x_3301_);
v___x_3305_ = lean_box(0);
v___y_3270_ = v_pkgDir_3298_;
v___y_3271_ = v___y_3296_;
v___y_3272_ = v___x_3299_;
v___y_3273_ = v___y_3297_;
v___y_3274_ = v___x_3300_;
v_val_3275_ = v___x_3305_;
goto v___jp_3269_;
}
}
v___jp_3306_:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lake_Git_filterUrl_x3f(v_url_3292_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v___x_3309_; 
v___x_3309_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_3296_ = v___y_3307_;
v___y_3297_ = v___x_3309_;
goto v___jp_3295_;
}
else
{
lean_object* v_val_3310_; 
v_val_3310_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_val_3310_);
lean_dec_ref_known(v___x_3308_, 1);
v___y_3296_ = v___y_3307_;
v___y_3297_ = v_val_3310_;
goto v___jp_3295_;
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec(v_url_3292_);
lean_dec_ref(v_relGitDir_3290_);
lean_dec_ref(v___x_3231_);
lean_dec(v_subDir_x3f_3228_);
lean_dec_ref(v_wsDir_3055_);
lean_dec_ref(v_manifestEntry_3053_);
v_a_3313_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3294_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3294_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
v___jp_3232_:
{
if (lean_obj_tag(v_a_3236_) == 1)
{
lean_dec_ref(v___y_3233_);
lean_dec_ref(v___x_3231_);
if (lean_obj_tag(v_manifestFile_x3f_3116_) == 1)
{
lean_object* v_val_3237_; lean_object* v_val_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_val_3237_ = lean_ctor_get(v_a_3236_, 0);
lean_inc_n(v_val_3237_, 2);
lean_dec_ref_known(v_a_3236_, 1);
v_val_3238_ = lean_ctor_get(v_manifestFile_x3f_3116_, 0);
lean_inc(v_val_3238_);
v___x_3239_ = l_Lake_joinRelative(v_val_3237_, v_val_3238_);
v___x_3240_ = lean_unsigned_to_nat(0u);
v___x_3241_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3242_ = l_Lake_Manifest_load(v___x_3239_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
lean_ctor_set_tag(v___x_3245_, 1);
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
v___y_3067_ = v___x_3240_;
v___y_3068_ = v___y_3234_;
v___y_3069_ = v___x_3241_;
v___y_3070_ = v___y_3235_;
v___y_3071_ = v_val_3237_;
v_val_3072_ = v___x_3248_;
goto v___jp_3066_;
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
v_a_3251_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3242_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3242_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
lean_ctor_set_tag(v___x_3253_, 0);
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
v___y_3067_ = v___x_3240_;
v___y_3068_ = v___y_3234_;
v___y_3069_ = v___x_3241_;
v___y_3070_ = v___y_3235_;
v___y_3071_ = v_val_3237_;
v_val_3072_ = v___x_3256_;
goto v___jp_3066_;
}
}
}
}
else
{
lean_object* v_val_3259_; lean_object* v___x_3260_; 
v_val_3259_ = lean_ctor_get(v_a_3236_, 0);
lean_inc(v_val_3259_);
lean_dec_ref_known(v_a_3236_, 1);
v___x_3260_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_3060_ = v___y_3234_;
v___y_3061_ = v___y_3235_;
v___y_3062_ = v_val_3259_;
v_a_3063_ = v___x_3260_;
goto v___jp_3059_;
}
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec(v_a_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v_manifestEntry_3053_);
v___x_3261_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3262_ = lean_string_append(v___x_3231_, v___x_3261_);
v___x_3263_ = lean_string_append(v___x_3262_, v___y_3233_);
lean_dec_ref(v___y_3233_);
v___x_3264_ = 3;
v___x_3265_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*1, v___x_3264_);
lean_inc_ref(v_a_3057_);
v___x_3266_ = lean_apply_2(v_a_3057_, v___x_3265_, lean_box(0));
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
}
v___jp_3269_:
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = lean_array_get_size(v___y_3274_);
v___x_3277_ = lean_nat_dec_lt(v___y_3272_, v___x_3276_);
if (v___x_3277_ == 0)
{
v___y_3233_ = v___y_3270_;
v___y_3234_ = v___y_3271_;
v___y_3235_ = v___y_3273_;
v_a_3236_ = v_val_3275_;
goto v___jp_3232_;
}
else
{
lean_object* v___x_3278_; size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v___x_3278_ = lean_box(0);
v___x_3279_ = ((size_t)0ULL);
v___x_3280_ = lean_usize_of_nat(v___x_3276_);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3274_, v___x_3279_, v___x_3280_, v___x_3278_, v_a_3057_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_dec_ref_known(v___x_3281_, 1);
v___y_3233_ = v___y_3270_;
v___y_3234_ = v___y_3271_;
v___y_3235_ = v___y_3273_;
v_a_3236_ = v_val_3275_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_val_3275_);
lean_dec_ref(v___y_3273_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec_ref(v___x_3231_);
lean_dec_ref(v_manifestEntry_3053_);
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
}
v___jp_3059_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3064_, 0, v___y_3062_);
lean_ctor_set(v___x_3064_, 1, v___y_3060_);
lean_ctor_set(v___x_3064_, 2, v___y_3061_);
lean_ctor_set(v___x_3064_, 3, v_a_3063_);
lean_ctor_set(v___x_3064_, 4, v_manifestEntry_3053_);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
v___jp_3066_:
{
lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = lean_array_get_size(v___y_3069_);
v___x_3074_ = lean_nat_dec_lt(v___y_3067_, v___x_3073_);
if (v___x_3074_ == 0)
{
v___y_3060_ = v___y_3068_;
v___y_3061_ = v___y_3070_;
v___y_3062_ = v___y_3071_;
v_a_3063_ = v_val_3072_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3075_; size_t v___x_3076_; size_t v___x_3077_; lean_object* v___x_3078_; 
v___x_3075_ = lean_box(0);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = lean_usize_of_nat(v___x_3073_);
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3069_, v___x_3076_, v___x_3077_, v___x_3075_, v_a_3057_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_dec_ref_known(v___x_3078_, 1);
v___y_3060_ = v___y_3068_;
v___y_3061_ = v___y_3070_;
v___y_3062_ = v___y_3071_;
v_a_3063_ = v_val_3072_;
goto v___jp_3059_;
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v_val_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v_manifestEntry_3053_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
v___jp_3087_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_inc_ref(v___y_3088_);
v___x_3092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3092_, 0, v___y_3090_);
lean_ctor_set(v___x_3092_, 1, v___y_3089_);
lean_ctor_set(v___x_3092_, 2, v___y_3088_);
lean_ctor_set(v___x_3092_, 3, v_a_3091_);
lean_ctor_set(v___x_3092_, 4, v_manifestEntry_3053_);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
v___jp_3094_:
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = lean_array_get_size(v___y_3099_);
v___x_3102_ = lean_nat_dec_lt(v___y_3096_, v___x_3101_);
if (v___x_3102_ == 0)
{
v___y_3088_ = v___y_3095_;
v___y_3089_ = v___y_3097_;
v___y_3090_ = v___y_3098_;
v_a_3091_ = v_val_3100_;
goto v___jp_3087_;
}
else
{
lean_object* v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v___x_3103_ = lean_box(0);
v___x_3104_ = ((size_t)0ULL);
v___x_3105_ = lean_usize_of_nat(v___x_3101_);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3099_, v___x_3104_, v___x_3105_, v___x_3103_, v_a_3057_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_dec_ref_known(v___x_3106_, 1);
v___y_3088_ = v___y_3095_;
v___y_3089_ = v___y_3097_;
v___y_3090_ = v___y_3098_;
v_a_3091_ = v_val_3100_;
goto v___jp_3087_;
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref(v_val_3100_);
lean_dec_ref(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec_ref(v_manifestEntry_3053_);
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
v___jp_3118_:
{
if (lean_obj_tag(v_a_3122_) == 1)
{
lean_dec_ref(v___y_3119_);
if (lean_obj_tag(v_manifestFile_x3f_3116_) == 1)
{
lean_object* v_val_3123_; lean_object* v_val_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_val_3123_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_n(v_val_3123_, 2);
lean_dec_ref_known(v_a_3122_, 1);
v_val_3124_ = lean_ctor_get(v_manifestFile_x3f_3116_, 0);
lean_inc(v_val_3124_);
v___x_3125_ = l_Lake_joinRelative(v_val_3123_, v_val_3124_);
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3128_ = l_Lake_Manifest_load(v___x_3125_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 1);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
v___y_3095_ = v___y_3120_;
v___y_3096_ = v___x_3126_;
v___y_3097_ = v___y_3121_;
v___y_3098_ = v_val_3123_;
v___y_3099_ = v___x_3127_;
v_val_3100_ = v___x_3134_;
goto v___jp_3094_;
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_a_3137_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3128_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3128_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set_tag(v___x_3139_, 0);
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
v___y_3095_ = v___y_3120_;
v___y_3096_ = v___x_3126_;
v___y_3097_ = v___y_3121_;
v___y_3098_ = v_val_3123_;
v___y_3099_ = v___x_3127_;
v_val_3100_ = v___x_3142_;
goto v___jp_3094_;
}
}
}
}
else
{
lean_object* v_val_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3154_; 
v_val_3145_ = lean_ctor_get(v_a_3122_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_a_3122_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3147_ = v_a_3122_;
v_isShared_3148_ = v_isSharedCheck_3154_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_val_3145_);
lean_dec(v_a_3122_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3154_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
uint32_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3149_ = 0;
lean_inc_ref_n(v___y_3120_, 2);
v___x_3150_ = lean_alloc_ctor(11, 2, 4);
lean_ctor_set(v___x_3150_, 0, v___y_3120_);
lean_ctor_set(v___x_3150_, 1, v___y_3120_);
lean_ctor_set_uint32(v___x_3150_, sizeof(void*)*2, v___x_3149_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3150_);
v___x_3152_ = v___x_3147_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
v___y_3088_ = v___y_3120_;
v___y_3089_ = v___y_3121_;
v___y_3090_ = v_val_3145_;
v_a_3091_ = v___x_3152_;
goto v___jp_3087_;
}
}
}
}
else
{
uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
lean_inc(v_name_3115_);
lean_dec(v_a_3122_);
lean_dec_ref(v___y_3121_);
lean_dec_ref(v_manifestEntry_3053_);
v___x_3155_ = 0;
v___x_3156_ = l_Lean_Name_toString(v_name_3115_, v___x_3155_);
v___x_3157_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3158_ = lean_string_append(v___x_3156_, v___x_3157_);
v___x_3159_ = lean_string_append(v___x_3158_, v___y_3119_);
lean_dec_ref(v___y_3119_);
v___x_3160_ = 3;
v___x_3161_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*1, v___x_3160_);
lean_inc_ref(v_a_3057_);
v___x_3162_ = lean_apply_2(v_a_3057_, v___x_3161_, lean_box(0));
v___x_3163_ = lean_box(0);
v___x_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
v___jp_3165_:
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = lean_array_get_size(v___y_3170_);
v___x_3173_ = lean_nat_dec_lt(v___y_3168_, v___x_3172_);
if (v___x_3173_ == 0)
{
v___y_3119_ = v___y_3167_;
v___y_3120_ = v___y_3166_;
v___y_3121_ = v___y_3169_;
v_a_3122_ = v_val_3171_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3174_; size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3174_ = lean_box(0);
v___x_3175_ = ((size_t)0ULL);
v___x_3176_ = lean_usize_of_nat(v___x_3172_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3170_, v___x_3175_, v___x_3176_, v___x_3174_, v_a_3057_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec_ref_known(v___x_3177_, 1);
v___y_3119_ = v___y_3167_;
v___y_3120_ = v___y_3166_;
v___y_3121_ = v___y_3169_;
v_a_3122_ = v_val_3171_;
goto v___jp_3118_;
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_val_3171_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v___y_3167_);
lean_dec_ref(v_manifestEntry_3053_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
v___jp_3186_:
{
lean_object* v___x_3188_; lean_object* v_pkgDir_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3188_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_a_3187_);
v_pkgDir_3189_ = l_Lake_joinRelative(v_wsDir_3055_, v_a_3187_);
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3189_);
v___x_3192_ = l_Lake_resolvePath(v_pkgDir_3189_);
v___x_3193_ = lean_string_utf8_byte_size(v___x_3192_);
v___x_3194_ = lean_nat_dec_eq(v___x_3193_, v___x_3190_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3192_);
v___y_3166_ = v___x_3188_;
v___y_3167_ = v_pkgDir_3189_;
v___y_3168_ = v___x_3190_;
v___y_3169_ = v_a_3187_;
v___y_3170_ = v___x_3191_;
v_val_3171_ = v___x_3195_;
goto v___jp_3165_;
}
else
{
lean_object* v___x_3196_; 
lean_dec_ref(v___x_3192_);
v___x_3196_ = lean_box(0);
v___y_3166_ = v___x_3188_;
v___y_3167_ = v_pkgDir_3189_;
v___y_3168_ = v___x_3190_;
v___y_3169_ = v_a_3187_;
v___y_3170_ = v___x_3191_;
v_val_3171_ = v___x_3196_;
goto v___jp_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_3321_, lean_object* v_lakeEnv_3322_, lean_object* v_wsDir_3323_, lean_object* v_relPkgsDir_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lake_PackageEntry_materialize(v_manifestEntry_3321_, v_lakeEnv_3322_, v_wsDir_3323_, v_relPkgsDir_3324_, v_a_3325_);
lean_dec_ref(v_a_3325_);
lean_dec_ref(v_lakeEnv_3322_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object* v_00_u03b4_3328_, lean_object* v_t_3329_, lean_object* v_k_3330_, lean_object* v_fallback_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3329_, v_k_3330_, v_fallback_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object* v_00_u03b4_3333_, lean_object* v_t_3334_, lean_object* v_k_3335_, lean_object* v_fallback_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(v_00_u03b4_3333_, v_t_3334_, v_k_3335_, v_fallback_3336_);
lean_dec(v_fallback_3336_);
lean_dec(v_k_3335_);
lean_dec(v_t_3334_);
return v_res_3337_;
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
