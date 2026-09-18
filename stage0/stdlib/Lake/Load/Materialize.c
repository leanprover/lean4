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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* v_dep_1148_, uint8_t v_inherited_1149_, lean_object* v_wsDir_1150_, lean_object* v_name_1151_, lean_object* v_relPkgDir_1152_, lean_object* v_remoteUrl_1153_, lean_object* v_src_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___y_1158_; lean_object* v_a_1159_; lean_object* v___f_1176_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v_val_1182_; lean_object* v_pkgDir_1198_; lean_object* v_a_1200_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_val_1236_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___f_1176_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_1152_);
v_pkgDir_1198_ = l_Lake_joinRelative(v_wsDir_1150_, v_relPkgDir_1152_);
v___x_1232_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_1198_);
v___x_1251_ = l_Lake_resolvePath(v_pkgDir_1198_);
v___x_1252_ = lean_string_utf8_byte_size(v___x_1251_);
v___x_1253_ = lean_nat_dec_eq(v___x_1252_, v___x_1233_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1251_);
v_val_1236_ = v___x_1254_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1255_; 
lean_dec_ref(v___x_1251_);
v___x_1255_ = lean_box(0);
v_val_1236_ = v___x_1255_;
goto v___jp_1235_;
}
v___jp_1157_:
{
lean_object* v_name_1160_; lean_object* v_scope_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1172_; 
v_name_1160_ = lean_ctor_get(v_dep_1148_, 0);
v_scope_1161_ = lean_ctor_get(v_dep_1148_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_dep_1148_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; 
v_unused_1173_ = lean_ctor_get(v_dep_1148_, 4);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_dep_1148_, 3);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_dep_1148_, 2);
lean_dec(v_unused_1175_);
v___x_1163_ = v_dep_1148_;
v_isShared_1164_ = v_isSharedCheck_1172_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_scope_1161_);
lean_inc(v_name_1160_);
lean_dec(v_dep_1148_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1172_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1165_ = l_Lake_defaultConfigFile;
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1167_, 0, v_name_1160_);
lean_ctor_set(v___x_1167_, 1, v_scope_1161_);
lean_ctor_set(v___x_1167_, 2, v___x_1165_);
lean_ctor_set(v___x_1167_, 3, v___x_1166_);
lean_ctor_set(v___x_1167_, 4, v_src_1154_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*5, v_inherited_1149_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 4, v___x_1167_);
lean_ctor_set(v___x_1163_, 3, v_a_1159_);
lean_ctor_set(v___x_1163_, 2, v_remoteUrl_1153_);
lean_ctor_set(v___x_1163_, 1, v_relPkgDir_1152_);
lean_ctor_set(v___x_1163_, 0, v___y_1158_);
v___x_1169_ = v___x_1163_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___y_1158_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_relPkgDir_1152_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_remoteUrl_1153_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_a_1159_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
}
v___jp_1177_:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_array_get_size(v___y_1180_);
v___x_1184_ = lean_nat_dec_lt(v___y_1181_, v___x_1183_);
if (v___x_1184_ == 0)
{
v___y_1158_ = v___y_1179_;
v_a_1159_ = v_val_1182_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1819__overap_1188_; lean_object* v___x_1189_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = ((size_t)0ULL);
v___x_1187_ = lean_usize_of_nat(v___x_1183_);
lean_inc_ref(v___y_1180_);
lean_inc_ref(v___y_1178_);
v___x_1819__overap_1188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_1178_, v___f_1176_, v___y_1180_, v___x_1186_, v___x_1187_, v___x_1185_);
lean_inc_ref(v_a_1155_);
v___x_1189_ = lean_apply_2(v___x_1819__overap_1188_, v_a_1155_, lean_box(0));
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_dec_ref_known(v___x_1189_, 1);
v___y_1158_ = v___y_1179_;
v_a_1159_ = v_val_1182_;
goto v___jp_1157_;
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v_val_1182_);
lean_dec_ref(v___y_1179_);
lean_dec_ref(v_src_1154_);
lean_dec_ref(v_remoteUrl_1153_);
lean_dec_ref(v_relPkgDir_1152_);
lean_dec_ref(v_dep_1148_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
v___jp_1199_:
{
if (lean_obj_tag(v_a_1200_) == 1)
{
lean_object* v_val_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec_ref(v_pkgDir_1198_);
lean_dec_ref(v_name_1151_);
v_val_1201_ = lean_ctor_get(v_a_1200_, 0);
lean_inc_n(v_val_1201_, 2);
lean_dec_ref_known(v_a_1200_, 1);
v___x_1202_ = l_Lake_defaultManifestFile;
v___x_1203_ = l_Lake_joinRelative(v_val_1201_, v___x_1202_);
v___x_1204_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1207_ = l_Lake_Manifest_load(v___x_1203_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 1);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
v___y_1178_ = v___x_1204_;
v___y_1179_ = v_val_1201_;
v___y_1180_ = v___x_1206_;
v___y_1181_ = v___x_1205_;
v_val_1182_ = v___x_1213_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
v_a_1216_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1207_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1207_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 0);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v___y_1178_ = v___x_1204_;
v___y_1179_ = v_val_1201_;
v___y_1180_ = v___x_1206_;
v___y_1181_ = v___x_1205_;
v_val_1182_ = v___x_1221_;
goto v___jp_1177_;
}
}
}
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_a_1200_);
lean_dec_ref(v_src_1154_);
lean_dec_ref(v_remoteUrl_1153_);
lean_dec_ref(v_relPkgDir_1152_);
lean_dec_ref(v_dep_1148_);
v___x_1224_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_1225_ = lean_string_append(v_name_1151_, v___x_1224_);
v___x_1226_ = lean_string_append(v___x_1225_, v_pkgDir_1198_);
lean_dec_ref(v_pkgDir_1198_);
v___x_1227_ = 3;
v___x_1228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*1, v___x_1227_);
lean_inc_ref(v_a_1155_);
v___x_1229_ = lean_apply_2(v_a_1155_, v___x_1228_, lean_box(0));
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
v___jp_1235_:
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1237_ == 0)
{
v_a_1200_ = v_val_1236_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1865__overap_1241_; lean_object* v___x_1242_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1865__overap_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1232_, v___f_1176_, v___x_1234_, v___x_1239_, v___x_1240_, v___x_1238_);
lean_inc_ref(v_a_1155_);
v___x_1242_ = lean_apply_2(v___x_1865__overap_1241_, v_a_1155_, lean_box(0));
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_dec_ref_known(v___x_1242_, 1);
v_a_1200_ = v_val_1236_;
goto v___jp_1199_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_val_1236_);
lean_dec_ref(v_pkgDir_1198_);
lean_dec_ref(v_src_1154_);
lean_dec_ref(v_remoteUrl_1153_);
lean_dec_ref(v_relPkgDir_1152_);
lean_dec_ref(v_name_1151_);
lean_dec_ref(v_dep_1148_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object* v_dep_1256_, lean_object* v_inherited_1257_, lean_object* v_wsDir_1258_, lean_object* v_name_1259_, lean_object* v_relPkgDir_1260_, lean_object* v_remoteUrl_1261_, lean_object* v_src_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
uint8_t v_inherited_boxed_1265_; lean_object* v_res_1266_; 
v_inherited_boxed_1265_ = lean_unbox(v_inherited_1257_);
v_res_1266_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(v_dep_1256_, v_inherited_boxed_1265_, v_wsDir_1258_, v_name_1259_, v_relPkgDir_1260_, v_remoteUrl_1261_, v_src_1262_, v_a_1263_);
lean_dec_ref(v_a_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object* v_a_1267_, lean_object* v_name_1268_, lean_object* v_repo_1269_, lean_object* v_url_1270_, lean_object* v_rev_x3f_1271_){
_start:
{
lean_object* v___y_1283_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1355_; lean_object* v___y_1356_; uint8_t v_a_1357_; lean_object* v___y_1365_; uint8_t v_a_1366_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v_val_1378_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v_val_1438_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v_a_1450_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v_a_1497_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1602_; uint8_t v_a_1603_; lean_object* v___y_1611_; uint8_t v_a_1612_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; uint8_t v_val_1623_; uint8_t v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1633_; uint8_t v___y_1638_; lean_object* v___y_1639_; uint8_t v___y_1640_; lean_object* v___y_1641_; uint8_t v___y_1643_; lean_object* v___y_1644_; uint8_t v___y_1645_; uint8_t v___y_1674_; lean_object* v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; uint8_t v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v_a_1685_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; uint8_t v_val_1732_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v_a_1744_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v_a_1787_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; uint8_t v_a_1863_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v_a_1927_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v_a_1940_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v_val_1955_; lean_object* v___y_1963_; lean_object* v___y_1964_; uint8_t v_a_1965_; lean_object* v___y_1974_; 
if (lean_obj_tag(v_rev_x3f_1271_) == 0)
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lake_Git_upstreamBranch;
v___y_1974_ = v___x_1983_;
goto v___jp_1973_;
}
else
{
lean_object* v_val_1984_; 
v_val_1984_ = lean_ctor_get(v_rev_x3f_1271_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v_rev_x3f_1271_, 1);
v___y_1974_ = v_val_1984_;
goto v___jp_1973_;
}
v___jp_1273_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
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
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1286_ = l_Lake_GitRepo_gcAuto(v_repo_1269_, v___x_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_a_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
v_a_1288_ = lean_ctor_get(v___x_1286_, 1);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1286_, 2);
v___x_1289_ = lean_array_get_size(v_a_1288_);
v___x_1290_ = lean_nat_dec_lt(v___x_1284_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
lean_dec(v_a_1288_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1287_);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_usize_of_nat(v___x_1289_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1288_, v___x_1293_, v___x_1294_, v___x_1292_, v___y_1283_);
lean_dec(v_a_1288_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v___x_1295_, 0);
lean_dec(v_unused_1303_);
v___x_1297_ = v___x_1295_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_dec(v___x_1295_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v_a_1287_);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1287_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_dec(v_a_1287_);
return v___x_1295_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1286_, 1);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1286_, 2);
v___x_1305_ = lean_array_get_size(v_a_1304_);
v___x_1306_ = lean_nat_dec_lt(v___x_1284_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec(v_a_1304_);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = lean_usize_of_nat(v___x_1305_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1304_, v___x_1310_, v___x_1311_, v___x_1309_, v___y_1283_);
lean_dec(v_a_1304_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v___x_1312_, 0);
lean_dec(v_unused_1320_);
v___x_1314_ = v___x_1312_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v___x_1312_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 1);
lean_ctor_set(v___x_1314_, 0, v___x_1309_);
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1309_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
return v___x_1312_;
}
}
}
}
v___jp_1321_:
{
if (lean_obj_tag(v___y_1323_) == 0)
{
lean_dec_ref_known(v___y_1323_, 1);
v___y_1283_ = v___y_1322_;
goto v___jp_1282_;
}
else
{
lean_dec_ref(v_repo_1269_);
return v___y_1323_;
}
}
v___jp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
lean_inc_ref(v___y_1326_);
v___x_1329_ = l_Lake_GitRepo_pruneRemote(v___y_1326_, v_repo_1269_, v___x_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 1);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 2);
v___x_1331_ = lean_array_get_size(v_a_1330_);
v___x_1332_ = lean_nat_dec_lt(v___x_1327_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_dec(v_a_1330_);
v___y_1283_ = v___y_1325_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = lean_usize_of_nat(v___x_1331_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1330_, v___x_1334_, v___x_1335_, v___x_1333_, v___y_1325_);
lean_dec(v_a_1330_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_dec_ref_known(v___x_1336_, 1);
v___y_1283_ = v___y_1325_;
goto v___jp_1282_;
}
else
{
v___y_1322_ = v___y_1325_;
v___y_1323_ = v___x_1336_;
goto v___jp_1321_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_a_1337_ = lean_ctor_get(v___x_1329_, 1);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1329_, 2);
v___x_1338_ = lean_array_get_size(v_a_1337_);
v___x_1339_ = lean_nat_dec_lt(v___x_1327_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec(v_a_1337_);
lean_dec_ref(v_repo_1269_);
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = lean_usize_of_nat(v___x_1338_);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1337_, v___x_1343_, v___x_1344_, v___x_1342_, v___y_1325_);
lean_dec(v_a_1337_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_repo_1269_);
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
lean_ctor_set_tag(v___x_1347_, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1342_);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1342_);
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
v___y_1322_ = v___y_1325_;
v___y_1323_ = v___x_1345_;
goto v___jp_1321_;
}
}
}
}
v___jp_1354_:
{
if (v_a_1357_ == 0)
{
lean_dec_ref(v_name_1268_);
v___y_1325_ = v___y_1355_;
v___y_1326_ = v___y_1356_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1358_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1359_ = lean_string_append(v_name_1268_, v___x_1358_);
v___x_1360_ = lean_string_append(v___x_1359_, v_repo_1269_);
v___x_1361_ = 2;
v___x_1362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*1, v___x_1361_);
lean_inc_ref(v___y_1355_);
v___x_1363_ = lean_apply_2(v___y_1355_, v___x_1362_, lean_box(0));
v___y_1325_ = v___y_1355_;
v___y_1326_ = v___y_1356_;
goto v___jp_1324_;
}
}
v___jp_1364_:
{
if (v_a_1366_ == 0)
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
goto v___jp_1279_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1367_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1368_ = lean_string_append(v_name_1268_, v___x_1367_);
v___x_1369_ = lean_string_append(v___x_1368_, v_repo_1269_);
lean_dec_ref(v_repo_1269_);
v___x_1370_ = 2;
v___x_1371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*1, v___x_1370_);
lean_inc_ref(v___y_1365_);
v___x_1372_ = lean_apply_2(v___y_1365_, v___x_1371_, lean_box(0));
goto v___jp_1279_;
}
}
v___jp_1373_:
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = lean_array_get_size(v___y_1376_);
v___x_1380_ = lean_nat_dec_lt(v___y_1377_, v___x_1379_);
if (v___x_1380_ == 0)
{
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___y_1375_;
v_a_1357_ = v_val_1378_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = lean_usize_of_nat(v___x_1379_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1376_, v___x_1382_, v___x_1383_, v___x_1381_, v___y_1374_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec_ref_known(v___x_1384_, 1);
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___y_1375_;
v_a_1357_ = v_val_1378_;
goto v___jp_1354_;
}
else
{
lean_dec_ref(v_name_1268_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec_ref_known(v___x_1384_, 1);
v___y_1325_ = v___y_1374_;
v___y_1326_ = v___y_1375_;
goto v___jp_1324_;
}
else
{
lean_dec_ref(v_repo_1269_);
return v___x_1384_;
}
}
}
}
v___jp_1385_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1391_ = l_Lake_GitRepo_hasNoDiff(v_repo_1269_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = 1;
v___y_1374_ = v___y_1386_;
v___y_1375_ = v___y_1387_;
v___y_1376_ = v___x_1390_;
v___y_1377_ = v___x_1389_;
v_val_1378_ = v___x_1392_;
goto v___jp_1373_;
}
else
{
v___y_1374_ = v___y_1386_;
v___y_1375_ = v___y_1387_;
v___y_1376_ = v___x_1390_;
v___y_1377_ = v___x_1389_;
v_val_1378_ = v___y_1388_;
goto v___jp_1373_;
}
}
v___jp_1393_:
{
if (lean_obj_tag(v___y_1397_) == 0)
{
lean_dec_ref_known(v___y_1397_, 1);
v___y_1386_ = v___y_1394_;
v___y_1387_ = v___y_1395_;
v___y_1388_ = v___y_1396_;
goto v___jp_1385_;
}
else
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1397_;
}
}
v___jp_1398_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1404_ = l_Lake_GitRepo_clean(v_repo_1269_, v___x_1403_);
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
v___y_1386_ = v___y_1399_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1401_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1406_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1405_, v___x_1409_, v___x_1410_, v___x_1408_, v___y_1399_);
lean_dec(v_a_1405_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref_known(v___x_1411_, 1);
v___y_1386_ = v___y_1399_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1401_;
goto v___jp_1385_;
}
else
{
v___y_1394_ = v___y_1399_;
v___y_1395_ = v___y_1400_;
v___y_1396_ = v___y_1401_;
v___y_1397_ = v___x_1411_;
goto v___jp_1393_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_a_1412_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1404_, 2);
v___x_1413_ = lean_array_get_size(v_a_1412_);
v___x_1414_ = lean_nat_dec_lt(v___x_1402_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec(v_a_1412_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = lean_usize_of_nat(v___x_1413_);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1412_, v___x_1418_, v___x_1419_, v___x_1417_, v___y_1399_);
lean_dec(v_a_1412_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1428_);
v___x_1422_ = v___x_1420_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v___x_1420_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1417_);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1417_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
v___y_1394_ = v___y_1399_;
v___y_1395_ = v___y_1400_;
v___y_1396_ = v___y_1401_;
v___y_1397_ = v___x_1420_;
goto v___jp_1393_;
}
}
}
}
v___jp_1429_:
{
if (lean_obj_tag(v___y_1433_) == 0)
{
lean_dec_ref_known(v___y_1433_, 1);
v___y_1399_ = v___y_1430_;
v___y_1400_ = v___y_1431_;
v___y_1401_ = v___y_1432_;
goto v___jp_1398_;
}
else
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1433_;
}
}
v___jp_1434_:
{
lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_1439_ = lean_array_get_size(v___y_1435_);
v___x_1440_ = lean_nat_dec_lt(v___y_1437_, v___x_1439_);
if (v___x_1440_ == 0)
{
v___y_1365_ = v___y_1436_;
v_a_1366_ = v_val_1438_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1441_; size_t v___x_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1441_ = lean_box(0);
v___x_1442_ = ((size_t)0ULL);
v___x_1443_ = lean_usize_of_nat(v___x_1439_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1435_, v___x_1442_, v___x_1443_, v___x_1441_, v___y_1436_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_dec_ref_known(v___x_1444_, 1);
v___y_1365_ = v___y_1436_;
v_a_1366_ = v_val_1438_;
goto v___jp_1364_;
}
else
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_dec_ref_known(v___x_1444_, 1);
goto v___jp_1279_;
}
else
{
return v___x_1444_;
}
}
}
}
v___jp_1445_:
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_1452_ = l_Option_instDecidableEq___redArg(v___x_1451_, v_a_1450_, v___y_1446_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1453_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1268_);
v___x_1454_ = lean_string_append(v_name_1268_, v___x_1453_);
v___x_1455_ = lean_string_append(v___x_1454_, v___y_1449_);
v___x_1456_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1457_ = lean_string_append(v___x_1455_, v___x_1456_);
v___x_1458_ = 1;
v___x_1459_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*1, v___x_1458_);
lean_inc_ref(v___y_1447_);
v___x_1460_ = lean_apply_2(v___y_1447_, v___x_1459_, lean_box(0));
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1463_ = l_Lake_GitRepo_checkoutDetach(v___y_1449_, v_repo_1269_, v___x_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 2);
v___x_1465_ = lean_array_get_size(v_a_1464_);
v___x_1466_ = lean_nat_dec_lt(v___x_1461_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v_a_1464_);
v___y_1399_ = v___y_1447_;
v___y_1400_ = v___y_1448_;
v___y_1401_ = v___x_1452_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1465_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1464_, v___x_1468_, v___x_1469_, v___x_1467_, v___y_1447_);
lean_dec(v_a_1464_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_dec_ref_known(v___x_1470_, 1);
v___y_1399_ = v___y_1447_;
v___y_1400_ = v___y_1448_;
v___y_1401_ = v___x_1452_;
goto v___jp_1398_;
}
else
{
v___y_1430_ = v___y_1447_;
v___y_1431_ = v___y_1448_;
v___y_1432_ = v___x_1452_;
v___y_1433_ = v___x_1470_;
goto v___jp_1429_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_a_1471_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1463_, 2);
v___x_1472_ = lean_array_get_size(v_a_1471_);
v___x_1473_ = lean_nat_dec_lt(v___x_1461_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_a_1471_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = lean_usize_of_nat(v___x_1472_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1471_, v___x_1477_, v___x_1478_, v___x_1476_, v___y_1447_);
lean_dec(v_a_1471_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1479_, 0);
lean_dec(v_unused_1487_);
v___x_1481_ = v___x_1479_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v___x_1479_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 1);
lean_ctor_set(v___x_1481_, 0, v___x_1476_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1476_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
v___y_1430_ = v___y_1447_;
v___y_1431_ = v___y_1448_;
v___y_1432_ = v___x_1452_;
v___y_1433_ = v___x_1479_;
goto v___jp_1429_;
}
}
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
lean_dec_ref(v___y_1449_);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1490_ = l_Lake_GitRepo_hasNoDiff(v_repo_1269_);
if (v___x_1490_ == 0)
{
v___y_1435_ = v___x_1489_;
v___y_1436_ = v___y_1447_;
v___y_1437_ = v___x_1488_;
v_val_1438_ = v___x_1452_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1491_; 
v___x_1491_ = 0;
v___y_1435_ = v___x_1489_;
v___y_1436_ = v___y_1447_;
v___y_1437_ = v___x_1488_;
v_val_1438_ = v___x_1491_;
goto v___jp_1434_;
}
}
}
v___jp_1492_:
{
if (lean_obj_tag(v_a_1497_) == 1)
{
lean_object* v_val_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
lean_dec_ref(v___y_1496_);
lean_dec_ref(v___y_1494_);
v_val_1498_ = lean_ctor_get(v_a_1497_, 0);
lean_inc(v_val_1498_);
v___x_1499_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1500_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1269_);
v___x_1501_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1500_, v_repo_1269_);
v___x_1502_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1502_ == 0)
{
v___y_1446_ = v_a_1497_;
v___y_1447_ = v___y_1493_;
v___y_1448_ = v___y_1495_;
v___y_1449_ = v_val_1498_;
v_a_1450_ = v___x_1501_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1503_; size_t v___x_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1499_, v___x_1504_, v___x_1505_, v___x_1503_, v___y_1493_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_dec_ref_known(v___x_1506_, 1);
v___y_1446_ = v_a_1497_;
v___y_1447_ = v___y_1493_;
v___y_1448_ = v___y_1495_;
v___y_1449_ = v_val_1498_;
v_a_1450_ = v___x_1501_;
goto v___jp_1445_;
}
else
{
lean_dec(v___x_1501_);
lean_dec(v_val_1498_);
lean_dec_ref_known(v_a_1497_, 1);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1506_;
}
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v_a_1497_);
lean_dec_ref(v_repo_1269_);
v___x_1507_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__1));
v___x_1508_ = lean_string_append(v_name_1268_, v___x_1507_);
v___x_1509_ = lean_string_append(v___x_1508_, v___y_1496_);
lean_dec_ref(v___y_1496_);
v___x_1510_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__2));
v___x_1511_ = lean_string_append(v___x_1509_, v___x_1510_);
v___x_1512_ = lean_string_append(v___x_1511_, v___y_1494_);
lean_dec_ref(v___y_1494_);
v___x_1513_ = 3;
v___x_1514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*1, v___x_1513_);
lean_inc_ref(v___y_1493_);
v___x_1515_ = lean_apply_2(v___y_1493_, v___x_1514_, lean_box(0));
v___x_1516_ = lean_box(0);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
v___jp_1518_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1523_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__3));
lean_inc_ref(v_name_1268_);
v___x_1524_ = lean_string_append(v_name_1268_, v___x_1523_);
v___x_1525_ = lean_string_append(v___x_1524_, v___y_1521_);
v___x_1526_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__4));
v___x_1527_ = lean_string_append(v___x_1525_, v___x_1526_);
v___x_1528_ = lean_string_append(v___x_1527_, v___y_1519_);
v___x_1529_ = 1;
v___x_1530_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*1, v___x_1529_);
lean_inc_ref(v___y_1522_);
v___x_1531_ = lean_apply_2(v___y_1522_, v___x_1530_, lean_box(0));
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v___y_1521_);
lean_inc_ref(v___y_1520_);
lean_inc_ref(v_repo_1269_);
v___x_1534_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_1269_, v___y_1520_, v___y_1521_, v___x_1533_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_a_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
v_a_1536_ = lean_ctor_get(v___x_1534_, 1);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1534_, 2);
v___x_1537_ = lean_array_get_size(v_a_1536_);
v___x_1538_ = lean_nat_dec_lt(v___x_1532_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec(v_a_1536_);
v___y_1493_ = v___y_1522_;
v___y_1494_ = v___y_1519_;
v___y_1495_ = v___y_1520_;
v___y_1496_ = v___y_1521_;
v_a_1497_ = v_a_1535_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = lean_usize_of_nat(v___x_1537_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1536_, v___x_1540_, v___x_1541_, v___x_1539_, v___y_1522_);
lean_dec(v_a_1536_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_dec_ref_known(v___x_1542_, 1);
v___y_1493_ = v___y_1522_;
v___y_1494_ = v___y_1519_;
v___y_1495_ = v___y_1520_;
v___y_1496_ = v___y_1521_;
v_a_1497_ = v_a_1535_;
goto v___jp_1492_;
}
else
{
lean_dec(v_a_1535_);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1542_;
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
lean_dec_ref(v___y_1521_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_a_1543_ = lean_ctor_get(v___x_1534_, 1);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1534_, 2);
v___x_1544_ = lean_array_get_size(v_a_1543_);
v___x_1545_ = lean_nat_dec_lt(v___x_1532_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_a_1543_);
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = lean_usize_of_nat(v___x_1544_);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1543_, v___x_1549_, v___x_1550_, v___x_1548_, v___y_1522_);
lean_dec(v_a_1543_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1559_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 1);
lean_ctor_set(v___x_1553_, 0, v___x_1548_);
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1548_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
return v___x_1551_;
}
}
}
}
v___jp_1560_:
{
if (lean_obj_tag(v___y_1564_) == 0)
{
lean_dec_ref_known(v___y_1564_, 1);
v___y_1519_ = v___y_1562_;
v___y_1520_ = v___y_1561_;
v___y_1521_ = v___y_1563_;
v___y_1522_ = v_a_1267_;
goto v___jp_1518_;
}
else
{
lean_dec_ref(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1564_;
}
}
v___jp_1565_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
lean_inc_ref(v___y_1566_);
lean_inc_ref(v___y_1567_);
v___x_1571_ = l_Lake_GitRepo_addRemote(v___y_1567_, v___y_1566_, v_repo_1269_, v___x_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 2);
v___x_1573_ = lean_array_get_size(v_a_1572_);
v___x_1574_ = lean_nat_dec_lt(v___x_1569_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_dec(v_a_1572_);
v___y_1519_ = v___y_1566_;
v___y_1520_ = v___y_1567_;
v___y_1521_ = v___y_1568_;
v___y_1522_ = v_a_1267_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1575_; size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = lean_usize_of_nat(v___x_1573_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1572_, v___x_1576_, v___x_1577_, v___x_1575_, v_a_1267_);
lean_dec(v_a_1572_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_dec_ref_known(v___x_1578_, 1);
v___y_1519_ = v___y_1566_;
v___y_1520_ = v___y_1567_;
v___y_1521_ = v___y_1568_;
v___y_1522_ = v_a_1267_;
goto v___jp_1518_;
}
else
{
v___y_1561_ = v___y_1567_;
v___y_1562_ = v___y_1566_;
v___y_1563_ = v___y_1568_;
v___y_1564_ = v___x_1578_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_a_1579_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1571_, 2);
v___x_1580_ = lean_array_get_size(v_a_1579_);
v___x_1581_ = lean_nat_dec_lt(v___x_1569_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_a_1579_);
lean_dec_ref(v___y_1568_);
lean_dec_ref(v___y_1566_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = lean_usize_of_nat(v___x_1580_);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1579_, v___x_1585_, v___x_1586_, v___x_1584_, v_a_1267_);
lean_dec(v_a_1579_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v___y_1568_);
lean_dec_ref(v___y_1566_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v___x_1587_, 0);
lean_dec(v_unused_1595_);
v___x_1589_ = v___x_1587_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v___x_1587_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1584_);
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1584_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
v___y_1561_ = v___y_1567_;
v___y_1562_ = v___y_1566_;
v___y_1563_ = v___y_1568_;
v___y_1564_ = v___x_1587_;
goto v___jp_1560_;
}
}
}
}
v___jp_1596_:
{
if (lean_obj_tag(v___y_1600_) == 0)
{
lean_dec_ref_known(v___y_1600_, 1);
v___y_1566_ = v___y_1598_;
v___y_1567_ = v___y_1597_;
v___y_1568_ = v___y_1599_;
goto v___jp_1565_;
}
else
{
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1600_;
}
}
v___jp_1601_:
{
if (v_a_1603_ == 0)
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
goto v___jp_1276_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1604_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1605_ = lean_string_append(v_name_1268_, v___x_1604_);
v___x_1606_ = lean_string_append(v___x_1605_, v_repo_1269_);
lean_dec_ref(v_repo_1269_);
v___x_1607_ = 2;
v___x_1608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*1, v___x_1607_);
lean_inc_ref(v___y_1602_);
v___x_1609_ = lean_apply_2(v___y_1602_, v___x_1608_, lean_box(0));
goto v___jp_1276_;
}
}
v___jp_1610_:
{
if (v_a_1612_ == 0)
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
goto v___jp_1273_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1613_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkDiff___closed__0));
v___x_1614_ = lean_string_append(v_name_1268_, v___x_1613_);
v___x_1615_ = lean_string_append(v___x_1614_, v_repo_1269_);
lean_dec_ref(v_repo_1269_);
v___x_1616_ = 2;
v___x_1617_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*1, v___x_1616_);
lean_inc_ref(v___y_1611_);
v___x_1618_ = lean_apply_2(v___y_1611_, v___x_1617_, lean_box(0));
goto v___jp_1273_;
}
}
v___jp_1619_:
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = lean_array_get_size(v___y_1622_);
v___x_1625_ = lean_nat_dec_lt(v___y_1621_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1602_ = v___y_1620_;
v_a_1603_ = v_val_1623_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1626_ = lean_box(0);
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = lean_usize_of_nat(v___x_1624_);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1622_, v___x_1627_, v___x_1628_, v___x_1626_, v___y_1620_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_dec_ref_known(v___x_1629_, 1);
v___y_1602_ = v___y_1620_;
v_a_1603_ = v_val_1623_;
goto v___jp_1601_;
}
else
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_dec_ref_known(v___x_1629_, 1);
goto v___jp_1276_;
}
else
{
return v___x_1629_;
}
}
}
}
v___jp_1630_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1636_ = l_Lake_GitRepo_hasNoDiff(v_repo_1269_);
if (v___x_1636_ == 0)
{
v___y_1620_ = v___y_1632_;
v___y_1621_ = v___x_1634_;
v___y_1622_ = v___x_1635_;
v_val_1623_ = v___y_1631_;
goto v___jp_1619_;
}
else
{
v___y_1620_ = v___y_1632_;
v___y_1621_ = v___x_1634_;
v___y_1622_ = v___x_1635_;
v_val_1623_ = v___y_1633_;
goto v___jp_1619_;
}
}
v___jp_1637_:
{
if (lean_obj_tag(v___y_1641_) == 0)
{
lean_dec_ref_known(v___y_1641_, 1);
v___y_1631_ = v___y_1638_;
v___y_1632_ = v___y_1639_;
v___y_1633_ = v___y_1640_;
goto v___jp_1630_;
}
else
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1641_;
}
}
v___jp_1642_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1648_ = l_Lake_GitRepo_clean(v_repo_1269_, v___x_1647_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 1);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 2);
v___x_1650_ = lean_array_get_size(v_a_1649_);
v___x_1651_ = lean_nat_dec_lt(v___x_1646_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec(v_a_1649_);
v___y_1631_ = v___y_1643_;
v___y_1632_ = v___y_1644_;
v___y_1633_ = v___y_1645_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = ((size_t)0ULL);
v___x_1654_ = lean_usize_of_nat(v___x_1650_);
v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1649_, v___x_1653_, v___x_1654_, v___x_1652_, v___y_1644_);
lean_dec(v_a_1649_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_dec_ref_known(v___x_1655_, 1);
v___y_1631_ = v___y_1643_;
v___y_1632_ = v___y_1644_;
v___y_1633_ = v___y_1645_;
goto v___jp_1630_;
}
else
{
v___y_1638_ = v___y_1643_;
v___y_1639_ = v___y_1644_;
v___y_1640_ = v___y_1645_;
v___y_1641_ = v___x_1655_;
goto v___jp_1637_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_a_1656_ = lean_ctor_get(v___x_1648_, 1);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1648_, 2);
v___x_1657_ = lean_array_get_size(v_a_1656_);
v___x_1658_ = lean_nat_dec_lt(v___x_1646_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v_a_1656_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; size_t v___x_1662_; size_t v___x_1663_; lean_object* v___x_1664_; 
v___x_1661_ = lean_box(0);
v___x_1662_ = ((size_t)0ULL);
v___x_1663_ = lean_usize_of_nat(v___x_1657_);
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1656_, v___x_1662_, v___x_1663_, v___x_1661_, v___y_1644_);
lean_dec(v_a_1656_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v___x_1664_, 0);
lean_dec(v_unused_1672_);
v___x_1666_ = v___x_1664_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v___x_1664_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 1);
lean_ctor_set(v___x_1666_, 0, v___x_1661_);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1661_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
v___y_1638_ = v___y_1643_;
v___y_1639_ = v___y_1644_;
v___y_1640_ = v___y_1645_;
v___y_1641_ = v___x_1664_;
goto v___jp_1637_;
}
}
}
}
v___jp_1673_:
{
if (lean_obj_tag(v___y_1677_) == 0)
{
lean_dec_ref_known(v___y_1677_, 1);
v___y_1643_ = v___y_1674_;
v___y_1644_ = v___y_1675_;
v___y_1645_ = v___y_1676_;
goto v___jp_1642_;
}
else
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1677_;
}
}
v___jp_1678_:
{
if (lean_obj_tag(v_a_1685_) == 0)
{
v___y_1519_ = v___y_1681_;
v___y_1520_ = v___y_1680_;
v___y_1521_ = v___y_1684_;
v___y_1522_ = v___y_1682_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1726_; 
v_isSharedCheck_1726_ = !lean_is_exclusive(v_a_1685_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_a_1685_, 0);
lean_dec(v_unused_1727_);
v___x_1687_ = v_a_1685_;
v_isShared_1688_ = v_isSharedCheck_1726_;
goto v_resetjp_1686_;
}
else
{
lean_dec(v_a_1685_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1726_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
if (v___y_1679_ == 0)
{
lean_del_object(v___x_1687_);
v___y_1519_ = v___y_1681_;
v___y_1520_ = v___y_1680_;
v___y_1521_ = v___y_1684_;
v___y_1522_ = v___y_1682_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec_ref(v___y_1681_);
v___x_1689_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__0));
lean_inc_ref(v_name_1268_);
v___x_1690_ = lean_string_append(v_name_1268_, v___x_1689_);
v___x_1691_ = lean_string_append(v___x_1690_, v___y_1684_);
v___x_1692_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_checkout___closed__1));
v___x_1693_ = lean_string_append(v___x_1691_, v___x_1692_);
v___x_1694_ = 1;
v___x_1695_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*1, v___x_1694_);
lean_inc_ref(v___y_1682_);
v___x_1696_ = lean_apply_2(v___y_1682_, v___x_1695_, lean_box(0));
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1699_ = l_Lake_GitRepo_checkoutDetach(v___y_1684_, v_repo_1269_, v___x_1698_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
lean_del_object(v___x_1687_);
v_a_1700_ = lean_ctor_get(v___x_1699_, 1);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 2);
v___x_1701_ = lean_array_get_size(v_a_1700_);
v___x_1702_ = lean_nat_dec_lt(v___x_1697_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_dec(v_a_1700_);
v___y_1643_ = v___y_1679_;
v___y_1644_ = v___y_1682_;
v___y_1645_ = v___y_1683_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = lean_usize_of_nat(v___x_1701_);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1700_, v___x_1704_, v___x_1705_, v___x_1703_, v___y_1682_);
lean_dec(v_a_1700_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_dec_ref_known(v___x_1706_, 1);
v___y_1643_ = v___y_1679_;
v___y_1644_ = v___y_1682_;
v___y_1645_ = v___y_1683_;
goto v___jp_1642_;
}
else
{
v___y_1674_ = v___y_1679_;
v___y_1675_ = v___y_1682_;
v___y_1676_ = v___y_1683_;
v___y_1677_ = v___x_1706_;
goto v___jp_1673_;
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
lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_dec(v_a_1707_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1710_ = lean_box(0);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1710_);
v___x_1712_ = v___x_1687_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
else
{
lean_object* v___x_1714_; size_t v___x_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
lean_del_object(v___x_1687_);
v___x_1714_ = lean_box(0);
v___x_1715_ = ((size_t)0ULL);
v___x_1716_ = lean_usize_of_nat(v___x_1708_);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1707_, v___x_1715_, v___x_1716_, v___x_1714_, v___y_1682_);
lean_dec(v_a_1707_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v___x_1717_, 0);
lean_dec(v_unused_1725_);
v___x_1719_ = v___x_1717_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v___x_1717_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 1);
lean_ctor_set(v___x_1719_, 0, v___x_1714_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1714_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
v___y_1674_ = v___y_1679_;
v___y_1675_ = v___y_1682_;
v___y_1676_ = v___y_1683_;
v___y_1677_ = v___x_1717_;
goto v___jp_1673_;
}
}
}
}
}
}
}
v___jp_1728_:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = lean_array_get_size(v___y_1729_);
v___x_1734_ = lean_nat_dec_lt(v___y_1731_, v___x_1733_);
if (v___x_1734_ == 0)
{
v___y_1611_ = v___y_1730_;
v_a_1612_ = v_val_1732_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1735_; size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = ((size_t)0ULL);
v___x_1737_ = lean_usize_of_nat(v___x_1733_);
v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1729_, v___x_1736_, v___x_1737_, v___x_1735_, v___y_1730_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref_known(v___x_1738_, 1);
v___y_1611_ = v___y_1730_;
v_a_1612_ = v_val_1732_;
goto v___jp_1610_;
}
else
{
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref_known(v___x_1738_, 1);
goto v___jp_1273_;
}
else
{
return v___x_1738_;
}
}
}
}
v___jp_1739_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v___y_1743_);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___y_1743_);
v___x_1747_ = l_Option_instDecidableEq___redArg(v___x_1745_, v_a_1744_, v___x_1746_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; 
v___x_1748_ = l_Lake_GitRev_isFullSha1(v___y_1743_);
if (v___x_1748_ == 0)
{
v___y_1519_ = v___y_1740_;
v___y_1520_ = v___y_1741_;
v___y_1521_ = v___y_1743_;
v___y_1522_ = v___y_1742_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
lean_inc_ref(v___y_1743_);
v___x_1750_ = l_Lake_GitRepo_findCommit_x3f(v___y_1743_, v_repo_1269_);
v___x_1751_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1751_ == 0)
{
v___y_1679_ = v___x_1748_;
v___y_1680_ = v___y_1741_;
v___y_1681_ = v___y_1740_;
v___y_1682_ = v___y_1742_;
v___y_1683_ = v___x_1747_;
v___y_1684_ = v___y_1743_;
v_a_1685_ = v___x_1750_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1752_; size_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1752_ = lean_box(0);
v___x_1753_ = ((size_t)0ULL);
v___x_1754_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1749_, v___x_1753_, v___x_1754_, v___x_1752_, v___y_1742_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref_known(v___x_1755_, 1);
v___y_1679_ = v___x_1748_;
v___y_1680_ = v___y_1741_;
v___y_1681_ = v___y_1740_;
v___y_1682_ = v___y_1742_;
v___y_1683_ = v___x_1747_;
v___y_1684_ = v___y_1743_;
v_a_1685_ = v___x_1750_;
goto v___jp_1678_;
}
else
{
lean_dec(v___x_1750_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1755_;
}
}
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
lean_dec_ref(v___y_1743_);
lean_dec_ref(v___y_1740_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1758_ = l_Lake_GitRepo_hasNoDiff(v_repo_1269_);
if (v___x_1758_ == 0)
{
v___y_1729_ = v___x_1757_;
v___y_1730_ = v___y_1742_;
v___y_1731_ = v___x_1756_;
v_val_1732_ = v___x_1747_;
goto v___jp_1728_;
}
else
{
uint8_t v___x_1759_; 
v___x_1759_ = 0;
v___y_1729_ = v___x_1757_;
v___y_1730_ = v___y_1742_;
v___y_1731_ = v___x_1756_;
v_val_1732_ = v___x_1759_;
goto v___jp_1728_;
}
}
}
v___jp_1760_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1765_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1766_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__0));
lean_inc_ref(v_repo_1269_);
v___x_1767_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1766_, v_repo_1269_);
v___x_1768_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1768_ == 0)
{
v___y_1740_ = v___y_1762_;
v___y_1741_ = v___y_1761_;
v___y_1742_ = v___y_1764_;
v___y_1743_ = v___y_1763_;
v_a_1744_ = v___x_1767_;
goto v___jp_1739_;
}
else
{
lean_object* v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_box(0);
v___x_1770_ = ((size_t)0ULL);
v___x_1771_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1765_, v___x_1770_, v___x_1771_, v___x_1769_, v___y_1764_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_dec_ref_known(v___x_1772_, 1);
v___y_1740_ = v___y_1762_;
v___y_1741_ = v___y_1761_;
v___y_1742_ = v___y_1764_;
v___y_1743_ = v___y_1763_;
v_a_1744_ = v___x_1767_;
goto v___jp_1739_;
}
else
{
lean_dec(v___x_1767_);
lean_dec_ref(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1772_;
}
}
}
v___jp_1773_:
{
if (lean_obj_tag(v___y_1777_) == 0)
{
lean_dec_ref_known(v___y_1777_, 1);
v___y_1761_ = v___y_1775_;
v___y_1762_ = v___y_1774_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v_a_1267_;
goto v___jp_1760_;
}
else
{
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1777_;
}
}
v___jp_1778_:
{
if (lean_obj_tag(v___y_1782_) == 0)
{
lean_dec_ref_known(v___y_1782_, 1);
v___y_1761_ = v___y_1780_;
v___y_1762_ = v___y_1779_;
v___y_1763_ = v___y_1781_;
v___y_1764_ = v_a_1267_;
goto v___jp_1760_;
}
else
{
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___y_1782_;
}
}
v___jp_1783_:
{
if (lean_obj_tag(v_a_1787_) == 1)
{
lean_object* v_val_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1831_; 
v_val_1788_ = lean_ctor_get(v_a_1787_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1790_ = v_a_1787_;
v_isShared_1791_ = v_isSharedCheck_1831_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_val_1788_);
lean_dec(v_a_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1831_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_string_dec_eq(v_val_1788_, v___y_1785_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1793_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__5));
lean_inc_ref(v_name_1268_);
v___x_1794_ = lean_string_append(v_name_1268_, v___x_1793_);
v___x_1795_ = lean_string_append(v___x_1794_, v_val_1788_);
lean_dec(v_val_1788_);
v___x_1796_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__6));
v___x_1797_ = lean_string_append(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_string_append(v___x_1797_, v___y_1785_);
v___x_1799_ = 1;
v___x_1800_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1, v___x_1799_);
lean_inc_ref(v_a_1267_);
v___x_1801_ = lean_apply_2(v_a_1267_, v___x_1800_, lean_box(0));
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
lean_inc_ref(v___y_1785_);
lean_inc_ref(v___y_1784_);
v___x_1804_ = l_Lake_GitRepo_setRemoteUrl(v___y_1784_, v___y_1785_, v_repo_1269_, v___x_1803_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
lean_del_object(v___x_1790_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 2);
v___x_1806_ = lean_array_get_size(v_a_1805_);
v___x_1807_ = lean_nat_dec_lt(v___x_1802_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec(v_a_1805_);
v___y_1761_ = v___y_1784_;
v___y_1762_ = v___y_1785_;
v___y_1763_ = v___y_1786_;
v___y_1764_ = v_a_1267_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1808_; size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_box(0);
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = lean_usize_of_nat(v___x_1806_);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1805_, v___x_1809_, v___x_1810_, v___x_1808_, v_a_1267_);
lean_dec(v_a_1805_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref_known(v___x_1811_, 1);
v___y_1761_ = v___y_1784_;
v___y_1762_ = v___y_1785_;
v___y_1763_ = v___y_1786_;
v___y_1764_ = v_a_1267_;
goto v___jp_1760_;
}
else
{
v___y_1779_ = v___y_1785_;
v___y_1780_ = v___y_1784_;
v___y_1781_ = v___y_1786_;
v___y_1782_ = v___x_1811_;
goto v___jp_1778_;
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_a_1812_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1804_, 2);
v___x_1813_ = lean_array_get_size(v_a_1812_);
v___x_1814_ = lean_nat_dec_lt(v___x_1802_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec(v_a_1812_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1815_ = lean_box(0);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1815_);
v___x_1817_ = v___x_1790_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
else
{
lean_object* v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
lean_del_object(v___x_1790_);
v___x_1819_ = lean_box(0);
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1813_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1812_, v___x_1820_, v___x_1821_, v___x_1819_, v_a_1267_);
lean_dec(v_a_1812_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v___x_1822_, 0);
lean_dec(v_unused_1830_);
v___x_1824_ = v___x_1822_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_dec(v___x_1822_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 1);
lean_ctor_set(v___x_1824_, 0, v___x_1819_);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1819_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
v___y_1779_ = v___y_1785_;
v___y_1780_ = v___y_1784_;
v___y_1781_ = v___y_1786_;
v___y_1782_ = v___x_1822_;
goto v___jp_1778_;
}
}
}
}
else
{
lean_del_object(v___x_1790_);
lean_dec(v_val_1788_);
v___y_1761_ = v___y_1784_;
v___y_1762_ = v___y_1785_;
v___y_1763_ = v___y_1786_;
v___y_1764_ = v_a_1267_;
goto v___jp_1760_;
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v_a_1787_);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
lean_inc_ref(v___y_1785_);
lean_inc_ref(v___y_1784_);
v___x_1834_ = l_Lake_GitRepo_addRemote(v___y_1784_, v___y_1785_, v_repo_1269_, v___x_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 1);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 2);
v___x_1836_ = lean_array_get_size(v_a_1835_);
v___x_1837_ = lean_nat_dec_lt(v___x_1832_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_dec(v_a_1835_);
v___y_1761_ = v___y_1784_;
v___y_1762_ = v___y_1785_;
v___y_1763_ = v___y_1786_;
v___y_1764_ = v_a_1267_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1838_; size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = lean_usize_of_nat(v___x_1836_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1835_, v___x_1839_, v___x_1840_, v___x_1838_, v_a_1267_);
lean_dec(v_a_1835_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_dec_ref_known(v___x_1841_, 1);
v___y_1761_ = v___y_1784_;
v___y_1762_ = v___y_1785_;
v___y_1763_ = v___y_1786_;
v___y_1764_ = v_a_1267_;
goto v___jp_1760_;
}
else
{
v___y_1774_ = v___y_1785_;
v___y_1775_ = v___y_1784_;
v___y_1776_ = v___y_1786_;
v___y_1777_ = v___x_1841_;
goto v___jp_1773_;
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1834_, 1);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1834_, 2);
v___x_1843_ = lean_array_get_size(v_a_1842_);
v___x_1844_ = lean_nat_dec_lt(v___x_1832_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_a_1842_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1847_ = lean_box(0);
v___x_1848_ = ((size_t)0ULL);
v___x_1849_ = lean_usize_of_nat(v___x_1843_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1842_, v___x_1848_, v___x_1849_, v___x_1847_, v_a_1267_);
lean_dec(v_a_1842_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1858_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 1);
lean_ctor_set(v___x_1852_, 0, v___x_1847_);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1847_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
v___y_1774_ = v___y_1785_;
v___y_1775_ = v___y_1784_;
v___y_1776_ = v___y_1786_;
v___y_1777_ = v___x_1850_;
goto v___jp_1773_;
}
}
}
}
}
v___jp_1859_:
{
if (v_a_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__7));
lean_inc_ref(v_name_1268_);
v___x_1865_ = lean_string_append(v_name_1268_, v___x_1864_);
v___x_1866_ = 1;
v___x_1867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*1, v___x_1866_);
lean_inc_ref(v_a_1267_);
v___x_1868_ = lean_apply_2(v_a_1267_, v___x_1867_, lean_box(0));
lean_inc_ref(v_repo_1269_);
v___x_1869_ = l_IO_FS_createDirAll(v_repo_1269_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1903_);
v___x_1871_ = v___x_1869_;
v_isShared_1872_ = v_isSharedCheck_1902_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v___x_1869_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1902_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
v___x_1875_ = l_Lake_GitRepo_quietInit(v_repo_1269_, v___x_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
lean_del_object(v___x_1871_);
v_a_1876_ = lean_ctor_get(v___x_1875_, 1);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 2);
v___x_1877_ = lean_array_get_size(v_a_1876_);
v___x_1878_ = lean_nat_dec_lt(v___x_1873_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_dec(v_a_1876_);
v___y_1566_ = v___y_1861_;
v___y_1567_ = v___y_1860_;
v___y_1568_ = v___y_1862_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1879_; size_t v___x_1880_; size_t v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = ((size_t)0ULL);
v___x_1881_ = lean_usize_of_nat(v___x_1877_);
v___x_1882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1876_, v___x_1880_, v___x_1881_, v___x_1879_, v_a_1267_);
lean_dec(v_a_1876_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_dec_ref_known(v___x_1882_, 1);
v___y_1566_ = v___y_1861_;
v___y_1567_ = v___y_1860_;
v___y_1568_ = v___y_1862_;
goto v___jp_1565_;
}
else
{
v___y_1597_ = v___y_1860_;
v___y_1598_ = v___y_1861_;
v___y_1599_ = v___y_1862_;
v___y_1600_ = v___x_1882_;
goto v___jp_1596_;
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_a_1883_ = lean_ctor_get(v___x_1875_, 1);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1875_, 2);
v___x_1884_ = lean_array_get_size(v_a_1883_);
v___x_1885_ = lean_nat_dec_lt(v___x_1873_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_dec(v_a_1883_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v___x_1886_ = lean_box(0);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 1);
lean_ctor_set(v___x_1871_, 0, v___x_1886_);
v___x_1888_ = v___x_1871_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
else
{
lean_object* v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
lean_del_object(v___x_1871_);
v___x_1890_ = lean_box(0);
v___x_1891_ = ((size_t)0ULL);
v___x_1892_ = lean_usize_of_nat(v___x_1884_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_1883_, v___x_1891_, v___x_1892_, v___x_1890_, v_a_1267_);
lean_dec(v_a_1883_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v___x_1893_, 0);
lean_dec(v_unused_1901_);
v___x_1895_ = v___x_1893_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_dec(v___x_1893_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
lean_ctor_set(v___x_1895_, 0, v___x_1890_);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1890_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
else
{
v___y_1597_ = v___y_1860_;
v___y_1598_ = v___y_1861_;
v___y_1599_ = v___y_1862_;
v___y_1600_ = v___x_1893_;
goto v___jp_1596_;
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
v_a_1904_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1906_ = v___x_1869_;
v_isShared_1907_ = v_isSharedCheck_1916_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1869_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1916_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1908_ = lean_io_error_to_string(v_a_1904_);
v___x_1909_ = 3;
v___x_1910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set_uint8(v___x_1910_, sizeof(void*)*1, v___x_1909_);
lean_inc_ref(v_a_1267_);
v___x_1911_ = lean_apply_2(v_a_1267_, v___x_1910_, lean_box(0));
v___x_1912_ = lean_box(0);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1912_);
v___x_1914_ = v___x_1906_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_repo_1269_);
lean_inc_ref(v___y_1860_);
v___x_1918_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___y_1860_, v_repo_1269_);
v___x_1919_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1919_ == 0)
{
v___y_1784_ = v___y_1860_;
v___y_1785_ = v___y_1861_;
v___y_1786_ = v___y_1862_;
v_a_1787_ = v___x_1918_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1920_; size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = ((size_t)0ULL);
v___x_1922_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1917_, v___x_1921_, v___x_1922_, v___x_1920_, v_a_1267_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_dec_ref_known(v___x_1923_, 1);
v___y_1784_ = v___y_1860_;
v___y_1785_ = v___y_1861_;
v___y_1786_ = v___y_1862_;
v_a_1787_ = v___x_1918_;
goto v___jp_1783_;
}
else
{
lean_dec(v___x_1918_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1923_;
}
}
}
}
v___jp_1924_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1928_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1929_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___closed__8));
lean_inc_ref(v_repo_1269_);
v___x_1930_ = l_System_FilePath_join(v_repo_1269_, v___x_1929_);
v___x_1931_ = l_System_FilePath_pathExists(v___x_1930_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1932_ == 0)
{
v___y_1860_ = v___y_1925_;
v___y_1861_ = v_a_1927_;
v___y_1862_ = v___y_1926_;
v_a_1863_ = v___x_1931_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1933_ = lean_box(0);
v___x_1934_ = ((size_t)0ULL);
v___x_1935_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1928_, v___x_1934_, v___x_1935_, v___x_1933_, v_a_1267_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v___y_1860_ = v___y_1925_;
v___y_1861_ = v_a_1927_;
v___y_1862_ = v___y_1926_;
v_a_1863_ = v___x_1931_;
goto v___jp_1859_;
}
else
{
lean_dec_ref(v_a_1927_);
lean_dec_ref(v___y_1926_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1936_;
}
}
}
v___jp_1937_:
{
if (lean_obj_tag(v_a_1940_) == 1)
{
lean_object* v_val_1941_; 
lean_dec_ref(v_url_1270_);
v_val_1941_ = lean_ctor_get(v_a_1940_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_a_1940_, 1);
v___y_1925_ = v___y_1938_;
v___y_1926_ = v___y_1939_;
v_a_1927_ = v_val_1941_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_a_1940_);
lean_dec_ref(v___y_1939_);
lean_dec_ref(v_repo_1269_);
v___x_1942_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__0));
v___x_1943_ = lean_string_append(v_name_1268_, v___x_1942_);
v___x_1944_ = lean_string_append(v___x_1943_, v_url_1270_);
lean_dec_ref(v_url_1270_);
v___x_1945_ = 3;
v___x_1946_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set_uint8(v___x_1946_, sizeof(void*)*1, v___x_1945_);
lean_inc_ref(v_a_1267_);
v___x_1947_ = lean_apply_2(v_a_1267_, v___x_1946_, lean_box(0));
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
}
v___jp_1950_:
{
lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = lean_array_get_size(v___y_1952_);
v___x_1957_ = lean_nat_dec_lt(v___y_1953_, v___x_1956_);
if (v___x_1957_ == 0)
{
v___y_1938_ = v___y_1951_;
v___y_1939_ = v___y_1954_;
v_a_1940_ = v_val_1955_;
goto v___jp_1937_;
}
else
{
lean_object* v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_box(0);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = lean_usize_of_nat(v___x_1956_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_1952_, v___x_1959_, v___x_1960_, v___x_1958_, v_a_1267_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref_known(v___x_1961_, 1);
v___y_1938_ = v___y_1951_;
v___y_1939_ = v___y_1954_;
v_a_1940_ = v_val_1955_;
goto v___jp_1937_;
}
else
{
lean_dec(v_val_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_url_1270_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1961_;
}
}
}
v___jp_1962_:
{
if (v_a_1965_ == 0)
{
v___y_1925_ = v___y_1963_;
v___y_1926_ = v___y_1964_;
v_a_1927_ = v_url_1270_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_url_1270_);
v___x_1968_ = l_Lake_resolvePath(v_url_1270_);
v___x_1969_ = lean_string_utf8_byte_size(v___x_1968_);
v___x_1970_ = lean_nat_dec_eq(v___x_1969_, v___x_1966_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1968_);
v___y_1951_ = v___y_1963_;
v___y_1952_ = v___x_1967_;
v___y_1953_ = v___x_1966_;
v___y_1954_ = v___y_1964_;
v_val_1955_ = v___x_1971_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1972_; 
lean_dec_ref(v___x_1968_);
v___x_1972_ = lean_box(0);
v___y_1951_ = v___y_1963_;
v___y_1952_ = v___x_1967_;
v___y_1953_ = v___x_1966_;
v___y_1954_ = v___y_1964_;
v_val_1955_ = v___x_1972_;
goto v___jp_1950_;
}
}
}
v___jp_1973_:
{
lean_object* v_remote_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; uint8_t v___x_1978_; 
v_remote_1975_ = l_Lake_Git_defaultRemote;
v___x_1976_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_1977_ = l_System_FilePath_pathExists(v_url_1270_);
v___x_1978_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_1978_ == 0)
{
v___y_1963_ = v_remote_1975_;
v___y_1964_ = v___y_1974_;
v_a_1965_ = v___x_1977_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1979_ = lean_box(0);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_1976_, v___x_1980_, v___x_1981_, v___x_1979_, v_a_1267_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_dec_ref_known(v___x_1982_, 1);
v___y_1963_ = v_remote_1975_;
v___y_1964_ = v___y_1974_;
v_a_1965_ = v___x_1977_;
goto v___jp_1962_;
}
else
{
lean_dec_ref(v___y_1974_);
lean_dec_ref(v_url_1270_);
lean_dec_ref(v_repo_1269_);
lean_dec_ref(v_name_1268_);
return v___x_1982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object* v_a_1985_, lean_object* v_name_1986_, lean_object* v_repo_1987_, lean_object* v_url_1988_, lean_object* v_rev_x3f_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_1985_, v_name_1986_, v_repo_1987_, v_url_1988_, v_rev_x3f_1989_);
lean_dec_ref(v_a_1985_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* v_dep_1992_, uint8_t v_inherited_1993_, lean_object* v_lakeEnv_1994_, lean_object* v_wsDir_1995_, lean_object* v_name_1996_, lean_object* v_relPkgDir_1997_, lean_object* v_gitUrl_1998_, lean_object* v_remoteUrl_1999_, lean_object* v_inputRev_x3f_2000_, lean_object* v_subDir_x3f_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_pkgUrlMap_2004_; lean_object* v_name_2005_; lean_object* v_scope_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2182_; 
v_pkgUrlMap_2004_ = lean_ctor_get(v_lakeEnv_1994_, 5);
v_name_2005_ = lean_ctor_get(v_dep_1992_, 0);
v_scope_2006_ = lean_ctor_get(v_dep_1992_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_dep_1992_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2183_ = lean_ctor_get(v_dep_1992_, 4);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_dep_1992_, 3);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_dep_1992_, 2);
lean_dec(v_unused_2185_);
v___x_2008_ = v_dep_1992_;
v_isShared_2009_ = v_isSharedCheck_2182_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_scope_2006_);
lean_inc(v_name_2005_);
lean_dec(v_dep_1992_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2182_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v_a_2014_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v_val_2028_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v_a_2047_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v_val_2084_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2113_; lean_object* v_a_2114_; lean_object* v_gitDir_2117_; lean_object* v___y_2119_; lean_object* v___x_2180_; 
lean_inc_ref(v_relPkgDir_1997_);
lean_inc_ref(v_wsDir_1995_);
v_gitDir_2117_ = l_Lake_joinRelative(v_wsDir_1995_, v_relPkgDir_1997_);
v___x_2180_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2004_, v_name_2005_);
if (lean_obj_tag(v___x_2180_) == 0)
{
v___y_2119_ = v_gitUrl_1998_;
goto v___jp_2118_;
}
else
{
lean_object* v_val_2181_; 
lean_dec_ref(v_gitUrl_1998_);
v_val_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___y_2119_ = v_val_2181_;
goto v___jp_2118_;
}
v___jp_2010_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2015_ = l_Lake_defaultConfigFile;
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2017_, 0, v_name_2005_);
lean_ctor_set(v___x_2017_, 1, v_scope_2006_);
lean_ctor_set(v___x_2017_, 2, v___x_2015_);
lean_ctor_set(v___x_2017_, 3, v___x_2016_);
lean_ctor_set(v___x_2017_, 4, v___y_2012_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*5, v_inherited_1993_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v___x_2017_);
lean_ctor_set(v___x_2008_, 3, v_a_2014_);
lean_ctor_set(v___x_2008_, 2, v_remoteUrl_1999_);
lean_ctor_set(v___x_2008_, 1, v___y_2011_);
lean_ctor_set(v___x_2008_, 0, v___y_2013_);
v___x_2019_ = v___x_2008_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___y_2013_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___y_2011_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_remoteUrl_1999_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
v___jp_2022_:
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = lean_array_get_size(v___y_2023_);
v___x_2030_ = lean_nat_dec_lt(v___y_2024_, v___x_2029_);
if (v___x_2030_ == 0)
{
v___y_2011_ = v___y_2025_;
v___y_2012_ = v___y_2026_;
v___y_2013_ = v___y_2027_;
v_a_2014_ = v_val_2028_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2031_ = lean_box(0);
v___x_2032_ = ((size_t)0ULL);
v___x_2033_ = lean_usize_of_nat(v___x_2029_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2023_, v___x_2032_, v___x_2033_, v___x_2031_, v_a_2002_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_dec_ref_known(v___x_2034_, 1);
v___y_2011_ = v___y_2025_;
v___y_2012_ = v___y_2026_;
v___y_2013_ = v___y_2027_;
v_a_2014_ = v_val_2028_;
goto v___jp_2010_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_val_2028_);
lean_dec_ref(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_scope_2006_);
lean_dec(v_name_2005_);
lean_dec_ref(v_remoteUrl_1999_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
v___jp_2043_:
{
if (lean_obj_tag(v_a_2047_) == 1)
{
lean_object* v_val_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v___y_2045_);
lean_dec_ref(v_name_1996_);
v_val_2048_ = lean_ctor_get(v_a_2047_, 0);
lean_inc_n(v_val_2048_, 2);
lean_dec_ref_known(v_a_2047_, 1);
v___x_2049_ = l_Lake_defaultManifestFile;
v___x_2050_ = l_Lake_joinRelative(v_val_2048_, v___x_2049_);
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2053_ = l_Lake_Manifest_load(v___x_2050_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 1);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
v___y_2023_ = v___x_2052_;
v___y_2024_ = v___x_2051_;
v___y_2025_ = v___y_2044_;
v___y_2026_ = v___y_2046_;
v___y_2027_ = v_val_2048_;
v_val_2028_ = v___x_2059_;
goto v___jp_2022_;
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
v_a_2062_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2053_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2053_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 0);
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v___y_2023_ = v___x_2052_;
v___y_2024_ = v___x_2051_;
v___y_2025_ = v___y_2044_;
v___y_2026_ = v___y_2046_;
v___y_2027_ = v_val_2048_;
v_val_2028_ = v___x_2067_;
goto v___jp_2022_;
}
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v_a_2047_);
lean_dec_ref(v___y_2046_);
lean_dec_ref(v___y_2044_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_scope_2006_);
lean_dec(v_name_2005_);
lean_dec_ref(v_remoteUrl_1999_);
v___x_2070_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2071_ = lean_string_append(v_name_1996_, v___x_2070_);
v___x_2072_ = lean_string_append(v___x_2071_, v___y_2045_);
lean_dec_ref(v___y_2045_);
v___x_2073_ = 3;
v___x_2074_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*1, v___x_2073_);
lean_inc_ref(v_a_2002_);
v___x_2075_ = lean_apply_2(v_a_2002_, v___x_2074_, lean_box(0));
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
v___jp_2078_:
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_array_get_size(v___y_2083_);
v___x_2086_ = lean_nat_dec_lt(v___y_2081_, v___x_2085_);
if (v___x_2086_ == 0)
{
v___y_2044_ = v___y_2079_;
v___y_2045_ = v___y_2080_;
v___y_2046_ = v___y_2082_;
v_a_2047_ = v_val_2084_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = lean_box(0);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = lean_usize_of_nat(v___x_2085_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2083_, v___x_2088_, v___x_2089_, v___x_2087_, v_a_2002_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_dec_ref_known(v___x_2090_, 1);
v___y_2044_ = v___y_2079_;
v___y_2045_ = v___y_2080_;
v___y_2046_ = v___y_2082_;
v_a_2047_ = v_val_2084_;
goto v___jp_2043_;
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_val_2084_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_scope_2006_);
lean_dec(v_name_2005_);
lean_dec_ref(v_remoteUrl_1999_);
lean_dec_ref(v_name_1996_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
v___jp_2099_:
{
lean_object* v___x_2103_; lean_object* v_pkgDir_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2103_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2103_, 0, v___y_2101_);
lean_ctor_set(v___x_2103_, 1, v___y_2100_);
lean_ctor_set(v___x_2103_, 2, v_inputRev_x3f_2000_);
lean_ctor_set(v___x_2103_, 3, v_subDir_x3f_2001_);
lean_inc_ref(v___y_2102_);
v_pkgDir_2104_ = l_Lake_joinRelative(v_wsDir_1995_, v___y_2102_);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2104_);
v___x_2107_ = l_Lake_resolvePath(v_pkgDir_2104_);
v___x_2108_ = lean_string_utf8_byte_size(v___x_2107_);
v___x_2109_ = lean_nat_dec_eq(v___x_2108_, v___x_2105_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2107_);
v___y_2079_ = v___y_2102_;
v___y_2080_ = v_pkgDir_2104_;
v___y_2081_ = v___x_2105_;
v___y_2082_ = v___x_2103_;
v___y_2083_ = v___x_2106_;
v_val_2084_ = v___x_2110_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2111_; 
lean_dec_ref(v___x_2107_);
v___x_2111_ = lean_box(0);
v___y_2079_ = v___y_2102_;
v___y_2080_ = v_pkgDir_2104_;
v___y_2081_ = v___x_2105_;
v___y_2082_ = v___x_2103_;
v___y_2083_ = v___x_2106_;
v_val_2084_ = v___x_2111_;
goto v___jp_2078_;
}
}
v___jp_2112_:
{
if (lean_obj_tag(v_subDir_x3f_2001_) == 1)
{
lean_object* v_val_2115_; lean_object* v___x_2116_; 
v_val_2115_ = lean_ctor_get(v_subDir_x3f_2001_, 0);
lean_inc(v_val_2115_);
v___x_2116_ = l_Lake_joinRelative(v_relPkgDir_1997_, v_val_2115_);
v___y_2100_ = v_a_2114_;
v___y_2101_ = v___y_2113_;
v___y_2102_ = v___x_2116_;
goto v___jp_2099_;
}
else
{
v___y_2100_ = v_a_2114_;
v___y_2101_ = v___y_2113_;
v___y_2102_ = v_relPkgDir_1997_;
goto v___jp_2099_;
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; 
lean_inc(v_inputRev_x3f_2000_);
lean_inc_ref(v___y_2119_);
lean_inc_ref(v_gitDir_2117_);
lean_inc_ref(v_name_1996_);
v___x_2120_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2002_, v_name_1996_, v_gitDir_2117_, v___y_2119_, v_inputRev_x3f_2000_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2170_; 
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2120_, 0);
lean_dec(v_unused_2171_);
v___x_2122_ = v___x_2120_;
v_isShared_2123_ = v_isSharedCheck_2170_;
goto v_resetjp_2121_;
}
else
{
lean_dec(v___x_2120_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2170_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2126_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2117_, v___x_2125_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v_a_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
lean_del_object(v___x_2122_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
v_a_2128_ = lean_ctor_get(v___x_2126_, 1);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2126_, 2);
v___x_2129_ = lean_array_get_size(v_a_2128_);
v___x_2130_ = lean_nat_dec_lt(v___x_2124_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_dec(v_a_2128_);
v___y_2113_ = v___y_2119_;
v_a_2114_ = v_a_2127_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = lean_usize_of_nat(v___x_2129_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2128_, v___x_2132_, v___x_2133_, v___x_2131_, v_a_2002_);
lean_dec(v_a_2128_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_dec_ref_known(v___x_2134_, 1);
v___y_2113_ = v___y_2119_;
v_a_2114_ = v_a_2127_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v_a_2127_);
lean_dec_ref(v___y_2119_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_scope_2006_);
lean_dec(v_name_2005_);
lean_dec(v_subDir_x3f_2001_);
lean_dec(v_inputRev_x3f_2000_);
lean_dec_ref(v_remoteUrl_1999_);
lean_dec_ref(v_relPkgDir_1997_);
lean_dec_ref(v_name_1996_);
lean_dec_ref(v_wsDir_1995_);
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
lean_dec_ref(v___y_2119_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_scope_2006_);
lean_dec(v_name_2005_);
lean_dec(v_subDir_x3f_2001_);
lean_dec(v_inputRev_x3f_2000_);
lean_dec_ref(v_remoteUrl_1999_);
lean_dec_ref(v_relPkgDir_1997_);
lean_dec_ref(v_name_1996_);
lean_dec_ref(v_wsDir_1995_);
v_a_2143_ = lean_ctor_get(v___x_2126_, 1);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2126_, 2);
v___x_2144_ = lean_array_get_size(v_a_2143_);
v___x_2145_ = lean_nat_dec_lt(v___x_2124_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_a_2143_);
v___x_2146_ = lean_box(0);
if (v_isShared_2123_ == 0)
{
lean_ctor_set_tag(v___x_2122_, 1);
lean_ctor_set(v___x_2122_, 0, v___x_2146_);
v___x_2148_ = v___x_2122_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
else
{
lean_object* v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; lean_object* v___x_2153_; 
lean_del_object(v___x_2122_);
v___x_2150_ = lean_box(0);
v___x_2151_ = ((size_t)0ULL);
v___x_2152_ = lean_usize_of_nat(v___x_2144_);
v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2143_, v___x_2151_, v___x_2152_, v___x_2150_, v_a_2002_);
lean_dec(v_a_2143_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2153_, 0);
lean_dec(v_unused_2161_);
v___x_2155_ = v___x_2153_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v___x_2153_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2150_);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2150_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
v_a_2162_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2153_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2153_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_gitDir_2117_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_scope_2006_);
lean_dec(v_name_2005_);
lean_dec(v_subDir_x3f_2001_);
lean_dec(v_inputRev_x3f_2000_);
lean_dec_ref(v_remoteUrl_1999_);
lean_dec_ref(v_relPkgDir_1997_);
lean_dec_ref(v_name_1996_);
lean_dec_ref(v_wsDir_1995_);
v_a_2172_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2120_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2120_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object* v_dep_2186_, lean_object* v_inherited_2187_, lean_object* v_lakeEnv_2188_, lean_object* v_wsDir_2189_, lean_object* v_name_2190_, lean_object* v_relPkgDir_2191_, lean_object* v_gitUrl_2192_, lean_object* v_remoteUrl_2193_, lean_object* v_inputRev_x3f_2194_, lean_object* v_subDir_x3f_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
uint8_t v_inherited_boxed_2198_; lean_object* v_res_2199_; 
v_inherited_boxed_2198_ = lean_unbox(v_inherited_2187_);
v_res_2199_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(v_dep_2186_, v_inherited_boxed_2198_, v_lakeEnv_2188_, v_wsDir_2189_, v_name_2190_, v_relPkgDir_2191_, v_gitUrl_2192_, v_remoteUrl_2193_, v_inputRev_x3f_2194_, v_subDir_x3f_2195_, v_a_2196_);
lean_dec_ref(v_a_2196_);
lean_dec_ref(v_lakeEnv_2188_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object* v_a_2200_, lean_object* v_dep_2201_, uint8_t v_inherited_2202_, lean_object* v_lakeEnv_2203_, lean_object* v_wsDir_2204_, lean_object* v_name_2205_, lean_object* v_relPkgDir_2206_, lean_object* v_gitUrl_2207_, lean_object* v_remoteUrl_2208_, lean_object* v_inputRev_x3f_2209_, lean_object* v_subDir_x3f_2210_){
_start:
{
lean_object* v_pkgUrlMap_2212_; lean_object* v_name_2213_; lean_object* v_scope_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2390_; 
v_pkgUrlMap_2212_ = lean_ctor_get(v_lakeEnv_2203_, 5);
v_name_2213_ = lean_ctor_get(v_dep_2201_, 0);
v_scope_2214_ = lean_ctor_get(v_dep_2201_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_dep_2201_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; lean_object* v_unused_2392_; lean_object* v_unused_2393_; 
v_unused_2391_ = lean_ctor_get(v_dep_2201_, 4);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_dep_2201_, 3);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_dep_2201_, 2);
lean_dec(v_unused_2393_);
v___x_2216_ = v_dep_2201_;
v_isShared_2217_ = v_isSharedCheck_2390_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_scope_2214_);
lean_inc(v_name_2213_);
lean_dec(v_dep_2201_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2390_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v_a_2222_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v_val_2236_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v_a_2255_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v_val_2292_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2321_; lean_object* v_a_2322_; lean_object* v_gitDir_2325_; lean_object* v___y_2327_; lean_object* v___x_2388_; 
lean_inc_ref(v_relPkgDir_2206_);
lean_inc_ref(v_wsDir_2204_);
v_gitDir_2325_ = l_Lake_joinRelative(v_wsDir_2204_, v_relPkgDir_2206_);
v___x_2388_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_2212_, v_name_2213_);
if (lean_obj_tag(v___x_2388_) == 0)
{
v___y_2327_ = v_gitUrl_2207_;
goto v___jp_2326_;
}
else
{
lean_object* v_val_2389_; 
lean_dec_ref(v_gitUrl_2207_);
v_val_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_val_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___y_2327_ = v_val_2389_;
goto v___jp_2326_;
}
v___jp_2218_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2223_ = l_Lake_defaultConfigFile;
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2225_, 0, v_name_2213_);
lean_ctor_set(v___x_2225_, 1, v_scope_2214_);
lean_ctor_set(v___x_2225_, 2, v___x_2223_);
lean_ctor_set(v___x_2225_, 3, v___x_2224_);
lean_ctor_set(v___x_2225_, 4, v___y_2220_);
lean_ctor_set_uint8(v___x_2225_, sizeof(void*)*5, v_inherited_2202_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 4, v___x_2225_);
lean_ctor_set(v___x_2216_, 3, v_a_2222_);
lean_ctor_set(v___x_2216_, 2, v_remoteUrl_2208_);
lean_ctor_set(v___x_2216_, 1, v___y_2219_);
lean_ctor_set(v___x_2216_, 0, v___y_2221_);
v___x_2227_ = v___x_2216_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___y_2221_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___y_2219_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_remoteUrl_2208_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_a_2222_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
v___jp_2230_:
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_array_get_size(v___y_2235_);
v___x_2238_ = lean_nat_dec_lt(v___y_2232_, v___x_2237_);
if (v___x_2238_ == 0)
{
v___y_2219_ = v___y_2231_;
v___y_2220_ = v___y_2233_;
v___y_2221_ = v___y_2234_;
v_a_2222_ = v_val_2236_;
goto v___jp_2218_;
}
else
{
lean_object* v___x_2239_; size_t v___x_2240_; size_t v___x_2241_; lean_object* v___x_2242_; 
v___x_2239_ = lean_box(0);
v___x_2240_ = ((size_t)0ULL);
v___x_2241_ = lean_usize_of_nat(v___x_2237_);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2235_, v___x_2240_, v___x_2241_, v___x_2239_, v_a_2200_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_dec_ref_known(v___x_2242_, 1);
v___y_2219_ = v___y_2231_;
v___y_2220_ = v___y_2233_;
v___y_2221_ = v___y_2234_;
v_a_2222_ = v_val_2236_;
goto v___jp_2218_;
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref(v_val_2236_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___y_2231_);
lean_del_object(v___x_2216_);
lean_dec_ref(v_scope_2214_);
lean_dec(v_name_2213_);
lean_dec_ref(v_remoteUrl_2208_);
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
v___jp_2251_:
{
if (lean_obj_tag(v_a_2255_) == 1)
{
lean_object* v_val_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_name_2205_);
v_val_2256_ = lean_ctor_get(v_a_2255_, 0);
lean_inc_n(v_val_2256_, 2);
lean_dec_ref_known(v_a_2255_, 1);
v___x_2257_ = l_Lake_defaultManifestFile;
v___x_2258_ = l_Lake_joinRelative(v_val_2256_, v___x_2257_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2261_ = l_Lake_Manifest_load(v___x_2258_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 1);
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
v___y_2231_ = v___y_2252_;
v___y_2232_ = v___x_2259_;
v___y_2233_ = v___y_2254_;
v___y_2234_ = v_val_2256_;
v___y_2235_ = v___x_2260_;
v_val_2236_ = v___x_2267_;
goto v___jp_2230_;
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
v_a_2270_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2261_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2261_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 0);
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
v___y_2231_ = v___y_2252_;
v___y_2232_ = v___x_2259_;
v___y_2233_ = v___y_2254_;
v___y_2234_ = v_val_2256_;
v___y_2235_ = v___x_2260_;
v_val_2236_ = v___x_2275_;
goto v___jp_2230_;
}
}
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec(v_a_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v___y_2252_);
lean_del_object(v___x_2216_);
lean_dec_ref(v_scope_2214_);
lean_dec(v_name_2213_);
lean_dec_ref(v_remoteUrl_2208_);
v___x_2278_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2279_ = lean_string_append(v_name_2205_, v___x_2278_);
v___x_2280_ = lean_string_append(v___x_2279_, v___y_2253_);
lean_dec_ref(v___y_2253_);
v___x_2281_ = 3;
v___x_2282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*1, v___x_2281_);
lean_inc_ref(v_a_2200_);
v___x_2283_ = lean_apply_2(v_a_2200_, v___x_2282_, lean_box(0));
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
}
v___jp_2286_:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_array_get_size(v___y_2289_);
v___x_2294_ = lean_nat_dec_lt(v___y_2287_, v___x_2293_);
if (v___x_2294_ == 0)
{
v___y_2252_ = v___y_2288_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v_a_2255_ = v_val_2292_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2295_; size_t v___x_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = lean_box(0);
v___x_2296_ = ((size_t)0ULL);
v___x_2297_ = lean_usize_of_nat(v___x_2293_);
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2289_, v___x_2296_, v___x_2297_, v___x_2295_, v_a_2200_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_dec_ref_known(v___x_2298_, 1);
v___y_2252_ = v___y_2288_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v_a_2255_ = v_val_2292_;
goto v___jp_2251_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_val_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec_ref(v___y_2288_);
lean_del_object(v___x_2216_);
lean_dec_ref(v_scope_2214_);
lean_dec(v_name_2213_);
lean_dec_ref(v_remoteUrl_2208_);
lean_dec_ref(v_name_2205_);
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
v___jp_2307_:
{
lean_object* v___x_2311_; lean_object* v_pkgDir_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2311_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2311_, 0, v___y_2308_);
lean_ctor_set(v___x_2311_, 1, v___y_2309_);
lean_ctor_set(v___x_2311_, 2, v_inputRev_x3f_2209_);
lean_ctor_set(v___x_2311_, 3, v_subDir_x3f_2210_);
lean_inc_ref(v___y_2310_);
v_pkgDir_2312_ = l_Lake_joinRelative(v_wsDir_2204_, v___y_2310_);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2312_);
v___x_2315_ = l_Lake_resolvePath(v_pkgDir_2312_);
v___x_2316_ = lean_string_utf8_byte_size(v___x_2315_);
v___x_2317_ = lean_nat_dec_eq(v___x_2316_, v___x_2313_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2315_);
v___y_2287_ = v___x_2313_;
v___y_2288_ = v___y_2310_;
v___y_2289_ = v___x_2314_;
v___y_2290_ = v_pkgDir_2312_;
v___y_2291_ = v___x_2311_;
v_val_2292_ = v___x_2318_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2319_; 
lean_dec_ref(v___x_2315_);
v___x_2319_ = lean_box(0);
v___y_2287_ = v___x_2313_;
v___y_2288_ = v___y_2310_;
v___y_2289_ = v___x_2314_;
v___y_2290_ = v_pkgDir_2312_;
v___y_2291_ = v___x_2311_;
v_val_2292_ = v___x_2319_;
goto v___jp_2286_;
}
}
v___jp_2320_:
{
if (lean_obj_tag(v_subDir_x3f_2210_) == 1)
{
lean_object* v_val_2323_; lean_object* v___x_2324_; 
v_val_2323_ = lean_ctor_get(v_subDir_x3f_2210_, 0);
lean_inc(v_val_2323_);
v___x_2324_ = l_Lake_joinRelative(v_relPkgDir_2206_, v_val_2323_);
v___y_2308_ = v___y_2321_;
v___y_2309_ = v_a_2322_;
v___y_2310_ = v___x_2324_;
goto v___jp_2307_;
}
else
{
v___y_2308_ = v___y_2321_;
v___y_2309_ = v_a_2322_;
v___y_2310_ = v_relPkgDir_2206_;
goto v___jp_2307_;
}
}
v___jp_2326_:
{
lean_object* v___x_2328_; 
lean_inc(v_inputRev_x3f_2209_);
lean_inc_ref(v___y_2327_);
lean_inc_ref(v_gitDir_2325_);
lean_inc_ref(v_name_2205_);
v___x_2328_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2200_, v_name_2205_, v_gitDir_2325_, v___y_2327_, v_inputRev_x3f_2209_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2378_; 
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v___x_2328_, 0);
lean_dec(v_unused_2379_);
v___x_2330_ = v___x_2328_;
v_isShared_2331_ = v_isSharedCheck_2378_;
goto v_resetjp_2329_;
}
else
{
lean_dec(v___x_2328_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2378_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2334_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_2325_, v___x_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v_a_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
lean_del_object(v___x_2330_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
v_a_2336_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2334_, 2);
v___x_2337_ = lean_array_get_size(v_a_2336_);
v___x_2338_ = lean_nat_dec_lt(v___x_2332_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec(v_a_2336_);
v___y_2321_ = v___y_2327_;
v_a_2322_ = v_a_2335_;
goto v___jp_2320_;
}
else
{
lean_object* v___x_2339_; size_t v___x_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = lean_box(0);
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = lean_usize_of_nat(v___x_2337_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2336_, v___x_2340_, v___x_2341_, v___x_2339_, v_a_2200_);
lean_dec(v_a_2336_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_dec_ref_known(v___x_2342_, 1);
v___y_2321_ = v___y_2327_;
v_a_2322_ = v_a_2335_;
goto v___jp_2320_;
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2335_);
lean_dec_ref(v___y_2327_);
lean_del_object(v___x_2216_);
lean_dec_ref(v_scope_2214_);
lean_dec(v_name_2213_);
lean_dec(v_subDir_x3f_2210_);
lean_dec(v_inputRev_x3f_2209_);
lean_dec_ref(v_remoteUrl_2208_);
lean_dec_ref(v_relPkgDir_2206_);
lean_dec_ref(v_name_2205_);
lean_dec_ref(v_wsDir_2204_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
lean_dec_ref(v___y_2327_);
lean_del_object(v___x_2216_);
lean_dec_ref(v_scope_2214_);
lean_dec(v_name_2213_);
lean_dec(v_subDir_x3f_2210_);
lean_dec(v_inputRev_x3f_2209_);
lean_dec_ref(v_remoteUrl_2208_);
lean_dec_ref(v_relPkgDir_2206_);
lean_dec_ref(v_name_2205_);
lean_dec_ref(v_wsDir_2204_);
v_a_2351_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2334_, 2);
v___x_2352_ = lean_array_get_size(v_a_2351_);
v___x_2353_ = lean_nat_dec_lt(v___x_2332_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec(v_a_2351_);
v___x_2354_ = lean_box(0);
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 1);
lean_ctor_set(v___x_2330_, 0, v___x_2354_);
v___x_2356_ = v___x_2330_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
else
{
lean_object* v___x_2358_; size_t v___x_2359_; size_t v___x_2360_; lean_object* v___x_2361_; 
lean_del_object(v___x_2330_);
v___x_2358_ = lean_box(0);
v___x_2359_ = ((size_t)0ULL);
v___x_2360_ = lean_usize_of_nat(v___x_2352_);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_2351_, v___x_2359_, v___x_2360_, v___x_2358_, v_a_2200_);
lean_dec(v_a_2351_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v___x_2361_, 0);
lean_dec(v_unused_2369_);
v___x_2363_ = v___x_2361_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v___x_2361_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2358_);
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2358_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2361_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2361_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v___y_2327_);
lean_dec_ref(v_gitDir_2325_);
lean_del_object(v___x_2216_);
lean_dec_ref(v_scope_2214_);
lean_dec(v_name_2213_);
lean_dec(v_subDir_x3f_2210_);
lean_dec(v_inputRev_x3f_2209_);
lean_dec_ref(v_remoteUrl_2208_);
lean_dec_ref(v_relPkgDir_2206_);
lean_dec_ref(v_name_2205_);
lean_dec_ref(v_wsDir_2204_);
v_a_2380_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2328_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2328_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* v_a_2394_, lean_object* v_dep_2395_, lean_object* v_inherited_2396_, lean_object* v_lakeEnv_2397_, lean_object* v_wsDir_2398_, lean_object* v_name_2399_, lean_object* v_relPkgDir_2400_, lean_object* v_gitUrl_2401_, lean_object* v_remoteUrl_2402_, lean_object* v_inputRev_x3f_2403_, lean_object* v_subDir_x3f_2404_, lean_object* v_a_2405_){
_start:
{
uint8_t v_inherited_boxed_2406_; lean_object* v_res_2407_; 
v_inherited_boxed_2406_ = lean_unbox(v_inherited_2396_);
v_res_2407_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2394_, v_dep_2395_, v_inherited_boxed_2406_, v_lakeEnv_2397_, v_wsDir_2398_, v_name_2399_, v_relPkgDir_2400_, v_gitUrl_2401_, v_remoteUrl_2402_, v_inputRev_x3f_2403_, v_subDir_x3f_2404_);
lean_dec_ref(v_lakeEnv_2397_);
lean_dec_ref(v_a_2394_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* v_ver_2411_, lean_object* v_as_2412_, size_t v_sz_2413_, size_t v_i_2414_, lean_object* v_b_2415_){
_start:
{
uint8_t v___x_2416_; 
v___x_2416_ = lean_usize_dec_lt(v_i_2414_, v_sz_2413_);
if (v___x_2416_ == 0)
{
lean_inc_ref(v_b_2415_);
return v_b_2415_;
}
else
{
lean_object* v_a_2417_; lean_object* v_version_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v_a_2417_ = lean_array_uget_borrowed(v_as_2412_, v_i_2414_);
v_version_2418_ = lean_ctor_get(v_a_2417_, 0);
v___x_2419_ = lean_box(0);
v___x_2420_ = l_Lake_VerRange_test(v_ver_2411_, v_version_2418_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; size_t v___x_2422_; size_t v___x_2423_; 
v___x_2421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2414_, v___x_2422_);
v_i_2414_ = v___x_2423_;
v_b_2415_ = v___x_2421_;
goto _start;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
lean_inc(v_a_2417_);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_a_2417_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v___x_2419_);
return v___x_2427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* v_ver_2428_, lean_object* v_as_2429_, lean_object* v_sz_2430_, lean_object* v_i_2431_, lean_object* v_b_2432_){
_start:
{
size_t v_sz_boxed_2433_; size_t v_i_boxed_2434_; lean_object* v_res_2435_; 
v_sz_boxed_2433_ = lean_unbox_usize(v_sz_2430_);
lean_dec(v_sz_2430_);
v_i_boxed_2434_ = lean_unbox_usize(v_i_2431_);
lean_dec(v_i_2431_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_2428_, v_as_2429_, v_sz_boxed_2433_, v_i_boxed_2434_, v_b_2432_);
lean_dec_ref(v_b_2432_);
lean_dec_ref(v_as_2429_);
lean_dec_ref(v_ver_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* v_dep_2445_, uint8_t v_inherited_2446_, lean_object* v_lakeEnv_2447_, lean_object* v_wsDir_2448_, lean_object* v_relPkgsDir_2449_, lean_object* v_relParentDir_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v_a_2479_; lean_object* v_src_x3f_2482_; 
v_src_x3f_2482_ = lean_ctor_get(v_dep_2445_, 3);
lean_inc(v_src_x3f_2482_);
if (lean_obj_tag(v_src_x3f_2482_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2607_; 
v_val_2483_ = lean_ctor_get(v_src_x3f_2482_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_src_x3f_2482_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2485_ = v_src_x3f_2482_;
v_isShared_2486_ = v_isSharedCheck_2607_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_val_2483_);
lean_dec(v_src_x3f_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2607_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
if (lean_obj_tag(v_val_2483_) == 0)
{
lean_object* v_name_2487_; lean_object* v_scope_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref(v_relPkgsDir_2449_);
lean_dec_ref(v_lakeEnv_2447_);
v_name_2487_ = lean_ctor_get(v_dep_2445_, 0);
v_scope_2488_ = lean_ctor_get(v_dep_2445_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_dep_2445_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; lean_object* v_unused_2592_; lean_object* v_unused_2593_; 
v_unused_2591_ = lean_ctor_get(v_dep_2445_, 4);
lean_dec(v_unused_2591_);
v_unused_2592_ = lean_ctor_get(v_dep_2445_, 3);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_dep_2445_, 2);
lean_dec(v_unused_2593_);
v___x_2490_ = v_dep_2445_;
v_isShared_2491_ = v_isSharedCheck_2590_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_scope_2488_);
lean_inc(v_name_2487_);
lean_dec(v_dep_2445_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2590_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_dir_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2589_; 
v_dir_2492_ = lean_ctor_get(v_val_2483_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_val_2483_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2494_ = v_val_2483_;
v_isShared_2495_ = v_isSharedCheck_2589_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_dir_2492_);
lean_dec(v_val_2483_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2589_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_relPkgDir_2496_; uint8_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v_relPkgDir_2496_ = l_Lake_joinRelative(v_relParentDir_2450_, v_dir_2492_);
v___x_2497_ = 0;
lean_inc(v_name_2487_);
v___x_2498_ = l_Lean_Name_toString(v_name_2487_, v___x_2497_);
v___x_2499_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_relPkgDir_2496_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v_relPkgDir_2496_);
v___x_2501_ = v___x_2494_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_relPkgDir_2496_);
v___x_2501_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___y_2503_; lean_object* v_a_2504_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v_val_2516_; lean_object* v_pkgDir_2531_; lean_object* v_a_2533_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v_val_2567_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
lean_inc_ref(v_relPkgDir_2496_);
v_pkgDir_2531_ = l_Lake_joinRelative(v_wsDir_2448_, v_relPkgDir_2496_);
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2531_);
v___x_2581_ = l_Lake_resolvePath(v_pkgDir_2531_);
v___x_2582_ = lean_string_utf8_byte_size(v___x_2581_);
v___x_2583_ = lean_nat_dec_eq(v___x_2582_, v___x_2564_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2585_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2581_);
v___x_2585_ = v___x_2485_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2581_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
v_val_2567_ = v___x_2585_;
goto v___jp_2566_;
}
}
else
{
lean_object* v___x_2587_; 
lean_dec_ref(v___x_2581_);
lean_del_object(v___x_2485_);
v___x_2587_ = lean_box(0);
v_val_2567_ = v___x_2587_;
goto v___jp_2566_;
}
v___jp_2502_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2505_ = l_Lake_defaultConfigFile;
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2507_, 0, v_name_2487_);
lean_ctor_set(v___x_2507_, 1, v_scope_2488_);
lean_ctor_set(v___x_2507_, 2, v___x_2505_);
lean_ctor_set(v___x_2507_, 3, v___x_2506_);
lean_ctor_set(v___x_2507_, 4, v___x_2501_);
lean_ctor_set_uint8(v___x_2507_, sizeof(void*)*5, v_inherited_2446_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 4, v___x_2507_);
lean_ctor_set(v___x_2490_, 3, v_a_2504_);
lean_ctor_set(v___x_2490_, 2, v___x_2499_);
lean_ctor_set(v___x_2490_, 1, v_relPkgDir_2496_);
lean_ctor_set(v___x_2490_, 0, v___y_2503_);
v___x_2509_ = v___x_2490_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___y_2503_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_relPkgDir_2496_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_a_2504_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
v___jp_2512_:
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = lean_array_get_size(v___y_2515_);
v___x_2518_ = lean_nat_dec_lt(v___y_2514_, v___x_2517_);
if (v___x_2518_ == 0)
{
v___y_2503_ = v___y_2513_;
v_a_2504_ = v_val_2516_;
goto v___jp_2502_;
}
else
{
lean_object* v___x_2519_; size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v___x_2519_ = lean_box(0);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = lean_usize_of_nat(v___x_2517_);
v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2515_, v___x_2520_, v___x_2521_, v___x_2519_, v_a_2451_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref_known(v___x_2522_, 1);
v___y_2503_ = v___y_2513_;
v_a_2504_ = v_val_2516_;
goto v___jp_2502_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v_val_2516_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v_relPkgDir_2496_);
lean_del_object(v___x_2490_);
lean_dec_ref(v_scope_2488_);
lean_dec(v_name_2487_);
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
v___jp_2532_:
{
if (lean_obj_tag(v_a_2533_) == 1)
{
lean_object* v_val_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v_pkgDir_2531_);
lean_dec_ref(v___x_2498_);
v_val_2534_ = lean_ctor_get(v_a_2533_, 0);
lean_inc_n(v_val_2534_, 2);
lean_dec_ref_known(v_a_2533_, 1);
v___x_2535_ = l_Lake_defaultManifestFile;
v___x_2536_ = l_Lake_joinRelative(v_val_2534_, v___x_2535_);
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2539_ = l_Lake_Manifest_load(v___x_2536_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 1);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
v___y_2513_ = v_val_2534_;
v___y_2514_ = v___x_2537_;
v___y_2515_ = v___x_2538_;
v_val_2516_ = v___x_2545_;
goto v___jp_2512_;
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
v_a_2548_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2539_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2539_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set_tag(v___x_2550_, 0);
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
v___y_2513_ = v_val_2534_;
v___y_2514_ = v___x_2537_;
v___y_2515_ = v___x_2538_;
v_val_2516_ = v___x_2553_;
goto v___jp_2512_;
}
}
}
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec(v_a_2533_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v_relPkgDir_2496_);
lean_del_object(v___x_2490_);
lean_dec_ref(v_scope_2488_);
lean_dec(v_name_2487_);
v___x_2556_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2557_ = lean_string_append(v___x_2498_, v___x_2556_);
v___x_2558_ = lean_string_append(v___x_2557_, v_pkgDir_2531_);
lean_dec_ref(v_pkgDir_2531_);
v___x_2559_ = 3;
v___x_2560_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*1, v___x_2559_);
lean_inc_ref(v_a_2451_);
v___x_2561_ = lean_apply_2(v_a_2451_, v___x_2560_, lean_box(0));
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
}
v___jp_2566_:
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2568_ == 0)
{
v_a_2533_ = v_val_2567_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2569_ = lean_box(0);
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2565_, v___x_2570_, v___x_2571_, v___x_2569_, v_a_2451_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_dec_ref_known(v___x_2572_, 1);
v_a_2533_ = v_val_2567_;
goto v___jp_2532_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_val_2567_);
lean_dec_ref(v_pkgDir_2531_);
lean_dec_ref(v___x_2501_);
lean_dec_ref(v___x_2498_);
lean_dec_ref(v_relPkgDir_2496_);
lean_del_object(v___x_2490_);
lean_dec_ref(v_scope_2488_);
lean_dec(v_name_2487_);
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
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
lean_object* v_name_2594_; lean_object* v_url_2595_; lean_object* v_rev_2596_; lean_object* v_subDir_2597_; lean_object* v___y_2599_; lean_object* v___x_2604_; 
lean_del_object(v___x_2485_);
lean_dec_ref(v_relParentDir_2450_);
v_name_2594_ = lean_ctor_get(v_dep_2445_, 0);
v_url_2595_ = lean_ctor_get(v_val_2483_, 0);
lean_inc_ref_n(v_url_2595_, 2);
v_rev_2596_ = lean_ctor_get(v_val_2483_, 1);
lean_inc(v_rev_2596_);
v_subDir_2597_ = lean_ctor_get(v_val_2483_, 2);
lean_inc(v_subDir_2597_);
lean_dec_ref_known(v_val_2483_, 3);
v___x_2604_ = l_Lake_Git_filterUrl_x3f(v_url_2595_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; 
v___x_2605_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2599_ = v___x_2605_;
goto v___jp_2598_;
}
else
{
lean_object* v_val_2606_; 
v_val_2606_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_val_2606_);
lean_dec_ref_known(v___x_2604_, 1);
v___y_2599_ = v_val_2606_;
goto v___jp_2598_;
}
v___jp_2598_:
{
uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2600_ = 0;
lean_inc(v_name_2594_);
v___x_2601_ = l_Lean_Name_toString(v_name_2594_, v___x_2600_);
lean_inc_ref(v___x_2601_);
v___x_2602_ = l_Lake_joinRelative(v_relPkgsDir_2449_, v___x_2601_);
v___x_2603_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2451_, v_dep_2445_, v_inherited_2446_, v_lakeEnv_2447_, v_wsDir_2448_, v___x_2601_, v___x_2602_, v_url_2595_, v___y_2599_, v_rev_2596_, v_subDir_2597_);
lean_dec_ref(v_lakeEnv_2447_);
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_name_2608_; lean_object* v_scope_2609_; lean_object* v_version_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
lean_dec(v_src_x3f_2482_);
lean_dec_ref(v_relParentDir_2450_);
v_name_2608_ = lean_ctor_get(v_dep_2445_, 0);
v_scope_2609_ = lean_ctor_get(v_dep_2445_, 1);
v_version_2610_ = lean_ctor_get(v_dep_2445_, 2);
v___x_2611_ = lean_string_utf8_byte_size(v_scope_2609_);
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_nat_dec_eq(v___x_2611_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v___y_2616_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v_a_2638_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v_fst_2688_; lean_object* v_snd_2689_; lean_object* v_a_2705_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v_fst_2812_; lean_object* v_snd_2813_; 
lean_inc(v_name_2608_);
v___x_2614_ = l_Lean_Name_toString(v_name_2608_, v___x_2613_);
v___x_2809_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2609_);
lean_inc_ref(v_lakeEnv_2447_);
v___x_2810_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_2447_, v_scope_2609_, v___x_2614_, v___x_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2828_; lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2828_);
v_a_2829_ = lean_ctor_get(v___x_2810_, 1);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2810_, 2);
v___x_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_a_2828_);
v_fst_2812_ = v___x_2830_;
v_snd_2813_ = v_a_2829_;
goto v___jp_2811_;
}
else
{
lean_object* v_a_2831_; lean_object* v_a_2832_; lean_object* v___x_2833_; 
v_a_2831_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2831_);
v_a_2832_ = lean_ctor_get(v___x_2810_, 1);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2810_, 2);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2831_);
v_fst_2812_ = v___x_2833_;
v_snd_2813_ = v_a_2832_;
goto v___jp_2811_;
}
v___jp_2615_:
{
lean_object* v_toString_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_toString_2617_ = lean_ctor_get(v___y_2616_, 0);
lean_inc_ref(v_toString_2617_);
lean_dec_ref(v___y_2616_);
v___x_2618_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2619_ = lean_string_append(v_scope_2609_, v___x_2618_);
v___x_2620_ = lean_string_append(v___x_2619_, v___x_2614_);
lean_dec_ref(v___x_2614_);
v___x_2621_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__1));
v___x_2622_ = lean_string_append(v___x_2620_, v___x_2621_);
v___x_2623_ = lean_string_append(v___x_2622_, v_toString_2617_);
lean_dec_ref(v_toString_2617_);
v___x_2624_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__2));
v___x_2625_ = lean_string_append(v___x_2623_, v___x_2624_);
v___x_2626_ = 3;
v___x_2627_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*1, v___x_2626_);
lean_inc_ref(v_a_2451_);
v___x_2628_ = lean_apply_2(v_a_2451_, v___x_2627_, lean_box(0));
v___x_2629_ = lean_box(0);
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
v___jp_2631_:
{
if (lean_obj_tag(v_a_2638_) == 0)
{
lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2654_; 
lean_inc_ref(v_scope_2609_);
lean_dec_ref(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_a_2638_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_a_2638_, 0);
lean_dec(v_unused_2655_);
v___x_2640_ = v_a_2638_;
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
else
{
lean_dec(v_a_2638_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2642_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2643_ = lean_string_append(v_scope_2609_, v___x_2642_);
v___x_2644_ = lean_string_append(v___x_2643_, v___x_2614_);
lean_dec_ref(v___x_2614_);
v___x_2645_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__3));
v___x_2646_ = lean_string_append(v___x_2644_, v___x_2645_);
v___x_2647_ = 3;
v___x_2648_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2648_, 0, v___x_2646_);
lean_ctor_set_uint8(v___x_2648_, sizeof(void*)*1, v___x_2647_);
lean_inc_ref(v_a_2451_);
v___x_2649_ = lean_apply_2(v_a_2451_, v___x_2648_, lean_box(0));
v___x_2650_ = lean_box(0);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 1);
lean_ctor_set(v___x_2640_, 0, v___x_2650_);
v___x_2652_ = v___x_2640_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2657_; size_t v_sz_2658_; size_t v___x_2659_; lean_object* v___x_2660_; lean_object* v_fst_2661_; 
v_a_2656_ = lean_ctor_get(v_a_2638_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v_a_2638_, 1);
v___x_2657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0));
v_sz_2658_ = lean_array_size(v_a_2656_);
v___x_2659_ = ((size_t)0ULL);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_2637_, v_a_2656_, v_sz_2658_, v___x_2659_, v___x_2657_);
lean_dec(v_a_2656_);
v_fst_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_fst_2661_);
lean_dec_ref(v___x_2660_);
if (lean_obj_tag(v_fst_2661_) == 0)
{
lean_inc_ref(v_scope_2609_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v___y_2616_ = v___y_2637_;
goto v___jp_2615_;
}
else
{
lean_object* v_val_2662_; 
v_val_2662_ = lean_ctor_get(v_fst_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v_fst_2661_, 1);
if (lean_obj_tag(v_val_2662_) == 1)
{
lean_object* v_val_2663_; lean_object* v_version_2664_; lean_object* v_revision_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec_ref(v___y_2637_);
v_val_2663_ = lean_ctor_get(v_val_2662_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_val_2662_, 1);
v_version_2664_ = lean_ctor_get(v_val_2663_, 0);
lean_inc_ref(v_version_2664_);
v_revision_2665_ = lean_ctor_get(v_val_2663_, 1);
lean_inc_ref(v_revision_2665_);
lean_dec(v_val_2663_);
v___x_2666_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
lean_inc_ref(v_scope_2609_);
v___x_2667_ = lean_string_append(v_scope_2609_, v___x_2666_);
v___x_2668_ = lean_string_append(v___x_2667_, v___x_2614_);
lean_dec_ref(v___x_2614_);
v___x_2669_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__4));
v___x_2670_ = lean_string_append(v___x_2668_, v___x_2669_);
v___x_2671_ = l_Lake_StdVer_toString(v_version_2664_);
v___x_2672_ = lean_string_append(v___x_2670_, v___x_2671_);
lean_dec_ref(v___x_2671_);
v___x_2673_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__5));
v___x_2674_ = lean_string_append(v___x_2672_, v___x_2673_);
v___x_2675_ = lean_string_append(v___x_2674_, v_revision_2665_);
v___x_2676_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__6));
v___x_2677_ = lean_string_append(v___x_2675_, v___x_2676_);
v___x_2678_ = 1;
v___x_2679_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*1, v___x_2678_);
lean_inc_ref(v_a_2451_);
v___x_2680_ = lean_apply_2(v_a_2451_, v___x_2679_, lean_box(0));
v___y_2474_ = v___y_2633_;
v___y_2475_ = v___y_2632_;
v___y_2476_ = v___y_2634_;
v___y_2477_ = v___y_2635_;
v___y_2478_ = v___y_2636_;
v_a_2479_ = v_revision_2665_;
goto v___jp_2473_;
}
else
{
lean_inc_ref(v_scope_2609_);
lean_dec(v_val_2662_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v___y_2616_ = v___y_2637_;
goto v___jp_2615_;
}
}
}
}
v___jp_2681_:
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = lean_array_get_size(v_snd_2689_);
v___x_2691_ = lean_nat_dec_lt(v___x_2612_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_dec_ref(v_snd_2689_);
v___y_2632_ = v___y_2683_;
v___y_2633_ = v___y_2682_;
v___y_2634_ = v___y_2684_;
v___y_2635_ = v___y_2685_;
v___y_2636_ = v___y_2687_;
v___y_2637_ = v___y_2686_;
v_a_2638_ = v_fst_2688_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2692_; size_t v___x_2693_; size_t v___x_2694_; lean_object* v___x_2695_; 
v___x_2692_ = lean_box(0);
v___x_2693_ = ((size_t)0ULL);
v___x_2694_ = lean_usize_of_nat(v___x_2690_);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2689_, v___x_2693_, v___x_2694_, v___x_2692_, v_a_2451_);
lean_dec_ref(v_snd_2689_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_dec_ref_known(v___x_2695_, 1);
v___y_2632_ = v___y_2683_;
v___y_2633_ = v___y_2682_;
v___y_2634_ = v___y_2684_;
v___y_2635_ = v___y_2685_;
v___y_2636_ = v___y_2687_;
v___y_2637_ = v___y_2686_;
v_a_2638_ = v_fst_2688_;
goto v___jp_2631_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v_fst_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___x_2614_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
v___jp_2704_:
{
if (lean_obj_tag(v_a_2705_) == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_inc_ref(v_scope_2609_);
lean_dec_ref_known(v_a_2705_, 1);
lean_dec_ref(v_relPkgsDir_2449_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v___x_2706_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0));
v___x_2707_ = lean_string_append(v_scope_2609_, v___x_2706_);
v___x_2708_ = lean_string_append(v___x_2707_, v___x_2614_);
lean_dec_ref(v___x_2614_);
v___x_2709_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__7));
v___x_2710_ = lean_string_append(v___x_2708_, v___x_2709_);
v___x_2711_ = 3;
v___x_2712_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*1, v___x_2711_);
lean_inc_ref(v_a_2451_);
v___x_2713_ = lean_apply_2(v_a_2451_, v___x_2712_, lean_box(0));
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2808_; 
v_a_2716_ = lean_ctor_get(v_a_2705_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_a_2705_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2718_ = v_a_2705_;
v_isShared_2719_ = v_isSharedCheck_2808_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v_a_2705_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2808_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
if (lean_obj_tag(v_a_2716_) == 0)
{
lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2718_);
lean_dec_ref(v___x_2614_);
lean_dec_ref(v_relPkgsDir_2449_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
v___x_2720_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(v_dep_2445_);
v___x_2721_ = 3;
v___x_2722_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*1, v___x_2721_);
lean_inc_ref(v_a_2451_);
v___x_2723_ = lean_apply_2(v_a_2451_, v___x_2722_, lean_box(0));
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
else
{
lean_object* v_val_2726_; lean_object* v___x_2727_; 
v_val_2726_ = lean_ctor_get(v_a_2716_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v_a_2716_, 1);
v___x_2727_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_2726_);
if (lean_obj_tag(v___x_2727_) == 1)
{
lean_object* v_val_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2807_; 
v_val_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2807_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_val_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2807_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
if (lean_obj_tag(v_val_2728_) == 0)
{
lean_object* v_url_2732_; lean_object* v_githubUrl_x3f_2733_; lean_object* v_defaultBranch_x3f_2734_; lean_object* v_subDir_x3f_2735_; lean_object* v_name_2736_; lean_object* v_fullName_2737_; lean_object* v___x_2738_; 
v_url_2732_ = lean_ctor_get(v_val_2728_, 1);
lean_inc_ref(v_url_2732_);
v_githubUrl_x3f_2733_ = lean_ctor_get(v_val_2728_, 2);
lean_inc(v_githubUrl_x3f_2733_);
v_defaultBranch_x3f_2734_ = lean_ctor_get(v_val_2728_, 3);
lean_inc(v_defaultBranch_x3f_2734_);
v_subDir_x3f_2735_ = lean_ctor_get(v_val_2728_, 4);
lean_inc(v_subDir_x3f_2735_);
lean_dec_ref_known(v_val_2728_, 5);
v_name_2736_ = lean_ctor_get(v_val_2726_, 0);
lean_inc_ref(v_name_2736_);
v_fullName_2737_ = lean_ctor_get(v_val_2726_, 1);
lean_inc_ref(v_fullName_2737_);
lean_dec(v_val_2726_);
v___x_2738_ = l_Lake_joinRelative(v_relPkgsDir_2449_, v_name_2736_);
switch(lean_obj_tag(v_version_2610_))
{
case 0:
{
lean_object* v___x_2739_; 
lean_del_object(v___x_2718_);
lean_dec_ref(v___x_2614_);
v___x_2739_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
if (lean_obj_tag(v_defaultBranch_x3f_2734_) == 0)
{
uint8_t v___x_2740_; 
lean_dec_ref(v___x_2738_);
lean_dec_ref(v_fullName_2737_);
lean_dec(v_subDir_x3f_2735_);
lean_dec(v_githubUrl_x3f_2733_);
lean_dec_ref(v_url_2732_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v___x_2740_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_box(0);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2741_);
v___x_2743_ = v___x_2730_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
else
{
lean_object* v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
lean_del_object(v___x_2730_);
v___x_2745_ = lean_box(0);
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2739_, v___x_2746_, v___x_2747_, v___x_2745_, v_a_2451_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v___x_2748_, 0);
lean_dec(v_unused_2756_);
v___x_2750_ = v___x_2748_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_dec(v___x_2748_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 1);
lean_ctor_set(v___x_2750_, 0, v___x_2745_);
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2745_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2748_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2748_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
else
{
lean_object* v_val_2765_; uint8_t v___x_2766_; 
lean_del_object(v___x_2730_);
v_val_2765_ = lean_ctor_get(v_defaultBranch_x3f_2734_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v_defaultBranch_x3f_2734_, 1);
v___x_2766_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2766_ == 0)
{
v___y_2474_ = v_githubUrl_x3f_2733_;
v___y_2475_ = v_subDir_x3f_2735_;
v___y_2476_ = v_url_2732_;
v___y_2477_ = v___x_2738_;
v___y_2478_ = v_fullName_2737_;
v_a_2479_ = v_val_2765_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = ((size_t)0ULL);
v___x_2769_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2739_, v___x_2768_, v___x_2769_, v___x_2767_, v_a_2451_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_dec_ref_known(v___x_2770_, 1);
v___y_2474_ = v_githubUrl_x3f_2733_;
v___y_2475_ = v_subDir_x3f_2735_;
v___y_2476_ = v_url_2732_;
v___y_2477_ = v___x_2738_;
v___y_2478_ = v_fullName_2737_;
v_a_2479_ = v_val_2765_;
goto v___jp_2473_;
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_val_2765_);
lean_dec_ref(v___x_2738_);
lean_dec_ref(v_fullName_2737_);
lean_dec(v_subDir_x3f_2735_);
lean_dec(v_githubUrl_x3f_2733_);
lean_dec_ref(v_url_2732_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
case 1:
{
lean_object* v_rev_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
lean_dec(v_defaultBranch_x3f_2734_);
lean_del_object(v___x_2730_);
lean_del_object(v___x_2718_);
lean_dec_ref(v___x_2614_);
v_rev_2779_ = lean_ctor_get(v_version_2610_, 0);
v___x_2780_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2781_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2781_ == 0)
{
lean_inc_ref(v_rev_2779_);
v___y_2474_ = v_githubUrl_x3f_2733_;
v___y_2475_ = v_subDir_x3f_2735_;
v___y_2476_ = v_url_2732_;
v___y_2477_ = v___x_2738_;
v___y_2478_ = v_fullName_2737_;
v_a_2479_ = v_rev_2779_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2782_; size_t v___x_2783_; size_t v___x_2784_; lean_object* v___x_2785_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = ((size_t)0ULL);
v___x_2784_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_2780_, v___x_2783_, v___x_2784_, v___x_2782_, v_a_2451_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_dec_ref_known(v___x_2785_, 1);
lean_inc_ref(v_rev_2779_);
v___y_2474_ = v_githubUrl_x3f_2733_;
v___y_2475_ = v_subDir_x3f_2735_;
v___y_2476_ = v_url_2732_;
v___y_2477_ = v___x_2738_;
v___y_2478_ = v_fullName_2737_;
v_a_2479_ = v_rev_2779_;
goto v___jp_2473_;
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v___x_2738_);
lean_dec_ref(v_fullName_2737_);
lean_dec(v_subDir_x3f_2735_);
lean_dec(v_githubUrl_x3f_2733_);
lean_dec_ref(v_url_2732_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
default: 
{
lean_object* v_ver_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_dec(v_defaultBranch_x3f_2734_);
lean_del_object(v___x_2730_);
v_ver_2794_ = lean_ctor_get(v_version_2610_, 0);
v___x_2795_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_scope_2609_);
lean_inc_ref(v_lakeEnv_2447_);
v___x_2796_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_2447_, v_scope_2609_, v___x_2614_, v___x_2795_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v_a_2798_; lean_object* v___x_2800_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
v_a_2798_ = lean_ctor_get(v___x_2796_, 1);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2796_, 2);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_a_2797_);
v___x_2800_ = v___x_2718_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2797_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_inc_ref(v_ver_2794_);
v___y_2682_ = v_githubUrl_x3f_2733_;
v___y_2683_ = v_subDir_x3f_2735_;
v___y_2684_ = v_url_2732_;
v___y_2685_ = v___x_2738_;
v___y_2686_ = v_ver_2794_;
v___y_2687_ = v_fullName_2737_;
v_fst_2688_ = v___x_2800_;
v_snd_2689_ = v_a_2798_;
goto v___jp_2681_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v_a_2803_; lean_object* v___x_2805_; 
v_a_2802_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2802_);
v_a_2803_ = lean_ctor_get(v___x_2796_, 1);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2796_, 2);
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 0);
lean_ctor_set(v___x_2718_, 0, v_a_2802_);
v___x_2805_ = v___x_2718_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2802_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_inc_ref(v_ver_2794_);
v___y_2682_ = v_githubUrl_x3f_2733_;
v___y_2683_ = v_subDir_x3f_2735_;
v___y_2684_ = v_url_2732_;
v___y_2685_ = v___x_2738_;
v___y_2686_ = v_ver_2794_;
v___y_2687_ = v_fullName_2737_;
v_fst_2688_ = v___x_2805_;
v_snd_2689_ = v_a_2803_;
goto v___jp_2681_;
}
}
}
}
}
else
{
lean_del_object(v___x_2730_);
lean_dec(v_val_2728_);
lean_del_object(v___x_2718_);
lean_dec_ref(v___x_2614_);
lean_dec_ref(v_relPkgsDir_2449_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v___y_2454_ = v_val_2726_;
v___y_2455_ = v_a_2451_;
goto v___jp_2453_;
}
}
}
else
{
lean_dec(v___x_2727_);
lean_del_object(v___x_2718_);
lean_dec_ref(v___x_2614_);
lean_dec_ref(v_relPkgsDir_2449_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v___y_2454_ = v_val_2726_;
v___y_2455_ = v_a_2451_;
goto v___jp_2453_;
}
}
}
}
}
v___jp_2811_:
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = lean_array_get_size(v_snd_2813_);
v___x_2815_ = lean_nat_dec_lt(v___x_2612_, v___x_2814_);
if (v___x_2815_ == 0)
{
lean_dec_ref(v_snd_2813_);
v_a_2705_ = v_fst_2812_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2816_; size_t v___x_2817_; size_t v___x_2818_; lean_object* v___x_2819_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = ((size_t)0ULL);
v___x_2818_ = lean_usize_of_nat(v___x_2814_);
v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_snd_2813_, v___x_2817_, v___x_2818_, v___x_2816_, v_a_2451_);
lean_dec_ref(v_snd_2813_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_dec_ref_known(v___x_2819_, 1);
v_a_2705_ = v_fst_2812_;
goto v___jp_2704_;
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_fst_2812_);
lean_dec_ref(v___x_2614_);
lean_dec_ref(v_relPkgsDir_2449_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
else
{
uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_inc(v_name_2608_);
lean_dec_ref(v_relPkgsDir_2449_);
lean_dec_ref(v_wsDir_2448_);
lean_dec_ref(v_lakeEnv_2447_);
lean_dec_ref(v_dep_2445_);
v___x_2834_ = 0;
v___x_2835_ = l_Lean_Name_toString(v_name_2608_, v___x_2834_);
v___x_2836_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__8));
v___x_2837_ = lean_string_append(v___x_2835_, v___x_2836_);
v___x_2838_ = 3;
v___x_2839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set_uint8(v___x_2839_, sizeof(void*)*1, v___x_2838_);
lean_inc_ref(v_a_2451_);
v___x_2840_ = lean_apply_2(v_a_2451_, v___x_2839_, lean_box(0));
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
return v___x_2842_;
}
}
v___jp_2453_:
{
lean_object* v_fullName_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_fullName_2456_ = lean_ctor_get(v___y_2454_, 1);
lean_inc_ref(v_fullName_2456_);
lean_dec_ref(v___y_2454_);
v___x_2457_ = ((lean_object*)(l_Lake_Dependency_materialize___closed__0));
v___x_2458_ = lean_string_append(v_fullName_2456_, v___x_2457_);
v___x_2459_ = 3;
v___x_2460_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*1, v___x_2459_);
lean_inc_ref(v___y_2455_);
v___x_2461_ = lean_apply_2(v___y_2455_, v___x_2460_, lean_box(0));
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
return v___x_2463_;
}
v___jp_2464_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___y_2465_);
v___x_2472_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_2451_, v_dep_2445_, v_inherited_2446_, v_lakeEnv_2447_, v_wsDir_2448_, v___y_2469_, v___y_2468_, v___y_2467_, v___y_2470_, v___x_2471_, v___y_2466_);
lean_dec_ref(v_lakeEnv_2447_);
return v___x_2472_;
}
v___jp_2473_:
{
if (lean_obj_tag(v___y_2474_) == 0)
{
lean_object* v___x_2480_; 
v___x_2480_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_2465_ = v_a_2479_;
v___y_2466_ = v___y_2475_;
v___y_2467_ = v___y_2476_;
v___y_2468_ = v___y_2477_;
v___y_2469_ = v___y_2478_;
v___y_2470_ = v___x_2480_;
goto v___jp_2464_;
}
else
{
lean_object* v_val_2481_; 
v_val_2481_ = lean_ctor_get(v___y_2474_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v___y_2474_, 1);
v___y_2465_ = v_a_2479_;
v___y_2466_ = v___y_2475_;
v___y_2467_ = v___y_2476_;
v___y_2468_ = v___y_2477_;
v___y_2469_ = v___y_2478_;
v___y_2470_ = v_val_2481_;
goto v___jp_2464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* v_dep_2843_, lean_object* v_inherited_2844_, lean_object* v_lakeEnv_2845_, lean_object* v_wsDir_2846_, lean_object* v_relPkgsDir_2847_, lean_object* v_relParentDir_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
uint8_t v_inherited_boxed_2851_; lean_object* v_res_2852_; 
v_inherited_boxed_2851_ = lean_unbox(v_inherited_2844_);
v_res_2852_ = l_Lake_Dependency_materialize(v_dep_2843_, v_inherited_boxed_2851_, v_lakeEnv_2845_, v_wsDir_2846_, v_relPkgsDir_2847_, v_relParentDir_2848_, v_a_2849_);
lean_dec_ref(v_a_2849_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object* v_manifestEntry_2858_, lean_object* v_wsDir_2859_, lean_object* v_relPkgDir_2860_, lean_object* v_remoteUrl_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v___y_2865_; lean_object* v_a_2866_; lean_object* v___f_2869_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v_val_2875_; lean_object* v_pkgDir_2891_; lean_object* v_a_2893_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v_val_2935_; lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___f_2869_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__1));
lean_inc_ref(v_relPkgDir_2860_);
v_pkgDir_2891_ = l_Lake_joinRelative(v_wsDir_2859_, v_relPkgDir_2860_);
v___x_2931_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_2932_ = lean_unsigned_to_nat(0u);
v___x_2933_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_2891_);
v___x_2950_ = l_Lake_resolvePath(v_pkgDir_2891_);
v___x_2951_ = lean_string_utf8_byte_size(v___x_2950_);
v___x_2952_ = lean_nat_dec_eq(v___x_2951_, v___x_2932_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2950_);
v_val_2935_ = v___x_2953_;
goto v___jp_2934_;
}
else
{
lean_object* v___x_2954_; 
lean_dec_ref(v___x_2950_);
v___x_2954_ = lean_box(0);
v_val_2935_ = v___x_2954_;
goto v___jp_2934_;
}
v___jp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2867_, 0, v___y_2865_);
lean_ctor_set(v___x_2867_, 1, v_relPkgDir_2860_);
lean_ctor_set(v___x_2867_, 2, v_remoteUrl_2861_);
lean_ctor_set(v___x_2867_, 3, v_a_2866_);
lean_ctor_set(v___x_2867_, 4, v_manifestEntry_2858_);
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
v___jp_2870_:
{
lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2876_ = lean_array_get_size(v___y_2872_);
v___x_2877_ = lean_nat_dec_lt(v___y_2874_, v___x_2876_);
if (v___x_2877_ == 0)
{
v___y_2865_ = v___y_2873_;
v_a_2866_ = v_val_2875_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2878_; size_t v___x_2879_; size_t v___x_2880_; lean_object* v___x_1877__overap_2881_; lean_object* v___x_2882_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = ((size_t)0ULL);
v___x_2880_ = lean_usize_of_nat(v___x_2876_);
lean_inc_ref(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_1877__overap_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___y_2871_, v___f_2869_, v___y_2872_, v___x_2879_, v___x_2880_, v___x_2878_);
lean_inc_ref(v_a_2862_);
v___x_2882_ = lean_apply_2(v___x_1877__overap_2881_, v_a_2862_, lean_box(0));
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_dec_ref_known(v___x_2882_, 1);
v___y_2865_ = v___y_2873_;
v_a_2866_ = v_val_2875_;
goto v___jp_2864_;
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec_ref(v_val_2875_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v_remoteUrl_2861_);
lean_dec_ref(v_relPkgDir_2860_);
lean_dec_ref(v_manifestEntry_2858_);
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2882_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
v___jp_2892_:
{
if (lean_obj_tag(v_a_2893_) == 1)
{
lean_object* v_manifestFile_x3f_2894_; 
lean_dec_ref(v_pkgDir_2891_);
v_manifestFile_x3f_2894_ = lean_ctor_get(v_manifestEntry_2858_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2894_) == 1)
{
lean_object* v_val_2895_; lean_object* v_val_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_val_2895_ = lean_ctor_get(v_a_2893_, 0);
lean_inc_n(v_val_2895_, 2);
lean_dec_ref_known(v_a_2893_, 1);
v_val_2896_ = lean_ctor_get(v_manifestFile_x3f_2894_, 0);
lean_inc(v_val_2896_);
v___x_2897_ = l_Lake_joinRelative(v_val_2895_, v_val_2896_);
v___x_2898_ = lean_obj_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__3);
v___x_2899_ = lean_unsigned_to_nat(0u);
v___x_2900_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_2901_ = l_Lake_Manifest_load(v___x_2897_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2901_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 1);
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
v___y_2871_ = v___x_2898_;
v___y_2872_ = v___x_2900_;
v___y_2873_ = v_val_2895_;
v___y_2874_ = v___x_2899_;
v_val_2875_ = v___x_2907_;
goto v___jp_2870_;
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v_a_2910_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2901_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2901_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set_tag(v___x_2912_, 0);
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
v___y_2871_ = v___x_2898_;
v___y_2872_ = v___x_2900_;
v___y_2873_ = v_val_2895_;
v___y_2874_ = v___x_2899_;
v_val_2875_ = v___x_2915_;
goto v___jp_2870_;
}
}
}
}
else
{
lean_object* v_val_2918_; lean_object* v___x_2919_; 
v_val_2918_ = lean_ctor_get(v_a_2893_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v_a_2893_, 1);
v___x_2919_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2865_ = v_val_2918_;
v_a_2866_ = v___x_2919_;
goto v___jp_2864_;
}
}
else
{
lean_object* v_name_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v_a_2893_);
lean_dec_ref(v_remoteUrl_2861_);
lean_dec_ref(v_relPkgDir_2860_);
v_name_2920_ = lean_ctor_get(v_manifestEntry_2858_, 0);
lean_inc(v_name_2920_);
lean_dec_ref(v_manifestEntry_2858_);
v___x_2921_ = 0;
v___x_2922_ = l_Lean_Name_toString(v_name_2920_, v___x_2921_);
v___x_2923_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_2924_ = lean_string_append(v___x_2922_, v___x_2923_);
v___x_2925_ = lean_string_append(v___x_2924_, v_pkgDir_2891_);
lean_dec_ref(v_pkgDir_2891_);
v___x_2926_ = 3;
v___x_2927_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set_uint8(v___x_2927_, sizeof(void*)*1, v___x_2926_);
lean_inc_ref(v_a_2862_);
v___x_2928_ = lean_apply_2(v_a_2862_, v___x_2927_, lean_box(0));
v___x_2929_ = lean_box(0);
v___x_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
v___jp_2934_:
{
uint8_t v___x_2936_; 
v___x_2936_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_2936_ == 0)
{
v_a_2893_ = v_val_2935_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_2937_; size_t v___x_2938_; size_t v___x_2939_; lean_object* v___x_1931__overap_2940_; lean_object* v___x_2941_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = ((size_t)0ULL);
v___x_2939_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_1931__overap_2940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2931_, v___f_2869_, v___x_2933_, v___x_2938_, v___x_2939_, v___x_2937_);
lean_inc_ref(v_a_2862_);
v___x_2941_ = lean_apply_2(v___x_1931__overap_2940_, v_a_2862_, lean_box(0));
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_dec_ref_known(v___x_2941_, 1);
v_a_2893_ = v_val_2935_;
goto v___jp_2892_;
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_val_2935_);
lean_dec_ref(v_pkgDir_2891_);
lean_dec_ref(v_remoteUrl_2861_);
lean_dec_ref(v_relPkgDir_2860_);
lean_dec_ref(v_manifestEntry_2858_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(lean_object* v_manifestEntry_2955_, lean_object* v_wsDir_2956_, lean_object* v_relPkgDir_2957_, lean_object* v_remoteUrl_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(v_manifestEntry_2955_, v_wsDir_2956_, v_relPkgDir_2957_, v_remoteUrl_2958_, v_a_2959_);
lean_dec_ref(v_a_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(lean_object* v_t_2962_, lean_object* v_k_2963_, lean_object* v_fallback_2964_){
_start:
{
if (lean_obj_tag(v_t_2962_) == 0)
{
lean_object* v_k_2965_; lean_object* v_v_2966_; lean_object* v_l_2967_; lean_object* v_r_2968_; uint8_t v___x_2969_; 
v_k_2965_ = lean_ctor_get(v_t_2962_, 1);
v_v_2966_ = lean_ctor_get(v_t_2962_, 2);
v_l_2967_ = lean_ctor_get(v_t_2962_, 3);
v_r_2968_ = lean_ctor_get(v_t_2962_, 4);
v___x_2969_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2963_, v_k_2965_);
switch(v___x_2969_)
{
case 0:
{
v_t_2962_ = v_l_2967_;
goto _start;
}
case 1:
{
lean_inc(v_v_2966_);
return v_v_2966_;
}
default: 
{
v_t_2962_ = v_r_2968_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2964_);
return v_fallback_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg___boxed(lean_object* v_t_2972_, lean_object* v_k_2973_, lean_object* v_fallback_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_2972_, v_k_2973_, v_fallback_2974_);
lean_dec(v_fallback_2974_);
lean_dec(v_k_2973_);
lean_dec(v_t_2972_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* v_manifestEntry_2976_, lean_object* v_lakeEnv_2977_, lean_object* v_wsDir_2978_, lean_object* v_relPkgsDir_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v_a_2986_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v_val_2995_; lean_object* v_src_3010_; 
v_src_3010_ = lean_ctor_get(v_manifestEntry_2976_, 4);
lean_inc_ref(v_src_3010_);
if (lean_obj_tag(v_src_3010_) == 0)
{
lean_object* v_name_3011_; lean_object* v_manifestFile_x3f_3012_; lean_object* v_dir_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v_relPkgsDir_2979_);
v_name_3011_ = lean_ctor_get(v_manifestEntry_2976_, 0);
v_manifestFile_x3f_3012_ = lean_ctor_get(v_manifestEntry_2976_, 3);
v_dir_3013_ = lean_ctor_get(v_src_3010_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_src_3010_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3015_ = v_src_3010_;
v_isShared_3016_ = v_isSharedCheck_3103_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_dir_3013_);
lean_dec(v_src_3010_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3103_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___y_3019_; lean_object* v_a_3020_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v_val_3029_; lean_object* v_pkgDir_3044_; lean_object* v_a_3046_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v_val_3084_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3017_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
lean_inc_ref(v_dir_3013_);
v_pkgDir_3044_ = l_Lake_joinRelative(v_wsDir_2978_, v_dir_3013_);
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3044_);
v___x_3098_ = l_Lake_resolvePath(v_pkgDir_3044_);
v___x_3099_ = lean_string_utf8_byte_size(v___x_3098_);
v___x_3100_ = lean_nat_dec_eq(v___x_3099_, v___x_3081_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3098_);
v_val_3084_ = v___x_3101_;
goto v___jp_3083_;
}
else
{
lean_object* v___x_3102_; 
lean_dec_ref(v___x_3098_);
v___x_3102_ = lean_box(0);
v_val_3084_ = v___x_3102_;
goto v___jp_3083_;
}
v___jp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3021_, 0, v___y_3019_);
lean_ctor_set(v___x_3021_, 1, v_dir_3013_);
lean_ctor_set(v___x_3021_, 2, v___x_3017_);
lean_ctor_set(v___x_3021_, 3, v_a_3020_);
lean_ctor_set(v___x_3021_, 4, v_manifestEntry_2976_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3021_);
v___x_3023_ = v___x_3015_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
v___jp_3025_:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = lean_array_get_size(v___y_3026_);
v___x_3031_ = lean_nat_dec_lt(v___y_3027_, v___x_3030_);
if (v___x_3031_ == 0)
{
v___y_3019_ = v___y_3028_;
v_a_3020_ = v_val_3029_;
goto v___jp_3018_;
}
else
{
lean_object* v___x_3032_; size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = lean_usize_of_nat(v___x_3030_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3026_, v___x_3033_, v___x_3034_, v___x_3032_, v_a_2980_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref_known(v___x_3035_, 1);
v___y_3019_ = v___y_3028_;
v_a_3020_ = v_val_3029_;
goto v___jp_3018_;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v_val_3029_);
lean_dec_ref(v___y_3028_);
lean_del_object(v___x_3015_);
lean_dec_ref(v_dir_3013_);
lean_dec_ref(v_manifestEntry_2976_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
v___jp_3045_:
{
if (lean_obj_tag(v_a_3046_) == 1)
{
lean_dec_ref(v_pkgDir_3044_);
if (lean_obj_tag(v_manifestFile_x3f_3012_) == 1)
{
lean_object* v_val_3047_; lean_object* v_val_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_val_3047_ = lean_ctor_get(v_a_3046_, 0);
lean_inc_n(v_val_3047_, 2);
lean_dec_ref_known(v_a_3046_, 1);
v_val_3048_ = lean_ctor_get(v_manifestFile_x3f_3012_, 0);
lean_inc(v_val_3048_);
v___x_3049_ = l_Lake_joinRelative(v_val_3047_, v_val_3048_);
v___x_3050_ = lean_unsigned_to_nat(0u);
v___x_3051_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3052_ = l_Lake_Manifest_load(v___x_3049_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3052_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set_tag(v___x_3055_, 1);
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
v___y_3026_ = v___x_3051_;
v___y_3027_ = v___x_3050_;
v___y_3028_ = v_val_3047_;
v_val_3029_ = v___x_3058_;
goto v___jp_3025_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3052_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3052_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 0);
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
v___y_3026_ = v___x_3051_;
v___y_3027_ = v___x_3050_;
v___y_3028_ = v_val_3047_;
v_val_3029_ = v___x_3066_;
goto v___jp_3025_;
}
}
}
}
else
{
lean_object* v_val_3069_; lean_object* v___x_3070_; 
v_val_3069_ = lean_ctor_get(v_a_3046_, 0);
lean_inc(v_val_3069_);
lean_dec_ref_known(v_a_3046_, 1);
v___x_3070_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_3019_ = v_val_3069_;
v_a_3020_ = v___x_3070_;
goto v___jp_3018_;
}
}
else
{
uint8_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_inc(v_name_3011_);
lean_dec(v_a_3046_);
lean_del_object(v___x_3015_);
lean_dec_ref(v_dir_3013_);
lean_dec_ref(v_manifestEntry_2976_);
v___x_3071_ = 0;
v___x_3072_ = l_Lean_Name_toString(v_name_3011_, v___x_3071_);
v___x_3073_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3074_ = lean_string_append(v___x_3072_, v___x_3073_);
v___x_3075_ = lean_string_append(v___x_3074_, v_pkgDir_3044_);
lean_dec_ref(v_pkgDir_3044_);
v___x_3076_ = 3;
v___x_3077_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*1, v___x_3076_);
lean_inc_ref(v_a_2980_);
v___x_3078_ = lean_apply_2(v_a_2980_, v___x_3077_, lean_box(0));
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
}
v___jp_3083_:
{
uint8_t v___x_3085_; 
v___x_3085_ = lean_uint8_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__6);
if (v___x_3085_ == 0)
{
v_a_3046_ = v_val_3084_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3086_; size_t v___x_3087_; size_t v___x_3088_; lean_object* v___x_3089_; 
v___x_3086_ = lean_box(0);
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = lean_usize_once(&l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7, &l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7_once, _init_l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__7);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___x_3082_, v___x_3087_, v___x_3088_, v___x_3086_, v_a_2980_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_dec_ref_known(v___x_3089_, 1);
v_a_3046_ = v_val_3084_;
goto v___jp_3045_;
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_val_3084_);
lean_dec_ref(v_pkgDir_3044_);
lean_del_object(v___x_3015_);
lean_dec_ref(v_dir_3013_);
lean_dec_ref(v_manifestEntry_2976_);
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
}
}
else
{
lean_object* v_name_3104_; lean_object* v_manifestFile_x3f_3105_; lean_object* v_url_3106_; lean_object* v_rev_3107_; lean_object* v_subDir_x3f_3108_; lean_object* v_pkgUrlMap_3109_; uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v_a_3116_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v_val_3155_; lean_object* v_relGitDir_3170_; lean_object* v_repo_3171_; lean_object* v_url_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_name_3104_ = lean_ctor_get(v_manifestEntry_2976_, 0);
v_manifestFile_x3f_3105_ = lean_ctor_get(v_manifestEntry_2976_, 3);
v_url_3106_ = lean_ctor_get(v_src_3010_, 0);
lean_inc_ref(v_url_3106_);
v_rev_3107_ = lean_ctor_get(v_src_3010_, 1);
lean_inc_ref(v_rev_3107_);
v_subDir_x3f_3108_ = lean_ctor_get(v_src_3010_, 3);
lean_inc(v_subDir_x3f_3108_);
lean_dec_ref_known(v_src_3010_, 4);
v_pkgUrlMap_3109_ = lean_ctor_get(v_lakeEnv_2977_, 5);
v___x_3110_ = 0;
lean_inc(v_name_3104_);
v___x_3111_ = l_Lean_Name_toString(v_name_3104_, v___x_3110_);
lean_inc_ref_n(v___x_3111_, 2);
v_relGitDir_3170_ = l_Lake_joinRelative(v_relPkgsDir_2979_, v___x_3111_);
lean_inc_ref(v_relGitDir_3170_);
lean_inc_ref(v_wsDir_2978_);
v_repo_3171_ = l_Lake_joinRelative(v_wsDir_2978_, v_relGitDir_3170_);
v_url_3172_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_pkgUrlMap_3109_, v_name_3104_, v_url_3106_);
lean_dec_ref(v_url_3106_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_rev_3107_);
lean_inc(v_url_3172_);
v___x_3174_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_2980_, v___x_3111_, v_repo_3171_, v_url_3172_, v___x_3173_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3187_; 
lean_dec_ref_known(v___x_3174_, 1);
if (lean_obj_tag(v_subDir_x3f_3108_) == 0)
{
v___y_3187_ = v_relGitDir_3170_;
goto v___jp_3186_;
}
else
{
lean_object* v_val_3191_; lean_object* v___x_3192_; 
v_val_3191_ = lean_ctor_get(v_subDir_x3f_3108_, 0);
lean_inc(v_val_3191_);
lean_dec_ref_known(v_subDir_x3f_3108_, 1);
v___x_3192_ = l_Lake_joinRelative(v_relGitDir_3170_, v_val_3191_);
v___y_3187_ = v___x_3192_;
goto v___jp_3186_;
}
v___jp_3175_:
{
lean_object* v_pkgDir_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
lean_inc_ref(v___y_3176_);
v_pkgDir_3178_ = l_Lake_joinRelative(v_wsDir_2978_, v___y_3176_);
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
lean_inc_ref(v_pkgDir_3178_);
v___x_3181_ = l_Lake_resolvePath(v_pkgDir_3178_);
v___x_3182_ = lean_string_utf8_byte_size(v___x_3181_);
v___x_3183_ = lean_nat_dec_eq(v___x_3182_, v___x_3179_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3181_);
v___y_3150_ = v___x_3179_;
v___y_3151_ = v___x_3180_;
v___y_3152_ = v___y_3177_;
v___y_3153_ = v___y_3176_;
v___y_3154_ = v_pkgDir_3178_;
v_val_3155_ = v___x_3184_;
goto v___jp_3149_;
}
else
{
lean_object* v___x_3185_; 
lean_dec_ref(v___x_3181_);
v___x_3185_ = lean_box(0);
v___y_3150_ = v___x_3179_;
v___y_3151_ = v___x_3180_;
v___y_3152_ = v___y_3177_;
v___y_3153_ = v___y_3176_;
v___y_3154_ = v_pkgDir_3178_;
v_val_3155_ = v___x_3185_;
goto v___jp_3149_;
}
}
v___jp_3186_:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lake_Git_filterUrl_x3f(v_url_3172_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v___x_3189_; 
v___x_3189_ = ((lean_object*)(l_Lake_instInhabitedMaterializedDep_default___closed__0));
v___y_3176_ = v___y_3187_;
v___y_3177_ = v___x_3189_;
goto v___jp_3175_;
}
else
{
lean_object* v_val_3190_; 
v_val_3190_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_val_3190_);
lean_dec_ref_known(v___x_3188_, 1);
v___y_3176_ = v___y_3187_;
v___y_3177_ = v_val_3190_;
goto v___jp_3175_;
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_url_3172_);
lean_dec_ref(v_relGitDir_3170_);
lean_dec_ref(v___x_3111_);
lean_dec(v_subDir_x3f_3108_);
lean_dec_ref(v_wsDir_2978_);
lean_dec_ref(v_manifestEntry_2976_);
v_a_3193_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3174_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3174_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
v___jp_3112_:
{
if (lean_obj_tag(v_a_3116_) == 1)
{
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___x_3111_);
if (lean_obj_tag(v_manifestFile_x3f_3105_) == 1)
{
lean_object* v_val_3117_; lean_object* v_val_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v_val_3117_ = lean_ctor_get(v_a_3116_, 0);
lean_inc_n(v_val_3117_, 2);
lean_dec_ref_known(v_a_3116_, 1);
v_val_3118_ = lean_ctor_get(v_manifestFile_x3f_3105_, 0);
lean_inc(v_val_3118_);
v___x_3119_ = l_Lake_joinRelative(v_val_3117_, v_val_3118_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo_resolveUrl___closed__4));
v___x_3122_ = l_Lake_Manifest_load(v___x_3119_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 1);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
v___y_2990_ = v___x_3120_;
v___y_2991_ = v_val_3117_;
v___y_2992_ = v___x_3121_;
v___y_2993_ = v___y_3113_;
v___y_2994_ = v___y_3114_;
v_val_2995_ = v___x_3128_;
goto v___jp_2989_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_a_3131_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3122_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3122_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set_tag(v___x_3133_, 0);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
v___y_2990_ = v___x_3120_;
v___y_2991_ = v_val_3117_;
v___y_2992_ = v___x_3121_;
v___y_2993_ = v___y_3113_;
v___y_2994_ = v___y_3114_;
v_val_2995_ = v___x_3136_;
goto v___jp_2989_;
}
}
}
}
else
{
lean_object* v_val_3139_; lean_object* v___x_3140_; 
v_val_3139_ = lean_ctor_get(v_a_3116_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v_a_3116_, 1);
v___x_3140_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1));
v___y_2983_ = v_val_3139_;
v___y_2984_ = v___y_3114_;
v___y_2985_ = v___y_3113_;
v_a_2986_ = v___x_3140_;
goto v___jp_2982_;
}
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec(v_a_3116_);
lean_dec_ref(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec_ref(v_manifestEntry_2976_);
v___x_3141_ = ((lean_object*)(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0));
v___x_3142_ = lean_string_append(v___x_3111_, v___x_3141_);
v___x_3143_ = lean_string_append(v___x_3142_, v___y_3115_);
lean_dec_ref(v___y_3115_);
v___x_3144_ = 3;
v___x_3145_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3145_, 0, v___x_3143_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*1, v___x_3144_);
lean_inc_ref(v_a_2980_);
v___x_3146_ = lean_apply_2(v_a_2980_, v___x_3145_, lean_box(0));
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
v___jp_3149_:
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = lean_array_get_size(v___y_3151_);
v___x_3157_ = lean_nat_dec_lt(v___y_3150_, v___x_3156_);
if (v___x_3157_ == 0)
{
v___y_3113_ = v___y_3153_;
v___y_3114_ = v___y_3152_;
v___y_3115_ = v___y_3154_;
v_a_3116_ = v_val_3155_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3158_; size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3158_ = lean_box(0);
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = lean_usize_of_nat(v___x_3156_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_3151_, v___x_3159_, v___x_3160_, v___x_3158_, v_a_2980_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_dec_ref_known(v___x_3161_, 1);
v___y_3113_ = v___y_3153_;
v___y_3114_ = v___y_3152_;
v___y_3115_ = v___y_3154_;
v_a_3116_ = v_val_3155_;
goto v___jp_3112_;
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_val_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v___x_3111_);
lean_dec_ref(v_manifestEntry_2976_);
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
v___jp_2982_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2987_, 0, v___y_2983_);
lean_ctor_set(v___x_2987_, 1, v___y_2985_);
lean_ctor_set(v___x_2987_, 2, v___y_2984_);
lean_ctor_set(v___x_2987_, 3, v_a_2986_);
lean_ctor_set(v___x_2987_, 4, v_manifestEntry_2976_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
v___jp_2989_:
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = lean_array_get_size(v___y_2992_);
v___x_2997_ = lean_nat_dec_lt(v___y_2990_, v___x_2996_);
if (v___x_2997_ == 0)
{
v___y_2983_ = v___y_2991_;
v___y_2984_ = v___y_2994_;
v___y_2985_ = v___y_2993_;
v_a_2986_ = v_val_2995_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_2998_; size_t v___x_2999_; size_t v___x_3000_; lean_object* v___x_3001_; 
v___x_2998_ = lean_box(0);
v___x_2999_ = ((size_t)0ULL);
v___x_3000_ = lean_usize_of_nat(v___x_2996_);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v___y_2992_, v___x_2999_, v___x_3000_, v___x_2998_, v_a_2980_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_dec_ref_known(v___x_3001_, 1);
v___y_2983_ = v___y_2991_;
v___y_2984_ = v___y_2994_;
v___y_2985_ = v___y_2993_;
v_a_2986_ = v_val_2995_;
goto v___jp_2982_;
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec_ref(v_val_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v_manifestEntry_2976_);
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* v_manifestEntry_3201_, lean_object* v_lakeEnv_3202_, lean_object* v_wsDir_3203_, lean_object* v_relPkgsDir_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lake_PackageEntry_materialize(v_manifestEntry_3201_, v_lakeEnv_3202_, v_wsDir_3203_, v_relPkgsDir_3204_, v_a_3205_);
lean_dec_ref(v_a_3205_);
lean_dec_ref(v_lakeEnv_3202_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(lean_object* v_00_u03b4_3208_, lean_object* v_t_3209_, lean_object* v_k_3210_, lean_object* v_fallback_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___redArg(v_t_3209_, v_k_3210_, v_fallback_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0___boxed(lean_object* v_00_u03b4_3213_, lean_object* v_t_3214_, lean_object* v_k_3215_, lean_object* v_fallback_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lake_PackageEntry_materialize_spec__0(v_00_u03b4_3213_, v_t_3214_, v_k_3215_, v_fallback_3216_);
lean_dec(v_fallback_3216_);
lean_dec(v_k_3215_);
lean_dec(v_t_3214_);
return v_res_3217_;
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
