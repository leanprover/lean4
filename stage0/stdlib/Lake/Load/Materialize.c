// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: public import Lake.Config.Env public import Lake.Load.Manifest public import Lake.Config.Package import Lake.Util.Git import Lake.Config.Dependency import Lake.Reservoir
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1;
extern lean_object* l_System_instInhabitedFilePath_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__3;
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__6;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx___boxed(lean_object*);
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__8;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__9;
static lean_object* l_Lake_Dependency_materialize___closed__11;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__10;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
static lean_object* l_Lake_PackageEntry_materialize___closed__0;
lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__7;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
static lean_object* l_Lake_Dependency_materialize___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__12;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__2;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
lean_object* lean_io_realpath(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
static uint8_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
static size_t l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Option_instDecidableEq_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__3;
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(x_5, x_8);
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
lean_object* x_14; 
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": repository '", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has local changes", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_defaultRemote;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_80; lean_object* x_84; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_89 = lean_unsigned_to_nat(0u);
x_90 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_91 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_88, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_116; uint8_t x_117; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_116 = lean_array_get_size(x_93);
x_117 = lean_nat_dec_lt(x_89, x_116);
if (x_117 == 0)
{
lean_dec(x_116);
lean_dec(x_93);
x_94 = lean_box(0);
goto block_115;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_116, x_116);
if (x_118 == 0)
{
lean_dec(x_116);
lean_dec(x_93);
x_94 = lean_box(0);
goto block_115;
}
else
{
lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; 
x_119 = lean_box(0);
x_120 = 0;
x_121 = lean_usize_of_nat(x_116);
lean_dec(x_116);
lean_inc_ref(x_4);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_93, x_120, x_121, x_119, x_4);
lean_dec(x_93);
lean_dec_ref(x_122);
x_94 = lean_box(0);
goto block_115;
}
}
block_115:
{
lean_object* x_95; 
lean_inc_ref(x_2);
x_95 = l_Lake_GitRepo_getHeadRevision(x_2, x_90);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = lean_array_get_size(x_97);
x_99 = lean_nat_dec_lt(x_89, x_98);
if (x_99 == 0)
{
lean_dec(x_98);
lean_dec(x_97);
x_36 = x_92;
x_37 = x_96;
x_38 = lean_box(0);
goto block_79;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_98, x_98);
if (x_100 == 0)
{
lean_dec(x_98);
lean_dec(x_97);
x_36 = x_92;
x_37 = x_96;
x_38 = lean_box(0);
goto block_79;
}
else
{
lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; 
x_101 = lean_box(0);
x_102 = 0;
x_103 = lean_usize_of_nat(x_98);
lean_dec(x_98);
lean_inc_ref(x_4);
x_104 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_97, x_102, x_103, x_101, x_4);
lean_dec(x_97);
lean_dec_ref(x_104);
x_36 = x_92;
x_37 = x_96;
x_38 = lean_box(0);
goto block_79;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_92);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = lean_ctor_get(x_95, 1);
lean_inc(x_105);
lean_dec_ref(x_95);
x_106 = lean_array_get_size(x_105);
x_107 = lean_nat_dec_lt(x_89, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_4);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
else
{
uint8_t x_110; 
x_110 = lean_nat_dec_le(x_106, x_106);
if (x_110 == 0)
{
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_4);
x_80 = lean_box(0);
goto block_83;
}
else
{
lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; 
x_111 = lean_box(0);
x_112 = 0;
x_113 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_114 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_105, x_112, x_113, x_111, x_4);
lean_dec(x_105);
lean_dec_ref(x_114);
x_80 = lean_box(0);
goto block_83;
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_91, 1);
lean_inc(x_123);
lean_dec_ref(x_91);
x_124 = lean_array_get_size(x_123);
x_125 = lean_nat_dec_lt(x_89, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_4);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_124, x_124);
if (x_128 == 0)
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_4);
x_84 = lean_box(0);
goto block_87;
}
else
{
lean_object* x_129; size_t x_130; size_t x_131; lean_object* x_132; 
x_129 = lean_box(0);
x_130 = 0;
x_131 = lean_usize_of_nat(x_124);
lean_dec(x_124);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_123, x_130, x_131, x_129, x_4);
lean_dec(x_123);
lean_dec_ref(x_132);
x_84 = lean_box(0);
goto block_87;
}
}
}
block_19:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
lean_dec_ref(x_2);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = 2;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_2(x_4, x_16, lean_box(0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
block_31:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_20);
x_25 = lean_nat_dec_lt(x_21, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_20);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_20);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_27 = lean_box(0);
x_28 = 0;
x_29 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc_ref(x_4);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_20, x_28, x_29, x_27, x_4);
lean_dec_ref(x_20);
lean_dec_ref(x_30);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
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
block_79:
{
uint8_t x_39; 
x_39 = lean_string_dec_eq(x_37, x_36);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_41 = lean_string_append(x_1, x_40);
x_42 = lean_string_append(x_41, x_36);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
lean_inc_ref(x_4);
x_47 = lean_apply_2(x_4, x_46, lean_box(0));
x_48 = lean_unsigned_to_nat(0u);
x_49 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_50 = l_Lake_GitRepo_checkoutDetach(x_36, x_2, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_48, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_4);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_4);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_51);
return x_57;
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_box(0);
x_59 = 0;
x_60 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_52, x_59, x_60, x_58, x_4);
lean_dec(x_52);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_51);
return x_61;
}
else
{
lean_object* x_64; 
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_51);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
lean_dec_ref(x_50);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_48, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_4);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_66, x_66);
if (x_70 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_4);
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = 0;
x_73 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_74 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_65, x_72, x_73, x_71, x_4);
lean_dec(x_65);
lean_dec_ref(x_74);
x_32 = lean_box(0);
goto block_35;
}
}
}
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_36);
lean_inc_ref(x_2);
x_75 = l_Lake_GitRepo_hasNoDiff(x_2);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (x_75 == 0)
{
x_20 = x_77;
x_21 = x_76;
x_22 = x_39;
x_23 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_78; 
x_78 = 0;
x_20 = x_77;
x_21 = x_76;
x_22 = x_78;
x_23 = lean_box(0);
goto block_31;
}
}
}
block_83:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
block_87:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0_spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": cloning ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_49; lean_object* x_53; lean_object* x_105; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_1);
x_110 = lean_string_append(x_1, x_109);
x_111 = lean_string_append(x_110, x_3);
x_112 = 1;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
lean_inc_ref(x_5);
x_114 = lean_apply_2(x_5, x_113, lean_box(0));
x_115 = lean_unsigned_to_nat(0u);
x_116 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_117 = l_Lake_GitRepo_clone(x_3, x_2, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_array_get_size(x_118);
x_120 = lean_nat_dec_lt(x_115, x_119);
if (x_120 == 0)
{
lean_dec(x_119);
lean_dec(x_118);
x_53 = lean_box(0);
goto block_104;
}
else
{
uint8_t x_121; 
x_121 = lean_nat_dec_le(x_119, x_119);
if (x_121 == 0)
{
lean_dec(x_119);
lean_dec(x_118);
x_53 = lean_box(0);
goto block_104;
}
else
{
lean_object* x_122; size_t x_123; size_t x_124; lean_object* x_125; 
x_122 = lean_box(0);
x_123 = 0;
x_124 = lean_usize_of_nat(x_119);
lean_dec(x_119);
lean_inc_ref(x_5);
x_125 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_118, x_123, x_124, x_122, x_5);
lean_dec(x_118);
lean_dec_ref(x_125);
x_53 = lean_box(0);
goto block_104;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
lean_dec_ref(x_117);
x_127 = lean_array_get_size(x_126);
x_128 = lean_nat_dec_lt(x_115, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec_ref(x_5);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_le(x_127, x_127);
if (x_131 == 0)
{
lean_dec(x_127);
lean_dec(x_126);
lean_dec_ref(x_5);
x_105 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_132; size_t x_133; size_t x_134; lean_object* x_135; 
x_132 = lean_box(0);
x_133 = 0;
x_134 = lean_usize_of_nat(x_127);
lean_dec(x_127);
x_135 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_126, x_133, x_134, x_132, x_5);
lean_dec(x_126);
lean_dec_ref(x_135);
x_105 = lean_box(0);
goto block_108;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_48:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_14 = lean_string_append(x_1, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_5);
x_20 = lean_apply_2(x_5, x_19, lean_box(0));
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_23 = l_Lake_GitRepo_checkoutDetach(x_11, x_2, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_5);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_26, x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_5);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_24);
return x_30;
}
else
{
lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_box(0);
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_25, x_32, x_33, x_31, x_5);
lean_dec(x_25);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_24);
return x_34;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_24);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec_ref(x_23);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_21, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_5);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_5);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_44 = lean_box(0);
x_45 = 0;
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_38, x_45, x_46, x_44, x_5);
lean_dec(x_38);
lean_dec_ref(x_47);
x_7 = lean_box(0);
goto block_10;
}
}
}
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
block_104:
{
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_4);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_57 = lean_unsigned_to_nat(0u);
x_58 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_59 = l_Lake_GitRepo_resolveRemoteRevision(x_55, x_56, x_2, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_free_object(x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_array_get_size(x_61);
x_63 = lean_nat_dec_lt(x_57, x_62);
if (x_63 == 0)
{
lean_dec(x_62);
lean_dec(x_61);
x_11 = x_60;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_62, x_62);
if (x_64 == 0)
{
lean_dec(x_62);
lean_dec(x_61);
x_11 = x_60;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_65 = lean_box(0);
x_66 = 0;
x_67 = lean_usize_of_nat(x_62);
lean_dec(x_62);
lean_inc_ref(x_5);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_61, x_66, x_67, x_65, x_5);
lean_dec(x_61);
lean_dec_ref(x_68);
x_11 = x_60;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_dec_ref(x_59);
x_70 = lean_array_get_size(x_69);
x_71 = lean_nat_dec_lt(x_57, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_5);
x_72 = lean_box(0);
lean_ctor_set(x_4, 0, x_72);
return x_4;
}
else
{
uint8_t x_73; 
lean_free_object(x_4);
x_73 = lean_nat_dec_le(x_70, x_70);
if (x_73 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_5);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_69, x_75, x_76, x_74, x_5);
lean_dec(x_69);
lean_dec_ref(x_77);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
lean_dec(x_4);
x_79 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_82 = l_Lake_GitRepo_resolveRemoteRevision(x_78, x_79, x_2, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = lean_array_get_size(x_84);
x_86 = lean_nat_dec_lt(x_80, x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_84);
x_11 = x_83;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_85, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec(x_84);
x_11 = x_83;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; 
x_88 = lean_box(0);
x_89 = 0;
x_90 = lean_usize_of_nat(x_85);
lean_dec(x_85);
lean_inc_ref(x_5);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_84, x_89, x_90, x_88, x_5);
lean_dec(x_84);
lean_dec_ref(x_91);
x_11 = x_83;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_dec_ref(x_82);
x_93 = lean_array_get_size(x_92);
x_94 = lean_nat_dec_lt(x_80, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec_ref(x_5);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_93, x_93);
if (x_97 == 0)
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec_ref(x_5);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; 
x_98 = lean_box(0);
x_99 = 0;
x_100 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_101 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_92, x_99, x_100, x_98, x_5);
lean_dec(x_92);
lean_dec_ref(x_101);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
block_108:
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
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
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_49; lean_object* x_53; lean_object* x_105; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_2);
x_110 = lean_string_append(x_2, x_109);
x_111 = lean_string_append(x_110, x_4);
x_112 = 1;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
lean_inc_ref(x_1);
x_114 = lean_apply_2(x_1, x_113, lean_box(0));
x_115 = lean_unsigned_to_nat(0u);
x_116 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_117 = l_Lake_GitRepo_clone(x_4, x_3, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_array_get_size(x_118);
x_120 = lean_nat_dec_lt(x_115, x_119);
if (x_120 == 0)
{
lean_dec(x_119);
lean_dec(x_118);
x_53 = lean_box(0);
goto block_104;
}
else
{
uint8_t x_121; 
x_121 = lean_nat_dec_le(x_119, x_119);
if (x_121 == 0)
{
lean_dec(x_119);
lean_dec(x_118);
x_53 = lean_box(0);
goto block_104;
}
else
{
lean_object* x_122; size_t x_123; size_t x_124; lean_object* x_125; 
x_122 = lean_box(0);
x_123 = 0;
x_124 = lean_usize_of_nat(x_119);
lean_dec(x_119);
lean_inc_ref(x_1);
x_125 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_118, x_123, x_124, x_122, x_1);
lean_dec(x_118);
lean_dec_ref(x_125);
x_53 = lean_box(0);
goto block_104;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
lean_dec_ref(x_117);
x_127 = lean_array_get_size(x_126);
x_128 = lean_nat_dec_lt(x_115, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec_ref(x_1);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_le(x_127, x_127);
if (x_131 == 0)
{
lean_dec(x_127);
lean_dec(x_126);
lean_dec_ref(x_1);
x_105 = lean_box(0);
goto block_108;
}
else
{
lean_object* x_132; size_t x_133; size_t x_134; lean_object* x_135; 
x_132 = lean_box(0);
x_133 = 0;
x_134 = lean_usize_of_nat(x_127);
lean_dec(x_127);
x_135 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_126, x_133, x_134, x_132, x_1);
lean_dec(x_126);
lean_dec_ref(x_135);
x_105 = lean_box(0);
goto block_108;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_48:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_14 = lean_string_append(x_2, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_1);
x_20 = lean_apply_2(x_1, x_19, lean_box(0));
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_23 = l_Lake_GitRepo_checkoutDetach(x_11, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_26, x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_24);
return x_30;
}
else
{
lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_box(0);
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_25, x_32, x_33, x_31, x_1);
lean_dec(x_25);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_24);
return x_34;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_24);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec_ref(x_23);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_21, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_44 = lean_box(0);
x_45 = 0;
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_38, x_45, x_46, x_44, x_1);
lean_dec(x_38);
lean_dec_ref(x_47);
x_7 = lean_box(0);
goto block_10;
}
}
}
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
block_104:
{
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_57 = lean_unsigned_to_nat(0u);
x_58 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_59 = l_Lake_GitRepo_resolveRemoteRevision(x_55, x_56, x_3, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_free_object(x_5);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_array_get_size(x_61);
x_63 = lean_nat_dec_lt(x_57, x_62);
if (x_63 == 0)
{
lean_dec(x_62);
lean_dec(x_61);
x_11 = x_60;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_62, x_62);
if (x_64 == 0)
{
lean_dec(x_62);
lean_dec(x_61);
x_11 = x_60;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_65 = lean_box(0);
x_66 = 0;
x_67 = lean_usize_of_nat(x_62);
lean_dec(x_62);
lean_inc_ref(x_1);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_61, x_66, x_67, x_65, x_1);
lean_dec(x_61);
lean_dec_ref(x_68);
x_11 = x_60;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_dec_ref(x_59);
x_70 = lean_array_get_size(x_69);
x_71 = lean_nat_dec_lt(x_57, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_1);
x_72 = lean_box(0);
lean_ctor_set(x_5, 0, x_72);
return x_5;
}
else
{
uint8_t x_73; 
lean_free_object(x_5);
x_73 = lean_nat_dec_le(x_70, x_70);
if (x_73 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_1);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_69, x_75, x_76, x_74, x_1);
lean_dec(x_69);
lean_dec_ref(x_77);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_5, 0);
lean_inc(x_78);
lean_dec(x_5);
x_79 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_82 = l_Lake_GitRepo_resolveRemoteRevision(x_78, x_79, x_3, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = lean_array_get_size(x_84);
x_86 = lean_nat_dec_lt(x_80, x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_84);
x_11 = x_83;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_85, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec(x_84);
x_11 = x_83;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; 
x_88 = lean_box(0);
x_89 = 0;
x_90 = lean_usize_of_nat(x_85);
lean_dec(x_85);
lean_inc_ref(x_1);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_84, x_89, x_90, x_88, x_1);
lean_dec(x_84);
lean_dec_ref(x_91);
x_11 = x_83;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_dec_ref(x_82);
x_93 = lean_array_get_size(x_92);
x_94 = lean_nat_dec_lt(x_80, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec_ref(x_1);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_93, x_93);
if (x_97 == 0)
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec_ref(x_1);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; 
x_98 = lean_box(0);
x_99 = 0;
x_100 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_101 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_92, x_99, x_100, x_98, x_1);
lean_dec(x_92);
lean_dec_ref(x_101);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
block_108:
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_80; lean_object* x_84; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_89 = lean_unsigned_to_nat(0u);
x_90 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_91 = l_Lake_GitRepo_findRemoteRevision(x_3, x_4, x_88, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_116; uint8_t x_117; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_116 = lean_array_get_size(x_93);
x_117 = lean_nat_dec_lt(x_89, x_116);
if (x_117 == 0)
{
lean_dec(x_116);
lean_dec(x_93);
x_94 = lean_box(0);
goto block_115;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_116, x_116);
if (x_118 == 0)
{
lean_dec(x_116);
lean_dec(x_93);
x_94 = lean_box(0);
goto block_115;
}
else
{
lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; 
x_119 = lean_box(0);
x_120 = 0;
x_121 = lean_usize_of_nat(x_116);
lean_dec(x_116);
lean_inc_ref(x_1);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_93, x_120, x_121, x_119, x_1);
lean_dec(x_93);
lean_dec_ref(x_122);
x_94 = lean_box(0);
goto block_115;
}
}
block_115:
{
lean_object* x_95; 
lean_inc_ref(x_3);
x_95 = l_Lake_GitRepo_getHeadRevision(x_3, x_90);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = lean_array_get_size(x_97);
x_99 = lean_nat_dec_lt(x_89, x_98);
if (x_99 == 0)
{
lean_dec(x_98);
lean_dec(x_97);
x_36 = x_92;
x_37 = x_96;
x_38 = lean_box(0);
goto block_79;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_98, x_98);
if (x_100 == 0)
{
lean_dec(x_98);
lean_dec(x_97);
x_36 = x_92;
x_37 = x_96;
x_38 = lean_box(0);
goto block_79;
}
else
{
lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; 
x_101 = lean_box(0);
x_102 = 0;
x_103 = lean_usize_of_nat(x_98);
lean_dec(x_98);
lean_inc_ref(x_1);
x_104 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_97, x_102, x_103, x_101, x_1);
lean_dec(x_97);
lean_dec_ref(x_104);
x_36 = x_92;
x_37 = x_96;
x_38 = lean_box(0);
goto block_79;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_92);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_105 = lean_ctor_get(x_95, 1);
lean_inc(x_105);
lean_dec_ref(x_95);
x_106 = lean_array_get_size(x_105);
x_107 = lean_nat_dec_lt(x_89, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_1);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
else
{
uint8_t x_110; 
x_110 = lean_nat_dec_le(x_106, x_106);
if (x_110 == 0)
{
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_1);
x_80 = lean_box(0);
goto block_83;
}
else
{
lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; 
x_111 = lean_box(0);
x_112 = 0;
x_113 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_114 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_105, x_112, x_113, x_111, x_1);
lean_dec(x_105);
lean_dec_ref(x_114);
x_80 = lean_box(0);
goto block_83;
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_123 = lean_ctor_get(x_91, 1);
lean_inc(x_123);
lean_dec_ref(x_91);
x_124 = lean_array_get_size(x_123);
x_125 = lean_nat_dec_lt(x_89, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_124, x_124);
if (x_128 == 0)
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_84 = lean_box(0);
goto block_87;
}
else
{
lean_object* x_129; size_t x_130; size_t x_131; lean_object* x_132; 
x_129 = lean_box(0);
x_130 = 0;
x_131 = lean_usize_of_nat(x_124);
lean_dec(x_124);
x_132 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_123, x_130, x_131, x_129, x_1);
lean_dec(x_123);
lean_dec_ref(x_132);
x_84 = lean_box(0);
goto block_87;
}
}
}
block_19:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec_ref(x_3);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = 2;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_2(x_1, x_16, lean_box(0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
block_31:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_20);
x_25 = lean_nat_dec_lt(x_21, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_20);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_20);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_27 = lean_box(0);
x_28 = 0;
x_29 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc_ref(x_1);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_20, x_28, x_29, x_27, x_1);
lean_dec_ref(x_20);
lean_dec_ref(x_30);
x_6 = x_22;
x_7 = lean_box(0);
goto block_19;
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
block_79:
{
uint8_t x_39; 
x_39 = lean_string_dec_eq(x_37, x_36);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
x_41 = lean_string_append(x_2, x_40);
x_42 = lean_string_append(x_41, x_36);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
lean_inc_ref(x_1);
x_47 = lean_apply_2(x_1, x_46, lean_box(0));
x_48 = lean_unsigned_to_nat(0u);
x_49 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_50 = l_Lake_GitRepo_checkoutDetach(x_36, x_3, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_48, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_1);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_1);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_51);
return x_57;
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_box(0);
x_59 = 0;
x_60 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_52, x_59, x_60, x_58, x_1);
lean_dec(x_52);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_51);
return x_61;
}
else
{
lean_object* x_64; 
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_51);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
lean_dec_ref(x_50);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_48, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_1);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_66, x_66);
if (x_70 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_1);
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = 0;
x_73 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_74 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_65, x_72, x_73, x_71, x_1);
lean_dec(x_65);
lean_dec_ref(x_74);
x_32 = lean_box(0);
goto block_35;
}
}
}
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_36);
lean_inc_ref(x_3);
x_75 = l_Lake_GitRepo_hasNoDiff(x_3);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (x_75 == 0)
{
x_20 = x_77;
x_21 = x_76;
x_22 = x_39;
x_23 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_78; 
x_78 = 0;
x_20 = x_77;
x_21 = x_76;
x_22 = x_78;
x_23 = lean_box(0);
goto block_31;
}
}
}
block_83:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
block_87:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; deleting '", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' and cloning again", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; you might need to delete '", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' manually", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
lean_inc_ref(x_2);
x_46 = l_Lake_GitRepo_getRemoteUrl_x3f(x_45, x_2);
x_47 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_46, 0);
lean_inc(x_57);
lean_dec_ref(x_46);
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
x_48 = x_63;
x_49 = lean_box(0);
goto block_56;
}
else
{
lean_dec_ref(x_61);
lean_dec(x_60);
x_48 = x_58;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec_ref(x_59);
x_48 = x_58;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec(x_57);
x_48 = x_58;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
uint8_t x_64; 
lean_dec(x_46);
x_64 = 0;
x_48 = x_64;
x_49 = lean_box(0);
goto block_56;
}
block_44:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
lean_inc_ref(x_1);
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_5);
x_17 = lean_apply_2(x_5, x_16, lean_box(0));
x_18 = l_IO_FS_removeDirAll(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_apply_2(x_5, x_24, lean_box(0));
x_26 = lean_box(0);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_io_error_to_string(x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_apply_2(x_5, x_30, lean_box(0));
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_3);
x_34 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
lean_inc_ref(x_1);
x_35 = lean_string_append(x_1, x_34);
x_36 = lean_string_append(x_35, x_2);
x_37 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
x_38 = lean_string_append(x_36, x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_inc_ref(x_5);
x_41 = lean_apply_2(x_5, x_40, lean_box(0));
x_42 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_3);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4);
return x_43;
}
}
block_56:
{
uint8_t x_50; 
x_50 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_50 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_51; 
x_51 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_51 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = 0;
x_54 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_47, x_53, x_54, x_52, x_5);
lean_dec_ref(x_55);
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
}
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_4);
return x_6;
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
uint8_t x_7; lean_object* x_8; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
lean_inc_ref(x_3);
x_46 = l_Lake_GitRepo_getRemoteUrl_x3f(x_45, x_3);
x_47 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_46, 0);
lean_inc(x_57);
lean_dec_ref(x_46);
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
x_48 = x_63;
x_49 = lean_box(0);
goto block_56;
}
else
{
lean_dec_ref(x_61);
lean_dec(x_60);
x_48 = x_58;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec_ref(x_59);
x_48 = x_58;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec(x_57);
x_48 = x_58;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
uint8_t x_64; 
lean_dec(x_46);
x_64 = 0;
x_48 = x_64;
x_49 = lean_box(0);
goto block_56;
}
block_44:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
lean_inc_ref(x_2);
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_1);
x_17 = lean_apply_2(x_1, x_16, lean_box(0));
x_18 = l_IO_FS_removeDirAll(x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_apply_2(x_1, x_24, lean_box(0));
x_26 = lean_box(0);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_io_error_to_string(x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_apply_2(x_1, x_30, lean_box(0));
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_4);
x_34 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
lean_inc_ref(x_2);
x_35 = lean_string_append(x_2, x_34);
x_36 = lean_string_append(x_35, x_3);
x_37 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4;
x_38 = lean_string_append(x_36, x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_inc_ref(x_1);
x_41 = lean_apply_2(x_1, x_40, lean_box(0));
x_42 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_4);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5);
return x_43;
}
}
block_56:
{
uint8_t x_50; 
x_50 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_50 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_51; 
x_51 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_51 == 0)
{
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = 0;
x_54 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_1);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_47, x_53, x_54, x_52, x_1);
lean_dec_ref(x_55);
x_7 = x_48;
x_8 = lean_box(0);
goto block_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_12; uint8_t x_13; 
x_7 = l_System_FilePath_isDir(x_2);
x_12 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_14 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = 0;
x_17 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_12, x_16, x_17, x_15, x_5);
lean_dec_ref(x_18);
x_8 = lean_box(0);
goto block_11;
}
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_10;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instInhabitedFilePath_default;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageEntry_default;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instInhabitedMaterializedDep_default___closed__2;
x_2 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_3 = l_Lake_instInhabitedMaterializedDep_default___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedMaterializedDep_default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep() {
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package not found on Reservoir.\n\n  If the package is on GitHub, you can add a Git source. For example:\n\n    require ...\n      from git \"https://github.com/", 157, 157);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n  or, if using TOML:\n\n    [[require]]\n    git = \"https://github.com/", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    ...\n", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" @ git ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    rev = ", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" @ ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    version = ", 15, 15);
return x_1;
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
x_27 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_4 = x_27;
x_5 = x_27;
goto block_26;
}
case 1:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
x_31 = l_String_quote(x_29);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_31);
x_32 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Std_Format_pretty(x_3, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
x_36 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
x_37 = lean_string_append(x_36, x_34);
lean_dec_ref(x_34);
x_4 = x_35;
x_5 = x_37;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
x_40 = l_String_quote(x_38);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Std_Format_pretty(x_41, x_42, x_43, x_43);
x_45 = lean_string_append(x_39, x_44);
x_46 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
x_47 = lean_string_append(x_46, x_44);
lean_dec_ref(x_44);
x_4 = x_45;
x_5 = x_47;
goto block_26;
}
}
default: 
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_49);
x_51 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8;
x_52 = l_String_quote(x_50);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_52);
x_53 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Std_Format_pretty(x_3, x_53, x_54, x_54);
x_56 = lean_string_append(x_51, x_55);
x_57 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9;
x_58 = lean_string_append(x_57, x_55);
lean_dec_ref(x_55);
x_4 = x_56;
x_5 = x_58;
goto block_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_59);
x_61 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8;
x_62 = l_String_quote(x_60);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Std_Format_pretty(x_63, x_64, x_65, x_65);
x_67 = lean_string_append(x_61, x_66);
x_68 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9;
x_69 = lean_string_append(x_68, x_66);
lean_dec_ref(x_66);
x_4 = x_67;
x_5 = x_69;
goto block_26;
}
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_inc_ref(x_1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_string_append(x_7, x_2);
x_9 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_1);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_string_append(x_12, x_2);
x_14 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_4);
lean_dec_ref(x_4);
x_17 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec_ref(x_1);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_14);
x_23 = lean_string_append(x_22, x_5);
lean_dec_ref(x_5);
x_24 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4;
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
static lean_object* _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultConfigFile;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
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
uint8_t x_7; lean_object* x_8; lean_object* x_12; uint8_t x_13; 
x_7 = l_System_FilePath_isDir(x_3);
x_12 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_13 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_13 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_14 == 0)
{
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = 0;
x_17 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_1);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_12, x_16, x_17, x_15, x_1);
lean_dec_ref(x_18);
x_8 = lean_box(0);
goto block_11;
}
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_89; 
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_37 = l_Lake_joinRelative(x_4, x_6);
x_89 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_89) == 0)
{
x_38 = x_7;
goto block_88;
}
else
{
lean_object* x_90; 
lean_dec_ref(x_7);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_38 = x_90;
goto block_88;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_10);
x_25 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_26 = lean_box(0);
lean_inc_ref(x_19);
lean_inc(x_18);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_2);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_8);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = l_Lake_joinRelative(x_6, x_34);
x_20 = lean_box(0);
x_21 = x_32;
x_22 = x_31;
x_23 = x_35;
goto block_30;
}
else
{
x_20 = lean_box(0);
x_21 = x_32;
x_22 = x_31;
x_23 = x_6;
goto block_30;
}
}
block_88:
{
lean_object* x_39; 
lean_inc(x_9);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_11);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_11, x_5, x_37, x_38, x_9);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_44 = l_Lake_GitRepo_getHeadRevision(x_37, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_42, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_50 = lean_box(0);
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_46, x_51, x_52, x_50, x_11);
lean_dec(x_46);
lean_dec_ref(x_53);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec_ref(x_44);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_42, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_11);
x_57 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_57);
return x_39;
}
else
{
uint8_t x_58; 
lean_free_object(x_39);
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_11);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_54, x_60, x_61, x_59, x_11);
lean_dec(x_54);
lean_dec_ref(x_62);
x_13 = lean_box(0);
goto block_16;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_39);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_65 = l_Lake_GitRepo_getHeadRevision(x_37, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_lt(x_63, x_68);
if (x_69 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_66;
x_33 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_68, x_68);
if (x_70 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_66;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = 0;
x_73 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_74 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_67, x_72, x_73, x_71, x_11);
lean_dec(x_67);
lean_dec_ref(x_74);
x_31 = x_38;
x_32 = x_66;
x_33 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_dec_ref(x_65);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_63, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_11);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_76, x_76);
if (x_80 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_11);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; 
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_75, x_82, x_83, x_81, x_11);
lean_dec(x_75);
lean_dec_ref(x_84);
x_13 = lean_box(0);
goto block_16;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_85 = !lean_is_exclusive(x_39);
if (x_85 == 0)
{
return x_39;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_39, 0);
lean_inc(x_86);
lean_dec(x_39);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
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
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_89; 
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
x_37 = l_Lake_joinRelative(x_5, x_7);
x_89 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_89) == 0)
{
x_38 = x_8;
goto block_88;
}
else
{
lean_object* x_90; 
lean_dec_ref(x_8);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_38 = x_90;
goto block_88;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_10);
lean_ctor_set(x_24, 3, x_11);
x_25 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_26 = lean_box(0);
lean_inc_ref(x_19);
lean_inc(x_18);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_3);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
x_35 = l_Lake_joinRelative(x_7, x_34);
x_20 = lean_box(0);
x_21 = x_32;
x_22 = x_31;
x_23 = x_35;
goto block_30;
}
else
{
x_20 = lean_box(0);
x_21 = x_32;
x_22 = x_31;
x_23 = x_7;
goto block_30;
}
}
block_88:
{
lean_object* x_39; 
lean_inc(x_10);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_39 = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_6, x_37, x_38, x_10);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_44 = l_Lake_GitRepo_getHeadRevision(x_37, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_42, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_50 = lean_box(0);
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_46, x_51, x_52, x_50, x_1);
lean_dec(x_46);
lean_dec_ref(x_53);
x_31 = x_38;
x_32 = x_45;
x_33 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec_ref(x_44);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_42, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_1);
x_57 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_57);
return x_39;
}
else
{
uint8_t x_58; 
lean_free_object(x_39);
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_54, x_60, x_61, x_59, x_1);
lean_dec(x_54);
lean_dec_ref(x_62);
x_13 = lean_box(0);
goto block_16;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_39);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_65 = l_Lake_GitRepo_getHeadRevision(x_37, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_lt(x_63, x_68);
if (x_69 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_66;
x_33 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_68, x_68);
if (x_70 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_66;
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = 0;
x_73 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_74 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_67, x_72, x_73, x_71, x_1);
lean_dec(x_67);
lean_dec_ref(x_74);
x_31 = x_38;
x_32 = x_66;
x_33 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_dec_ref(x_65);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_63, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_76, x_76);
if (x_80 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; 
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_75, x_82, x_83, x_81, x_1);
lean_dec(x_75);
lean_dec_ref(x_84);
x_13 = lean_box(0);
goto block_16;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_39);
if (x_85 == 0)
{
return x_39;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_39, 0);
lean_inc(x_86);
lean_dec(x_39);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_inc_ref(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = l_Lake_VerRange_test(x_1, x_10);
lean_dec_ref(x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
{
size_t _tmp_5 = x_13;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Git source not found on Reservoir", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": version `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` not found on Reservoir", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": could not fetch package versions: this may be a transient error or a bug in Lake or Reservoir", 95, 95);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": using version `", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` at revision `", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": could not materialize package: this may be a transient error or a bug in Lake or Reservoir", 92, 92);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git#", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid dependency version range: ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir", 92, 92);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
x_49 = lean_ctor_get(x_1, 2);
x_50 = lean_ctor_get(x_1, 3);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 1)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_50);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
lean_inc_ref(x_48);
lean_inc(x_47);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = l_Lake_joinRelative(x_6, x_129);
x_131 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_130);
lean_ctor_set(x_127, 0, x_130);
x_132 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_134, 0, x_47);
lean_ctor_set(x_134, 1, x_48);
lean_ctor_set(x_134, 2, x_132);
lean_ctor_set(x_134, 3, x_133);
lean_ctor_set(x_134, 4, x_127);
lean_ctor_set_uint8(x_134, sizeof(void*)*5, x_2);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_135);
return x_50;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_127, 0);
lean_inc(x_136);
lean_dec(x_127);
x_137 = l_Lake_joinRelative(x_6, x_136);
x_138 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_137);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_137);
x_140 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_142, 0, x_47);
lean_ctor_set(x_142, 1, x_48);
lean_ctor_set(x_142, 2, x_140);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 4, x_139);
lean_ctor_set_uint8(x_142, sizeof(void*)*5, x_2);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_143);
return x_50;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_153; 
lean_free_object(x_50);
lean_dec_ref(x_6);
x_144 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_127, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_127, 2);
lean_inc(x_146);
lean_dec_ref(x_127);
x_147 = 0;
lean_inc(x_47);
x_148 = l_Lean_Name_toString(x_47, x_147);
lean_inc_ref(x_144);
x_153 = l_Lake_Git_filterUrl_x3f(x_144);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_149 = x_154;
goto block_152;
}
else
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec_ref(x_153);
x_149 = x_155;
goto block_152;
}
block_152:
{
lean_object* x_150; lean_object* x_151; 
lean_inc_ref(x_148);
x_150 = l_Lake_joinRelative(x_5, x_148);
x_151 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_148, x_150, x_144, x_149, x_145, x_146);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_151;
}
}
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_50, 0);
lean_inc(x_156);
lean_dec(x_50);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc_ref(x_48);
lean_inc(x_47);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_157 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = l_Lake_joinRelative(x_6, x_157);
x_160 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 1, 0);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_159);
x_162 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_164, 0, x_47);
lean_ctor_set(x_164, 1, x_48);
lean_ctor_set(x_164, 2, x_162);
lean_ctor_set(x_164, 3, x_163);
lean_ctor_set(x_164, 4, x_161);
lean_ctor_set_uint8(x_164, sizeof(void*)*5, x_2);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_176; 
lean_dec_ref(x_6);
x_167 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_156, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_156, 2);
lean_inc(x_169);
lean_dec_ref(x_156);
x_170 = 0;
lean_inc(x_47);
x_171 = l_Lean_Name_toString(x_47, x_170);
lean_inc_ref(x_167);
x_176 = l_Lake_Git_filterUrl_x3f(x_167);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_172 = x_177;
goto block_175;
}
else
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec_ref(x_176);
x_172 = x_178;
goto block_175;
}
block_175:
{
lean_object* x_173; lean_object* x_174; 
lean_inc_ref(x_171);
x_173 = l_Lake_joinRelative(x_5, x_171);
x_174 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_171, x_173, x_167, x_172, x_168, x_169);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_174;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_50);
lean_dec_ref(x_6);
x_179 = lean_string_utf8_byte_size(x_48);
x_180 = lean_unsigned_to_nat(0u);
x_366 = lean_nat_dec_eq(x_179, x_180);
lean_dec(x_179);
if (x_366 == 0)
{
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_49, 0);
x_380 = l_Lake_Dependency_materialize___closed__9;
lean_inc(x_379);
x_381 = l_String_dropPrefix_x3f(x_379, x_380);
if (lean_obj_tag(x_381) == 1)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_ctor_get(x_383, 0);
lean_inc_ref(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_383, 2);
lean_inc(x_386);
lean_dec(x_383);
x_387 = lean_string_utf8_extract(x_384, x_385, x_386);
lean_dec(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_ctor_set(x_381, 0, x_387);
x_367 = x_381;
x_368 = lean_box(0);
goto block_378;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_388 = lean_ctor_get(x_381, 0);
lean_inc(x_388);
lean_dec(x_381);
x_389 = lean_ctor_get(x_388, 0);
lean_inc_ref(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_388, 2);
lean_inc(x_391);
lean_dec(x_388);
x_392 = lean_string_utf8_extract(x_389, x_390, x_391);
lean_dec(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_392);
x_367 = x_393;
x_368 = lean_box(0);
goto block_378;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_381);
x_394 = l_Lake_Dependency_materialize___closed__10;
x_395 = lean_string_utf8_byte_size(x_379);
lean_inc(x_379);
x_396 = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), x_379, x_394, x_180, x_395);
lean_dec(x_395);
if (lean_obj_tag(x_396) == 0)
{
uint8_t x_397; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
lean_object* x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_398 = lean_ctor_get(x_396, 0);
x_399 = 1;
x_400 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_399);
x_401 = l_Lake_Dependency_materialize___closed__11;
x_402 = lean_string_append(x_400, x_401);
x_403 = lean_string_append(x_402, x_398);
lean_dec(x_398);
x_404 = 3;
x_405 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*1, x_404);
x_406 = lean_apply_2(x_7, x_405, lean_box(0));
x_407 = lean_box(0);
lean_ctor_set_tag(x_396, 1);
lean_ctor_set(x_396, 0, x_407);
return x_396;
}
else
{
lean_object* x_408; uint8_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_408 = lean_ctor_get(x_396, 0);
lean_inc(x_408);
lean_dec(x_396);
x_409 = 1;
x_410 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_409);
x_411 = l_Lake_Dependency_materialize___closed__11;
x_412 = lean_string_append(x_410, x_411);
x_413 = lean_string_append(x_412, x_408);
lean_dec(x_408);
x_414 = 3;
x_415 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set_uint8(x_415, sizeof(void*)*1, x_414);
x_416 = lean_apply_2(x_7, x_415, lean_box(0));
x_417 = lean_box(0);
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_417);
return x_418;
}
}
else
{
uint8_t x_419; 
x_419 = !lean_is_exclusive(x_396);
if (x_419 == 0)
{
lean_ctor_set_tag(x_396, 2);
x_367 = x_396;
x_368 = lean_box(0);
goto block_378;
}
else
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_396, 0);
lean_inc(x_420);
lean_dec(x_396);
x_421 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_421, 0, x_420);
x_367 = x_421;
x_368 = lean_box(0);
goto block_378;
}
}
}
}
else
{
lean_object* x_422; 
x_422 = lean_box(0);
x_367 = x_422;
x_368 = lean_box(0);
goto block_378;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_423 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_366);
x_424 = l_Lake_Dependency_materialize___closed__12;
x_425 = lean_string_append(x_423, x_424);
x_426 = 3;
x_427 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set_uint8(x_427, sizeof(void*)*1, x_426);
x_428 = lean_apply_2(x_7, x_427, lean_box(0));
x_429 = lean_box(0);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_429);
return x_430;
}
block_198:
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_array_get_size(x_189);
x_192 = lean_nat_dec_lt(x_180, x_191);
if (x_192 == 0)
{
lean_dec(x_191);
lean_dec_ref(x_189);
x_69 = x_181;
x_70 = x_182;
x_71 = x_183;
x_72 = x_184;
x_73 = x_185;
x_74 = x_186;
x_75 = x_187;
x_76 = x_188;
x_77 = lean_box(0);
goto block_125;
}
else
{
uint8_t x_193; 
x_193 = lean_nat_dec_le(x_191, x_191);
if (x_193 == 0)
{
lean_dec(x_191);
lean_dec_ref(x_189);
x_69 = x_181;
x_70 = x_182;
x_71 = x_183;
x_72 = x_184;
x_73 = x_185;
x_74 = x_186;
x_75 = x_187;
x_76 = x_188;
x_77 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_194; size_t x_195; size_t x_196; lean_object* x_197; 
x_194 = lean_box(0);
x_195 = 0;
x_196 = lean_usize_of_nat(x_191);
lean_dec(x_191);
lean_inc_ref(x_7);
x_197 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_189, x_195, x_196, x_194, x_7);
lean_dec_ref(x_189);
lean_dec_ref(x_197);
x_69 = x_181;
x_70 = x_182;
x_71 = x_183;
x_72 = x_184;
x_73 = x_185;
x_74 = x_186;
x_75 = x_187;
x_76 = x_188;
x_77 = lean_box(0);
goto block_125;
}
}
}
block_352:
{
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec_ref(x_201);
lean_dec(x_199);
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_203 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_204 = lean_string_append(x_48, x_203);
x_205 = lean_string_append(x_204, x_200);
lean_dec_ref(x_200);
x_206 = l_Lake_Dependency_materialize___closed__8;
x_207 = lean_string_append(x_205, x_206);
x_208 = 3;
x_209 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set_uint8(x_209, sizeof(void*)*1, x_208);
x_210 = lean_apply_2(x_7, x_209, lean_box(0));
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
else
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_201);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_201, 0);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_free_object(x_201);
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_215 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_48, x_200, x_199);
lean_dec_ref(x_200);
x_216 = 3;
x_217 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set_uint8(x_217, sizeof(void*)*1, x_216);
x_218 = lean_apply_2(x_7, x_217, lean_box(0));
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_214, 0);
lean_inc(x_221);
lean_dec_ref(x_214);
x_222 = l_Lake_RegistryPkg_gitSrc_x3f(x_221);
if (lean_obj_tag(x_222) == 1)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_222, 0);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_225 = lean_ctor_get(x_224, 1);
lean_inc_ref(x_225);
x_226 = lean_ctor_get(x_224, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 4);
lean_inc(x_228);
lean_dec_ref(x_224);
x_229 = lean_ctor_get(x_221, 0);
lean_inc_ref(x_229);
x_230 = lean_ctor_get(x_221, 1);
lean_inc_ref(x_230);
lean_dec(x_221);
x_231 = l_Lake_joinRelative(x_5, x_229);
switch (lean_obj_tag(x_199)) {
case 0:
{
lean_object* x_232; 
lean_free_object(x_201);
lean_dec_ref(x_200);
x_232 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_233; 
lean_dec_ref(x_231);
lean_dec_ref(x_230);
lean_dec(x_228);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_233 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_233 == 0)
{
lean_object* x_234; 
lean_dec_ref(x_7);
x_234 = lean_box(0);
lean_ctor_set(x_222, 0, x_234);
return x_222;
}
else
{
uint8_t x_235; 
lean_free_object(x_222);
x_235 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_235 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_236; size_t x_237; size_t x_238; lean_object* x_239; 
x_236 = lean_box(0);
x_237 = 0;
x_238 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_239 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_232, x_237, x_238, x_236, x_7);
lean_dec_ref(x_239);
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_240; uint8_t x_241; 
lean_free_object(x_222);
x_240 = lean_ctor_get(x_227, 0);
lean_inc(x_240);
lean_dec_ref(x_227);
x_241 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_241 == 0)
{
x_36 = x_226;
x_37 = x_225;
x_38 = x_228;
x_39 = x_230;
x_40 = x_231;
x_41 = x_240;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_242; 
x_242 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_242 == 0)
{
x_36 = x_226;
x_37 = x_225;
x_38 = x_228;
x_39 = x_230;
x_40 = x_231;
x_41 = x_240;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_243; size_t x_244; size_t x_245; lean_object* x_246; 
x_243 = lean_box(0);
x_244 = 0;
x_245 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_246 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_232, x_244, x_245, x_243, x_7);
lean_dec_ref(x_246);
x_36 = x_226;
x_37 = x_225;
x_38 = x_228;
x_39 = x_230;
x_40 = x_231;
x_41 = x_240;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
}
case 1:
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
lean_dec(x_227);
lean_free_object(x_222);
lean_free_object(x_201);
lean_dec_ref(x_200);
x_247 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_247);
lean_dec_ref(x_199);
x_248 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_249 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_249 == 0)
{
x_36 = x_226;
x_37 = x_225;
x_38 = x_228;
x_39 = x_230;
x_40 = x_231;
x_41 = x_247;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_250; 
x_250 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_250 == 0)
{
x_36 = x_226;
x_37 = x_225;
x_38 = x_228;
x_39 = x_230;
x_40 = x_231;
x_41 = x_247;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_251; size_t x_252; size_t x_253; lean_object* x_254; 
x_251 = lean_box(0);
x_252 = 0;
x_253 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_254 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_248, x_252, x_253, x_251, x_7);
lean_dec_ref(x_254);
x_36 = x_226;
x_37 = x_225;
x_38 = x_228;
x_39 = x_230;
x_40 = x_231;
x_41 = x_247;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
default: 
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_227);
lean_free_object(x_222);
x_255 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_255);
lean_dec_ref(x_199);
x_256 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_257 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_200, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec_ref(x_257);
lean_ctor_set(x_201, 0, x_258);
x_181 = x_226;
x_182 = x_225;
x_183 = x_228;
x_184 = x_200;
x_185 = x_255;
x_186 = x_230;
x_187 = x_231;
x_188 = x_201;
x_189 = x_259;
x_190 = lean_box(0);
goto block_198;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
lean_dec_ref(x_257);
lean_ctor_set_tag(x_201, 0);
lean_ctor_set(x_201, 0, x_260);
x_181 = x_226;
x_182 = x_225;
x_183 = x_228;
x_184 = x_200;
x_185 = x_255;
x_186 = x_230;
x_187 = x_231;
x_188 = x_201;
x_189 = x_261;
x_190 = lean_box(0);
goto block_198;
}
}
}
}
else
{
lean_free_object(x_222);
lean_dec(x_224);
lean_free_object(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_221;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_222, 0);
lean_inc(x_262);
lean_dec(x_222);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc_ref(x_263);
x_264 = lean_ctor_get(x_262, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 3);
lean_inc(x_265);
x_266 = lean_ctor_get(x_262, 4);
lean_inc(x_266);
lean_dec_ref(x_262);
x_267 = lean_ctor_get(x_221, 0);
lean_inc_ref(x_267);
x_268 = lean_ctor_get(x_221, 1);
lean_inc_ref(x_268);
lean_dec(x_221);
x_269 = l_Lake_joinRelative(x_5, x_267);
switch (lean_obj_tag(x_199)) {
case 0:
{
lean_object* x_270; 
lean_free_object(x_201);
lean_dec_ref(x_200);
x_270 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_265) == 0)
{
uint8_t x_271; 
lean_dec_ref(x_269);
lean_dec_ref(x_268);
lean_dec(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_271 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
lean_dec_ref(x_7);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
else
{
uint8_t x_274; 
x_274 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_274 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_275; size_t x_276; size_t x_277; lean_object* x_278; 
x_275 = lean_box(0);
x_276 = 0;
x_277 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_278 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_270, x_276, x_277, x_275, x_7);
lean_dec_ref(x_278);
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_265, 0);
lean_inc(x_279);
lean_dec_ref(x_265);
x_280 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_280 == 0)
{
x_36 = x_264;
x_37 = x_263;
x_38 = x_266;
x_39 = x_268;
x_40 = x_269;
x_41 = x_279;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_281; 
x_281 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_281 == 0)
{
x_36 = x_264;
x_37 = x_263;
x_38 = x_266;
x_39 = x_268;
x_40 = x_269;
x_41 = x_279;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_282; size_t x_283; size_t x_284; lean_object* x_285; 
x_282 = lean_box(0);
x_283 = 0;
x_284 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_285 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_270, x_283, x_284, x_282, x_7);
lean_dec_ref(x_285);
x_36 = x_264;
x_37 = x_263;
x_38 = x_266;
x_39 = x_268;
x_40 = x_269;
x_41 = x_279;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
}
case 1:
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_dec(x_265);
lean_free_object(x_201);
lean_dec_ref(x_200);
x_286 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_286);
lean_dec_ref(x_199);
x_287 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_288 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_288 == 0)
{
x_36 = x_264;
x_37 = x_263;
x_38 = x_266;
x_39 = x_268;
x_40 = x_269;
x_41 = x_286;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_289; 
x_289 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_289 == 0)
{
x_36 = x_264;
x_37 = x_263;
x_38 = x_266;
x_39 = x_268;
x_40 = x_269;
x_41 = x_286;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_290; size_t x_291; size_t x_292; lean_object* x_293; 
x_290 = lean_box(0);
x_291 = 0;
x_292 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_293 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_287, x_291, x_292, x_290, x_7);
lean_dec_ref(x_293);
x_36 = x_264;
x_37 = x_263;
x_38 = x_266;
x_39 = x_268;
x_40 = x_269;
x_41 = x_286;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
default: 
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_265);
x_294 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_294);
lean_dec_ref(x_199);
x_295 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_296 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_200, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec_ref(x_296);
lean_ctor_set(x_201, 0, x_297);
x_181 = x_264;
x_182 = x_263;
x_183 = x_266;
x_184 = x_200;
x_185 = x_294;
x_186 = x_268;
x_187 = x_269;
x_188 = x_201;
x_189 = x_298;
x_190 = lean_box(0);
goto block_198;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_296, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
lean_dec_ref(x_296);
lean_ctor_set_tag(x_201, 0);
lean_ctor_set(x_201, 0, x_299);
x_181 = x_264;
x_182 = x_263;
x_183 = x_266;
x_184 = x_200;
x_185 = x_294;
x_186 = x_268;
x_187 = x_269;
x_188 = x_201;
x_189 = x_300;
x_190 = lean_box(0);
goto block_198;
}
}
}
}
else
{
lean_dec(x_262);
lean_free_object(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_221;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_dec(x_222);
lean_free_object(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_221;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_201, 0);
lean_inc(x_301);
lean_dec(x_201);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_302 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_48, x_200, x_199);
lean_dec_ref(x_200);
x_303 = 3;
x_304 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set_uint8(x_304, sizeof(void*)*1, x_303);
x_305 = lean_apply_2(x_7, x_304, lean_box(0));
x_306 = lean_box(0);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_301, 0);
lean_inc(x_308);
lean_dec_ref(x_301);
x_309 = l_Lake_RegistryPkg_gitSrc_x3f(x_308);
if (lean_obj_tag(x_309) == 1)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_311 = x_309;
} else {
 lean_dec_ref(x_309);
 x_311 = lean_box(0);
}
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_310, 1);
lean_inc_ref(x_312);
x_313 = lean_ctor_get(x_310, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_310, 3);
lean_inc(x_314);
x_315 = lean_ctor_get(x_310, 4);
lean_inc(x_315);
lean_dec_ref(x_310);
x_316 = lean_ctor_get(x_308, 0);
lean_inc_ref(x_316);
x_317 = lean_ctor_get(x_308, 1);
lean_inc_ref(x_317);
lean_dec(x_308);
x_318 = l_Lake_joinRelative(x_5, x_316);
switch (lean_obj_tag(x_199)) {
case 0:
{
lean_object* x_319; 
lean_dec_ref(x_200);
x_319 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_314) == 0)
{
uint8_t x_320; 
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec(x_315);
lean_dec(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_320 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
lean_dec_ref(x_7);
x_321 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_322 = lean_alloc_ctor(1, 1, 0);
} else {
 x_322 = x_311;
}
lean_ctor_set(x_322, 0, x_321);
return x_322;
}
else
{
uint8_t x_323; 
lean_dec(x_311);
x_323 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_323 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_324; size_t x_325; size_t x_326; lean_object* x_327; 
x_324 = lean_box(0);
x_325 = 0;
x_326 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_327 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_319, x_325, x_326, x_324, x_7);
lean_dec_ref(x_327);
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_328; uint8_t x_329; 
lean_dec(x_311);
x_328 = lean_ctor_get(x_314, 0);
lean_inc(x_328);
lean_dec_ref(x_314);
x_329 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_329 == 0)
{
x_36 = x_313;
x_37 = x_312;
x_38 = x_315;
x_39 = x_317;
x_40 = x_318;
x_41 = x_328;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_330; 
x_330 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_330 == 0)
{
x_36 = x_313;
x_37 = x_312;
x_38 = x_315;
x_39 = x_317;
x_40 = x_318;
x_41 = x_328;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_331; size_t x_332; size_t x_333; lean_object* x_334; 
x_331 = lean_box(0);
x_332 = 0;
x_333 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_334 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_319, x_332, x_333, x_331, x_7);
lean_dec_ref(x_334);
x_36 = x_313;
x_37 = x_312;
x_38 = x_315;
x_39 = x_317;
x_40 = x_318;
x_41 = x_328;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
}
case 1:
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec(x_314);
lean_dec(x_311);
lean_dec_ref(x_200);
x_335 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_335);
lean_dec_ref(x_199);
x_336 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_337 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_337 == 0)
{
x_36 = x_313;
x_37 = x_312;
x_38 = x_315;
x_39 = x_317;
x_40 = x_318;
x_41 = x_335;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_338; 
x_338 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_338 == 0)
{
x_36 = x_313;
x_37 = x_312;
x_38 = x_315;
x_39 = x_317;
x_40 = x_318;
x_41 = x_335;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_339; size_t x_340; size_t x_341; lean_object* x_342; 
x_339 = lean_box(0);
x_340 = 0;
x_341 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_342 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_336, x_340, x_341, x_339, x_7);
lean_dec_ref(x_342);
x_36 = x_313;
x_37 = x_312;
x_38 = x_315;
x_39 = x_317;
x_40 = x_318;
x_41 = x_335;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
default: 
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_314);
lean_dec(x_311);
x_343 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_343);
lean_dec_ref(x_199);
x_344 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_345 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_200, x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec_ref(x_345);
x_348 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_348, 0, x_346);
x_181 = x_313;
x_182 = x_312;
x_183 = x_315;
x_184 = x_200;
x_185 = x_343;
x_186 = x_317;
x_187 = x_318;
x_188 = x_348;
x_189 = x_347;
x_190 = lean_box(0);
goto block_198;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_345, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 1);
lean_inc(x_350);
lean_dec_ref(x_345);
x_351 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_351, 0, x_349);
x_181 = x_313;
x_182 = x_312;
x_183 = x_315;
x_184 = x_200;
x_185 = x_343;
x_186 = x_317;
x_187 = x_318;
x_188 = x_351;
x_189 = x_350;
x_190 = lean_box(0);
goto block_198;
}
}
}
}
else
{
lean_dec(x_311);
lean_dec(x_310);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_308;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
else
{
lean_dec(x_309);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_308;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
}
}
block_365:
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_array_get_size(x_356);
x_359 = lean_nat_dec_lt(x_180, x_358);
if (x_359 == 0)
{
lean_dec(x_358);
lean_dec_ref(x_356);
x_199 = x_353;
x_200 = x_354;
x_201 = x_355;
x_202 = lean_box(0);
goto block_352;
}
else
{
uint8_t x_360; 
x_360 = lean_nat_dec_le(x_358, x_358);
if (x_360 == 0)
{
lean_dec(x_358);
lean_dec_ref(x_356);
x_199 = x_353;
x_200 = x_354;
x_201 = x_355;
x_202 = lean_box(0);
goto block_352;
}
else
{
lean_object* x_361; size_t x_362; size_t x_363; lean_object* x_364; 
x_361 = lean_box(0);
x_362 = 0;
x_363 = lean_usize_of_nat(x_358);
lean_dec(x_358);
lean_inc_ref(x_7);
x_364 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_356, x_362, x_363, x_361, x_7);
lean_dec_ref(x_356);
lean_dec_ref(x_364);
x_199 = x_353;
x_200 = x_354;
x_201 = x_355;
x_202 = lean_box(0);
goto block_352;
}
}
}
block_378:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_inc(x_47);
x_369 = l_Lean_Name_toString(x_47, x_366);
x_370 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_371 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_48, x_369, x_370);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec_ref(x_371);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_372);
x_353 = x_367;
x_354 = x_369;
x_355 = x_374;
x_356 = x_373;
x_357 = lean_box(0);
goto block_365;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_371, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_371, 1);
lean_inc(x_376);
lean_dec_ref(x_371);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_375);
x_353 = x_367;
x_354 = x_369;
x_355 = x_377;
x_356 = x_376;
x_357 = lean_box(0);
goto block_365;
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
block_24:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = l_Lake_Dependency_materialize___closed__0;
x_18 = lean_string_append(x_16, x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_apply_2(x_14, x_20, lean_box(0));
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_29);
x_34 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_30, x_31, x_27, x_32, x_33, x_28, x_26);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_34;
}
block_46:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_44; 
x_44 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_25 = lean_box(0);
x_26 = x_42;
x_27 = x_37;
x_28 = x_38;
x_29 = x_41;
x_30 = x_39;
x_31 = x_40;
x_32 = x_44;
goto block_35;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec_ref(x_36);
x_25 = lean_box(0);
x_26 = x_42;
x_27 = x_37;
x_28 = x_38;
x_29 = x_41;
x_30 = x_39;
x_31 = x_40;
x_32 = x_45;
goto block_35;
}
}
block_68:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_53);
x_55 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_56 = lean_string_append(x_48, x_55);
x_57 = lean_string_append(x_56, x_52);
lean_dec_ref(x_52);
x_58 = l_Lake_Dependency_materialize___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_54);
lean_dec_ref(x_54);
x_61 = l_Lake_Dependency_materialize___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_apply_2(x_7, x_64, lean_box(0));
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
block_125:
{
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_78; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
x_80 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_81 = lean_string_append(x_48, x_80);
x_82 = lean_string_append(x_81, x_72);
lean_dec_ref(x_72);
x_83 = l_Lake_Dependency_materialize___closed__3;
x_84 = lean_string_append(x_82, x_83);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_apply_2(x_7, x_86, lean_box(0));
x_88 = lean_box(0);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_88);
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_76);
x_89 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_90 = lean_string_append(x_48, x_89);
x_91 = lean_string_append(x_90, x_72);
lean_dec_ref(x_72);
x_92 = l_Lake_Dependency_materialize___closed__3;
x_93 = lean_string_append(x_91, x_92);
x_94 = 3;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_apply_2(x_7, x_95, lean_box(0));
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_76, 0);
lean_inc(x_99);
lean_dec_ref(x_76);
x_100 = lean_box(0);
x_101 = l_Lake_Dependency_materialize___closed__4;
x_102 = lean_array_size(x_99);
x_103 = 0;
x_104 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_73, x_101, x_100, x_99, x_102, x_103, x_101);
lean_dec(x_99);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = lean_box(0);
x_52 = x_72;
x_53 = x_73;
goto block_68;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
if (lean_obj_tag(x_106) == 1)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_73);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_109);
lean_dec(x_107);
x_110 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
lean_inc_ref(x_48);
x_111 = lean_string_append(x_48, x_110);
x_112 = lean_string_append(x_111, x_72);
lean_dec_ref(x_72);
x_113 = l_Lake_Dependency_materialize___closed__5;
x_114 = lean_string_append(x_112, x_113);
x_115 = l_Lake_StdVer_toString(x_108);
x_116 = lean_string_append(x_114, x_115);
lean_dec_ref(x_115);
x_117 = l_Lake_Dependency_materialize___closed__6;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_string_append(x_118, x_109);
x_120 = l_Lake_Dependency_materialize___closed__7;
x_121 = lean_string_append(x_119, x_120);
x_122 = 1;
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_122);
lean_inc_ref(x_7);
x_124 = lean_apply_2(x_7, x_123, lean_box(0));
x_36 = x_69;
x_37 = x_70;
x_38 = x_71;
x_39 = x_74;
x_40 = x_75;
x_41 = x_109;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_dec(x_106);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = lean_box(0);
x_52 = x_72;
x_53 = x_73;
goto block_68;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
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
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_48; lean_object* x_49; uint8_t x_56; lean_object* x_57; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_79; lean_object* x_80; lean_object* x_81; uint8_t x_92; lean_object* x_93; lean_object* x_107; uint8_t x_108; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_13, 3);
lean_inc(x_25);
lean_dec_ref(x_13);
x_32 = 0;
lean_inc(x_22);
x_33 = l_Lean_Name_toString(x_22, x_32);
lean_inc_ref(x_33);
x_34 = l_Lake_joinRelative(x_4, x_33);
lean_inc_ref(x_34);
x_39 = l_Lake_joinRelative(x_3, x_34);
x_92 = l_System_FilePath_isDir(x_39);
x_107 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_108 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_108 == 0)
{
x_93 = lean_box(0);
goto block_106;
}
else
{
uint8_t x_109; 
x_109 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_109 == 0)
{
x_93 = lean_box(0);
goto block_106;
}
else
{
lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; 
x_110 = lean_box(0);
x_111 = 0;
x_112 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_113 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_107, x_111, x_112, x_110, x_5);
lean_dec_ref(x_113);
x_93 = lean_box(0);
goto block_106;
}
}
block_31:
{
lean_object* x_28; 
x_28 = l_Lake_Git_filterUrl_x3f(x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_7 = x_27;
x_8 = lean_box(0);
x_9 = x_29;
goto block_12;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_7 = x_27;
x_8 = lean_box(0);
x_9 = x_30;
goto block_12;
}
}
block_38:
{
if (lean_obj_tag(x_25) == 0)
{
x_26 = lean_box(0);
x_27 = x_34;
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec_ref(x_25);
x_37 = l_Lake_joinRelative(x_34, x_36);
x_26 = lean_box(0);
x_27 = x_37;
goto block_31;
}
}
block_47:
{
lean_object* x_43; 
x_43 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(x_5, x_33, x_39, x_42, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
x_35 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_44; 
lean_dec_ref(x_34);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
block_55:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_24);
x_51 = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(x_5, x_33, x_39, x_49, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_51);
x_35 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_52; 
lean_dec_ref(x_34);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
block_66:
{
if (x_56 == 0)
{
lean_dec_ref(x_39);
lean_dec_ref(x_33);
lean_dec_ref(x_5);
x_35 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_58 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
x_59 = lean_string_append(x_33, x_58);
x_60 = lean_string_append(x_59, x_39);
lean_dec_ref(x_39);
x_61 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = 2;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_apply_2(x_5, x_64, lean_box(0));
x_35 = lean_box(0);
goto block_38;
}
}
block_78:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_array_get_size(x_67);
x_72 = lean_nat_dec_lt(x_68, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec_ref(x_67);
x_56 = x_69;
x_57 = lean_box(0);
goto block_66;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_71, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec_ref(x_67);
x_56 = x_69;
x_57 = lean_box(0);
goto block_66;
}
else
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_71);
lean_dec(x_71);
lean_inc_ref(x_5);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_67, x_75, x_76, x_74, x_5);
lean_dec_ref(x_67);
lean_dec_ref(x_77);
x_56 = x_69;
x_57 = lean_box(0);
goto block_66;
}
}
}
block_91:
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_24);
lean_inc_ref(x_83);
x_84 = l_Option_instDecidableEq_decEq___redArg(x_82, x_80, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_2, 5);
x_86 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_85, x_22);
if (lean_obj_tag(x_86) == 0)
{
lean_inc_ref(x_23);
x_40 = lean_box(0);
x_41 = x_83;
x_42 = x_23;
goto block_47;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_40 = lean_box(0);
x_41 = x_83;
x_42 = x_87;
goto block_47;
}
}
else
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_83);
lean_inc_ref(x_39);
x_88 = l_Lake_GitRepo_hasNoDiff(x_39);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (x_88 == 0)
{
x_67 = x_90;
x_68 = x_89;
x_69 = x_79;
x_70 = lean_box(0);
goto block_78;
}
else
{
x_67 = x_90;
x_68 = x_89;
x_69 = x_32;
x_70 = lean_box(0);
goto block_78;
}
}
}
block_106:
{
if (x_92 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_2, 5);
x_95 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_94, x_22);
if (lean_obj_tag(x_95) == 0)
{
lean_inc_ref(x_23);
x_48 = lean_box(0);
x_49 = x_23;
goto block_55;
}
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_48 = lean_box(0);
x_49 = x_96;
goto block_55;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = l_Lake_PackageEntry_materialize___closed__0;
lean_inc_ref(x_39);
x_98 = l_Lake_GitRepo_resolveRevision_x3f(x_97, x_39);
x_99 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_100 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_100 == 0)
{
x_79 = x_92;
x_80 = x_98;
x_81 = lean_box(0);
goto block_91;
}
else
{
uint8_t x_101; 
x_101 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_101 == 0)
{
x_79 = x_92;
x_80 = x_98;
x_81 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_102; size_t x_103; size_t x_104; lean_object* x_105; 
x_102 = lean_box(0);
x_103 = 0;
x_104 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_5);
x_105 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_99, x_103, x_104, x_102, x_5);
lean_dec_ref(x_105);
x_79 = x_92;
x_80 = x_98;
x_81 = lean_box(0);
goto block_91;
}
}
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
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
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin);
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
res = initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4);
l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5);
l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7();
l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8 = _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8();
l_Lake_instInhabitedMaterializedDep_default___closed__0 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__0);
l_Lake_instInhabitedMaterializedDep_default___closed__1 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__1();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__1);
l_Lake_instInhabitedMaterializedDep_default___closed__2 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__2();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__2);
l_Lake_instInhabitedMaterializedDep_default___closed__3 = _init_l_Lake_instInhabitedMaterializedDep_default___closed__3();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default___closed__3);
l_Lake_instInhabitedMaterializedDep_default = _init_l_Lake_instInhabitedMaterializedDep_default();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__8);
l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9 = _init_l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__9);
l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0 = _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0();
lean_mark_persistent(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0);
l_Lake_Dependency_materialize___closed__0 = _init_l_Lake_Dependency_materialize___closed__0();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__0);
l_Lake_Dependency_materialize___closed__1 = _init_l_Lake_Dependency_materialize___closed__1();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__1);
l_Lake_Dependency_materialize___closed__2 = _init_l_Lake_Dependency_materialize___closed__2();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__2);
l_Lake_Dependency_materialize___closed__3 = _init_l_Lake_Dependency_materialize___closed__3();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__3);
l_Lake_Dependency_materialize___closed__4 = _init_l_Lake_Dependency_materialize___closed__4();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__4);
l_Lake_Dependency_materialize___closed__5 = _init_l_Lake_Dependency_materialize___closed__5();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__5);
l_Lake_Dependency_materialize___closed__6 = _init_l_Lake_Dependency_materialize___closed__6();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__6);
l_Lake_Dependency_materialize___closed__7 = _init_l_Lake_Dependency_materialize___closed__7();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__7);
l_Lake_Dependency_materialize___closed__8 = _init_l_Lake_Dependency_materialize___closed__8();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__8);
l_Lake_Dependency_materialize___closed__9 = _init_l_Lake_Dependency_materialize___closed__9();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__9);
l_Lake_Dependency_materialize___closed__10 = _init_l_Lake_Dependency_materialize___closed__10();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__10);
l_Lake_Dependency_materialize___closed__11 = _init_l_Lake_Dependency_materialize___closed__11();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__11);
l_Lake_Dependency_materialize___closed__12 = _init_l_Lake_Dependency_materialize___closed__12();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__12);
l_Lake_PackageEntry_materialize___closed__0 = _init_l_Lake_PackageEntry_materialize___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
