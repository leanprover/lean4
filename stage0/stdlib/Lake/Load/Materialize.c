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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__10;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lake_instInhabitedMaterializedDep_default___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_lt(x_20, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_21);
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
lean_dec_ref(x_21);
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
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_21, x_28, x_29, x_27, x_4);
lean_dec_ref(x_21);
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
x_20 = x_76;
x_21 = x_77;
x_22 = x_39;
x_23 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_78; 
x_78 = 0;
x_20 = x_76;
x_21 = x_77;
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
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_4);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_4, 0);
x_58 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_59 = lean_unsigned_to_nat(0u);
x_60 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_61 = l_Lake_GitRepo_resolveRemoteRevision(x_57, x_58, x_2, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_4);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_lt(x_59, x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
x_11 = x_62;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_64, x_64);
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
x_11 = x_62;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; 
x_67 = lean_box(0);
x_68 = 0;
x_69 = lean_usize_of_nat(x_64);
lean_dec(x_64);
lean_inc_ref(x_5);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_63, x_68, x_69, x_67, x_5);
lean_dec(x_63);
lean_dec_ref(x_70);
x_11 = x_62;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_dec_ref(x_61);
x_72 = lean_array_get_size(x_71);
x_73 = lean_nat_dec_lt(x_59, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_5);
x_74 = lean_box(0);
lean_ctor_set(x_4, 0, x_74);
return x_4;
}
else
{
uint8_t x_75; 
lean_free_object(x_4);
x_75 = lean_nat_dec_le(x_72, x_72);
if (x_75 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_5);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_71, x_77, x_78, x_76, x_5);
lean_dec(x_71);
lean_dec_ref(x_79);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
lean_dec(x_4);
x_81 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_82 = lean_unsigned_to_nat(0u);
x_83 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_84 = l_Lake_GitRepo_resolveRemoteRevision(x_80, x_81, x_2, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_array_get_size(x_86);
x_88 = lean_nat_dec_lt(x_82, x_87);
if (x_88 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_11 = x_85;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_87, x_87);
if (x_89 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_11 = x_85;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; 
x_90 = lean_box(0);
x_91 = 0;
x_92 = lean_usize_of_nat(x_87);
lean_dec(x_87);
lean_inc_ref(x_5);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_86, x_91, x_92, x_90, x_5);
lean_dec(x_86);
lean_dec_ref(x_93);
x_11 = x_85;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
lean_dec_ref(x_84);
x_95 = lean_array_get_size(x_94);
x_96 = lean_nat_dec_lt(x_82, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_5);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = lean_nat_dec_le(x_95, x_95);
if (x_99 == 0)
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_5);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_100; size_t x_101; size_t x_102; lean_object* x_103; 
x_100 = lean_box(0);
x_101 = 0;
x_102 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_94, x_101, x_102, x_100, x_5);
lean_dec(x_94);
lean_dec_ref(x_103);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
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
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_5);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_59 = lean_unsigned_to_nat(0u);
x_60 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_61 = l_Lake_GitRepo_resolveRemoteRevision(x_57, x_58, x_3, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_lt(x_59, x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
x_11 = x_62;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_64, x_64);
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
x_11 = x_62;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; 
x_67 = lean_box(0);
x_68 = 0;
x_69 = lean_usize_of_nat(x_64);
lean_dec(x_64);
lean_inc_ref(x_1);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_63, x_68, x_69, x_67, x_1);
lean_dec(x_63);
lean_dec_ref(x_70);
x_11 = x_62;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_dec_ref(x_61);
x_72 = lean_array_get_size(x_71);
x_73 = lean_nat_dec_lt(x_59, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_1);
x_74 = lean_box(0);
lean_ctor_set(x_5, 0, x_74);
return x_5;
}
else
{
uint8_t x_75; 
lean_free_object(x_5);
x_75 = lean_nat_dec_le(x_72, x_72);
if (x_75 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_1);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_71, x_77, x_78, x_76, x_1);
lean_dec(x_71);
lean_dec_ref(x_79);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_5, 0);
lean_inc(x_80);
lean_dec(x_5);
x_81 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__5;
x_82 = lean_unsigned_to_nat(0u);
x_83 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_84 = l_Lake_GitRepo_resolveRemoteRevision(x_80, x_81, x_3, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_array_get_size(x_86);
x_88 = lean_nat_dec_lt(x_82, x_87);
if (x_88 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_11 = x_85;
x_12 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_87, x_87);
if (x_89 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_11 = x_85;
x_12 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; 
x_90 = lean_box(0);
x_91 = 0;
x_92 = lean_usize_of_nat(x_87);
lean_dec(x_87);
lean_inc_ref(x_1);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_86, x_91, x_92, x_90, x_1);
lean_dec(x_86);
lean_dec_ref(x_93);
x_11 = x_85;
x_12 = lean_box(0);
goto block_48;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
lean_dec_ref(x_84);
x_95 = lean_array_get_size(x_94);
x_96 = lean_nat_dec_lt(x_82, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = lean_nat_dec_le(x_95, x_95);
if (x_99 == 0)
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_1);
x_49 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_100; size_t x_101; size_t x_102; lean_object* x_103; 
x_100 = lean_box(0);
x_101 = 0;
x_102 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_94, x_101, x_102, x_100, x_1);
lean_dec(x_94);
lean_dec_ref(x_103);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
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
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_lt(x_20, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_21);
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
lean_dec_ref(x_21);
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
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_21, x_28, x_29, x_27, x_1);
lean_dec_ref(x_21);
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
x_20 = x_76;
x_21 = x_77;
x_22 = x_39;
x_23 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_78; 
x_78 = 0;
x_20 = x_76;
x_21 = x_77;
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
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_57; 
x_57 = 0;
x_48 = x_57;
x_49 = lean_box(0);
goto block_56;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_46, 0);
lean_inc(x_58);
lean_dec_ref(x_46);
x_59 = lean_string_dec_eq(x_58, x_3);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_io_realpath(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc_ref(x_3);
x_62 = lean_io_realpath(x_3);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_string_dec_eq(x_61, x_63);
lean_dec(x_63);
lean_dec(x_61);
x_48 = x_64;
x_49 = lean_box(0);
goto block_56;
}
else
{
lean_dec_ref(x_62);
lean_dec(x_61);
x_48 = x_59;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec_ref(x_60);
x_48 = x_59;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec(x_58);
x_48 = x_59;
x_49 = lean_box(0);
goto block_56;
}
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
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_57; 
x_57 = 0;
x_48 = x_57;
x_49 = lean_box(0);
goto block_56;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_46, 0);
lean_inc(x_58);
lean_dec_ref(x_46);
x_59 = lean_string_dec_eq(x_58, x_4);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_io_realpath(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc_ref(x_4);
x_62 = lean_io_realpath(x_4);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_string_dec_eq(x_61, x_63);
lean_dec(x_63);
lean_dec(x_61);
x_48 = x_64;
x_49 = lean_box(0);
goto block_56;
}
else
{
lean_dec_ref(x_62);
lean_dec(x_61);
x_48 = x_59;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec_ref(x_60);
x_48 = x_59;
x_49 = lean_box(0);
goto block_56;
}
}
else
{
lean_dec(x_58);
x_48 = x_59;
x_49 = lean_box(0);
goto block_56;
}
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
lean_ctor_set(x_24, 0, x_20);
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
if (lean_obj_tag(x_10) == 0)
{
x_20 = x_31;
x_21 = x_32;
x_22 = lean_box(0);
x_23 = x_6;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = l_Lake_joinRelative(x_6, x_34);
x_20 = x_31;
x_21 = x_32;
x_22 = lean_box(0);
x_23 = x_35;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
if (lean_obj_tag(x_11) == 0)
{
x_20 = lean_box(0);
x_21 = x_32;
x_22 = x_31;
x_23 = x_7;
goto block_30;
}
else
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
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_313; lean_object* x_314; lean_object* x_315; 
lean_dec_ref(x_6);
x_126 = lean_string_utf8_byte_size(x_48);
x_127 = lean_unsigned_to_nat(0u);
x_313 = lean_nat_dec_eq(x_126, x_127);
lean_dec(x_126);
if (x_313 == 0)
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_326; 
x_326 = lean_box(0);
x_314 = x_326;
x_315 = lean_box(0);
goto block_325;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_49, 0);
x_328 = l_Lake_Dependency_materialize___closed__9;
lean_inc(x_327);
x_329 = l_String_dropPrefix_x3f(x_327, x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = l_Lake_Dependency_materialize___closed__10;
x_331 = lean_string_utf8_byte_size(x_327);
lean_inc(x_327);
x_332 = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), x_327, x_330, x_127, x_331);
lean_dec(x_331);
if (lean_obj_tag(x_332) == 0)
{
uint8_t x_333; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_333 = !lean_is_exclusive(x_332);
if (x_333 == 0)
{
lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_334 = lean_ctor_get(x_332, 0);
x_335 = 1;
x_336 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_335);
x_337 = l_Lake_Dependency_materialize___closed__11;
x_338 = lean_string_append(x_336, x_337);
x_339 = lean_string_append(x_338, x_334);
lean_dec(x_334);
x_340 = 3;
x_341 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set_uint8(x_341, sizeof(void*)*1, x_340);
x_342 = lean_apply_2(x_7, x_341, lean_box(0));
x_343 = lean_box(0);
lean_ctor_set_tag(x_332, 1);
lean_ctor_set(x_332, 0, x_343);
return x_332;
}
else
{
lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_344 = lean_ctor_get(x_332, 0);
lean_inc(x_344);
lean_dec(x_332);
x_345 = 1;
x_346 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_345);
x_347 = l_Lake_Dependency_materialize___closed__11;
x_348 = lean_string_append(x_346, x_347);
x_349 = lean_string_append(x_348, x_344);
lean_dec(x_344);
x_350 = 3;
x_351 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set_uint8(x_351, sizeof(void*)*1, x_350);
x_352 = lean_apply_2(x_7, x_351, lean_box(0));
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_353);
return x_354;
}
}
else
{
uint8_t x_355; 
x_355 = !lean_is_exclusive(x_332);
if (x_355 == 0)
{
lean_ctor_set_tag(x_332, 2);
x_314 = x_332;
x_315 = lean_box(0);
goto block_325;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_332, 0);
lean_inc(x_356);
lean_dec(x_332);
x_357 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_357, 0, x_356);
x_314 = x_357;
x_315 = lean_box(0);
goto block_325;
}
}
}
else
{
uint8_t x_358; 
x_358 = !lean_is_exclusive(x_329);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_359 = lean_ctor_get(x_329, 0);
x_360 = lean_ctor_get(x_359, 0);
lean_inc_ref(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 2);
lean_inc(x_362);
lean_dec(x_359);
x_363 = lean_string_utf8_extract(x_360, x_361, x_362);
lean_dec(x_362);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_ctor_set(x_329, 0, x_363);
x_314 = x_329;
x_315 = lean_box(0);
goto block_325;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_364 = lean_ctor_get(x_329, 0);
lean_inc(x_364);
lean_dec(x_329);
x_365 = lean_ctor_get(x_364, 0);
lean_inc_ref(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 2);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_string_utf8_extract(x_365, x_366, x_367);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_365);
x_369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_369, 0, x_368);
x_314 = x_369;
x_315 = lean_box(0);
goto block_325;
}
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_inc(x_47);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_370 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_313);
x_371 = l_Lake_Dependency_materialize___closed__12;
x_372 = lean_string_append(x_370, x_371);
x_373 = 3;
x_374 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_373);
x_375 = lean_apply_2(x_7, x_374, lean_box(0));
x_376 = lean_box(0);
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_376);
return x_377;
}
block_145:
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_array_get_size(x_136);
x_139 = lean_nat_dec_lt(x_127, x_138);
if (x_139 == 0)
{
lean_dec(x_138);
lean_dec_ref(x_136);
x_69 = x_128;
x_70 = x_129;
x_71 = x_130;
x_72 = x_131;
x_73 = x_133;
x_74 = x_132;
x_75 = x_134;
x_76 = x_135;
x_77 = lean_box(0);
goto block_125;
}
else
{
uint8_t x_140; 
x_140 = lean_nat_dec_le(x_138, x_138);
if (x_140 == 0)
{
lean_dec(x_138);
lean_dec_ref(x_136);
x_69 = x_128;
x_70 = x_129;
x_71 = x_130;
x_72 = x_131;
x_73 = x_133;
x_74 = x_132;
x_75 = x_134;
x_76 = x_135;
x_77 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_141; size_t x_142; size_t x_143; lean_object* x_144; 
x_141 = lean_box(0);
x_142 = 0;
x_143 = lean_usize_of_nat(x_138);
lean_dec(x_138);
lean_inc_ref(x_7);
x_144 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_136, x_142, x_143, x_141, x_7);
lean_dec_ref(x_136);
lean_dec_ref(x_144);
x_69 = x_128;
x_70 = x_129;
x_71 = x_130;
x_72 = x_131;
x_73 = x_133;
x_74 = x_132;
x_75 = x_134;
x_76 = x_135;
x_77 = lean_box(0);
goto block_125;
}
}
}
block_299:
{
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec_ref(x_148);
lean_dec(x_147);
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_150 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_151 = lean_string_append(x_48, x_150);
x_152 = lean_string_append(x_151, x_146);
lean_dec_ref(x_146);
x_153 = l_Lake_Dependency_materialize___closed__8;
x_154 = lean_string_append(x_152, x_153);
x_155 = 3;
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_apply_2(x_7, x_156, lean_box(0));
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
else
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_148);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_148, 0);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_free_object(x_148);
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_162 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_48, x_146, x_147);
lean_dec_ref(x_146);
x_163 = 3;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_apply_2(x_7, x_164, lean_box(0));
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_161, 0);
lean_inc(x_168);
lean_dec_ref(x_161);
x_169 = l_Lake_RegistryPkg_gitSrc_x3f(x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_free_object(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_168;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_169, 0);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_171, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 4);
lean_inc(x_175);
lean_dec_ref(x_171);
x_176 = lean_ctor_get(x_168, 0);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_168, 1);
lean_inc_ref(x_177);
lean_dec(x_168);
x_178 = l_Lake_joinRelative(x_5, x_176);
switch (lean_obj_tag(x_147)) {
case 0:
{
lean_object* x_179; 
lean_free_object(x_148);
lean_dec_ref(x_146);
x_179 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_180; 
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec(x_175);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_180 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec_ref(x_7);
x_181 = lean_box(0);
lean_ctor_set(x_169, 0, x_181);
return x_169;
}
else
{
uint8_t x_182; 
lean_free_object(x_169);
x_182 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_182 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_183; size_t x_184; size_t x_185; lean_object* x_186; 
x_183 = lean_box(0);
x_184 = 0;
x_185 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_186 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_179, x_184, x_185, x_183, x_7);
lean_dec_ref(x_186);
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_187; uint8_t x_188; 
lean_free_object(x_169);
x_187 = lean_ctor_get(x_174, 0);
lean_inc(x_187);
lean_dec_ref(x_174);
x_188 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_188 == 0)
{
x_36 = x_178;
x_37 = x_175;
x_38 = x_173;
x_39 = x_172;
x_40 = x_177;
x_41 = x_187;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_189; 
x_189 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_189 == 0)
{
x_36 = x_178;
x_37 = x_175;
x_38 = x_173;
x_39 = x_172;
x_40 = x_177;
x_41 = x_187;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_190; size_t x_191; size_t x_192; lean_object* x_193; 
x_190 = lean_box(0);
x_191 = 0;
x_192 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_193 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_179, x_191, x_192, x_190, x_7);
lean_dec_ref(x_193);
x_36 = x_178;
x_37 = x_175;
x_38 = x_173;
x_39 = x_172;
x_40 = x_177;
x_41 = x_187;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
}
case 1:
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_174);
lean_free_object(x_169);
lean_free_object(x_148);
lean_dec_ref(x_146);
x_194 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_194);
lean_dec_ref(x_147);
x_195 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_196 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_196 == 0)
{
x_36 = x_178;
x_37 = x_175;
x_38 = x_173;
x_39 = x_172;
x_40 = x_177;
x_41 = x_194;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_197; 
x_197 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_197 == 0)
{
x_36 = x_178;
x_37 = x_175;
x_38 = x_173;
x_39 = x_172;
x_40 = x_177;
x_41 = x_194;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_198; size_t x_199; size_t x_200; lean_object* x_201; 
x_198 = lean_box(0);
x_199 = 0;
x_200 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_201 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_195, x_199, x_200, x_198, x_7);
lean_dec_ref(x_201);
x_36 = x_178;
x_37 = x_175;
x_38 = x_173;
x_39 = x_172;
x_40 = x_177;
x_41 = x_194;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
default: 
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_174);
lean_free_object(x_169);
x_202 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_202);
lean_dec_ref(x_147);
x_203 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_204 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_146, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
lean_ctor_set(x_148, 0, x_205);
x_128 = x_178;
x_129 = x_175;
x_130 = x_202;
x_131 = x_146;
x_132 = x_173;
x_133 = x_172;
x_134 = x_177;
x_135 = x_148;
x_136 = x_206;
x_137 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_204, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_204, 1);
lean_inc(x_208);
lean_dec_ref(x_204);
lean_ctor_set_tag(x_148, 0);
lean_ctor_set(x_148, 0, x_207);
x_128 = x_178;
x_129 = x_175;
x_130 = x_202;
x_131 = x_146;
x_132 = x_173;
x_133 = x_172;
x_134 = x_177;
x_135 = x_148;
x_136 = x_208;
x_137 = lean_box(0);
goto block_145;
}
}
}
}
else
{
lean_free_object(x_169);
lean_dec_ref(x_171);
lean_free_object(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_168;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_169, 0);
lean_inc(x_209);
lean_dec(x_169);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_209, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_209, 4);
lean_inc(x_213);
lean_dec_ref(x_209);
x_214 = lean_ctor_get(x_168, 0);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_168, 1);
lean_inc_ref(x_215);
lean_dec(x_168);
x_216 = l_Lake_joinRelative(x_5, x_214);
switch (lean_obj_tag(x_147)) {
case 0:
{
lean_object* x_217; 
lean_free_object(x_148);
lean_dec_ref(x_146);
x_217 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_218; 
lean_dec_ref(x_216);
lean_dec_ref(x_215);
lean_dec(x_213);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_218 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec_ref(x_7);
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
else
{
uint8_t x_221; 
x_221 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_221 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_222; size_t x_223; size_t x_224; lean_object* x_225; 
x_222 = lean_box(0);
x_223 = 0;
x_224 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_225 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_217, x_223, x_224, x_222, x_7);
lean_dec_ref(x_225);
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_212, 0);
lean_inc(x_226);
lean_dec_ref(x_212);
x_227 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_227 == 0)
{
x_36 = x_216;
x_37 = x_213;
x_38 = x_211;
x_39 = x_210;
x_40 = x_215;
x_41 = x_226;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_228; 
x_228 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_228 == 0)
{
x_36 = x_216;
x_37 = x_213;
x_38 = x_211;
x_39 = x_210;
x_40 = x_215;
x_41 = x_226;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_229; size_t x_230; size_t x_231; lean_object* x_232; 
x_229 = lean_box(0);
x_230 = 0;
x_231 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_232 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_217, x_230, x_231, x_229, x_7);
lean_dec_ref(x_232);
x_36 = x_216;
x_37 = x_213;
x_38 = x_211;
x_39 = x_210;
x_40 = x_215;
x_41 = x_226;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
}
case 1:
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
lean_dec(x_212);
lean_free_object(x_148);
lean_dec_ref(x_146);
x_233 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_233);
lean_dec_ref(x_147);
x_234 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_235 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_235 == 0)
{
x_36 = x_216;
x_37 = x_213;
x_38 = x_211;
x_39 = x_210;
x_40 = x_215;
x_41 = x_233;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_236; 
x_236 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_236 == 0)
{
x_36 = x_216;
x_37 = x_213;
x_38 = x_211;
x_39 = x_210;
x_40 = x_215;
x_41 = x_233;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_237; size_t x_238; size_t x_239; lean_object* x_240; 
x_237 = lean_box(0);
x_238 = 0;
x_239 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_240 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_234, x_238, x_239, x_237, x_7);
lean_dec_ref(x_240);
x_36 = x_216;
x_37 = x_213;
x_38 = x_211;
x_39 = x_210;
x_40 = x_215;
x_41 = x_233;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
default: 
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_212);
x_241 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_241);
lean_dec_ref(x_147);
x_242 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_243 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_146, x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec_ref(x_243);
lean_ctor_set(x_148, 0, x_244);
x_128 = x_216;
x_129 = x_213;
x_130 = x_241;
x_131 = x_146;
x_132 = x_211;
x_133 = x_210;
x_134 = x_215;
x_135 = x_148;
x_136 = x_245;
x_137 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
lean_dec_ref(x_243);
lean_ctor_set_tag(x_148, 0);
lean_ctor_set(x_148, 0, x_246);
x_128 = x_216;
x_129 = x_213;
x_130 = x_241;
x_131 = x_146;
x_132 = x_211;
x_133 = x_210;
x_134 = x_215;
x_135 = x_148;
x_136 = x_247;
x_137 = lean_box(0);
goto block_145;
}
}
}
}
else
{
lean_dec_ref(x_209);
lean_free_object(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_168;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
}
}
else
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_148, 0);
lean_inc(x_248);
lean_dec(x_148);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_inc_ref(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_249 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(x_48, x_146, x_147);
lean_dec_ref(x_146);
x_250 = 3;
x_251 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*1, x_250);
x_252 = lean_apply_2(x_7, x_251, lean_box(0));
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_253);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_248, 0);
lean_inc(x_255);
lean_dec_ref(x_248);
x_256 = l_Lake_RegistryPkg_gitSrc_x3f(x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_255;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_259 = lean_ctor_get(x_257, 1);
lean_inc_ref(x_259);
x_260 = lean_ctor_get(x_257, 2);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 3);
lean_inc(x_261);
x_262 = lean_ctor_get(x_257, 4);
lean_inc(x_262);
lean_dec_ref(x_257);
x_263 = lean_ctor_get(x_255, 0);
lean_inc_ref(x_263);
x_264 = lean_ctor_get(x_255, 1);
lean_inc_ref(x_264);
lean_dec(x_255);
x_265 = l_Lake_joinRelative(x_5, x_263);
switch (lean_obj_tag(x_147)) {
case 0:
{
lean_object* x_266; 
lean_dec_ref(x_146);
x_266 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_267; 
lean_dec_ref(x_265);
lean_dec_ref(x_264);
lean_dec(x_262);
lean_dec(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_267 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec_ref(x_7);
x_268 = lean_box(0);
if (lean_is_scalar(x_258)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_258;
}
lean_ctor_set(x_269, 0, x_268);
return x_269;
}
else
{
uint8_t x_270; 
lean_dec(x_258);
x_270 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_270 == 0)
{
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_271; size_t x_272; size_t x_273; lean_object* x_274; 
x_271 = lean_box(0);
x_272 = 0;
x_273 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
x_274 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_266, x_272, x_273, x_271, x_7);
lean_dec_ref(x_274);
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_275; uint8_t x_276; 
lean_dec(x_258);
x_275 = lean_ctor_get(x_261, 0);
lean_inc(x_275);
lean_dec_ref(x_261);
x_276 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_276 == 0)
{
x_36 = x_265;
x_37 = x_262;
x_38 = x_260;
x_39 = x_259;
x_40 = x_264;
x_41 = x_275;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_277; 
x_277 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_277 == 0)
{
x_36 = x_265;
x_37 = x_262;
x_38 = x_260;
x_39 = x_259;
x_40 = x_264;
x_41 = x_275;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_278; size_t x_279; size_t x_280; lean_object* x_281; 
x_278 = lean_box(0);
x_279 = 0;
x_280 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_281 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_266, x_279, x_280, x_278, x_7);
lean_dec_ref(x_281);
x_36 = x_265;
x_37 = x_262;
x_38 = x_260;
x_39 = x_259;
x_40 = x_264;
x_41 = x_275;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
}
case 1:
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_261);
lean_dec(x_258);
lean_dec_ref(x_146);
x_282 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_282);
lean_dec_ref(x_147);
x_283 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
x_284 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6;
if (x_284 == 0)
{
x_36 = x_265;
x_37 = x_262;
x_38 = x_260;
x_39 = x_259;
x_40 = x_264;
x_41 = x_282;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_285; 
x_285 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7;
if (x_285 == 0)
{
x_36 = x_265;
x_37 = x_262;
x_38 = x_260;
x_39 = x_259;
x_40 = x_264;
x_41 = x_282;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_286; size_t x_287; size_t x_288; lean_object* x_289; 
x_286 = lean_box(0);
x_287 = 0;
x_288 = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__8;
lean_inc_ref(x_7);
x_289 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_283, x_287, x_288, x_286, x_7);
lean_dec_ref(x_289);
x_36 = x_265;
x_37 = x_262;
x_38 = x_260;
x_39 = x_259;
x_40 = x_264;
x_41 = x_282;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
default: 
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_261);
lean_dec(x_258);
x_290 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_290);
lean_dec_ref(x_147);
x_291 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_292 = l_Lake_Reservoir_fetchPkgVersions(x_3, x_48, x_146, x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec_ref(x_292);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_293);
x_128 = x_265;
x_129 = x_262;
x_130 = x_290;
x_131 = x_146;
x_132 = x_260;
x_133 = x_259;
x_134 = x_264;
x_135 = x_295;
x_136 = x_294;
x_137 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_292, 1);
lean_inc(x_297);
lean_dec_ref(x_292);
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_296);
x_128 = x_265;
x_129 = x_262;
x_130 = x_290;
x_131 = x_146;
x_132 = x_260;
x_133 = x_259;
x_134 = x_264;
x_135 = x_298;
x_136 = x_297;
x_137 = lean_box(0);
goto block_145;
}
}
}
}
else
{
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = x_255;
x_14 = x_7;
x_15 = lean_box(0);
goto block_24;
}
}
}
}
}
}
block_312:
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_array_get_size(x_303);
x_306 = lean_nat_dec_lt(x_127, x_305);
if (x_306 == 0)
{
lean_dec(x_305);
lean_dec_ref(x_303);
x_146 = x_300;
x_147 = x_301;
x_148 = x_302;
x_149 = lean_box(0);
goto block_299;
}
else
{
uint8_t x_307; 
x_307 = lean_nat_dec_le(x_305, x_305);
if (x_307 == 0)
{
lean_dec(x_305);
lean_dec_ref(x_303);
x_146 = x_300;
x_147 = x_301;
x_148 = x_302;
x_149 = lean_box(0);
goto block_299;
}
else
{
lean_object* x_308; size_t x_309; size_t x_310; lean_object* x_311; 
x_308 = lean_box(0);
x_309 = 0;
x_310 = lean_usize_of_nat(x_305);
lean_dec(x_305);
lean_inc_ref(x_7);
x_311 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(x_303, x_309, x_310, x_308, x_7);
lean_dec_ref(x_303);
lean_dec_ref(x_311);
x_146 = x_300;
x_147 = x_301;
x_148 = x_302;
x_149 = lean_box(0);
goto block_299;
}
}
}
block_325:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_inc(x_47);
x_316 = l_Lean_Name_toString(x_47, x_313);
x_317 = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
lean_inc_ref(x_48);
lean_inc_ref(x_3);
x_318 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_48, x_316, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec_ref(x_318);
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_319);
x_300 = x_316;
x_301 = x_314;
x_302 = x_321;
x_303 = x_320;
x_304 = lean_box(0);
goto block_312;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_318, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_dec_ref(x_318);
x_324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_324, 0, x_322);
x_300 = x_316;
x_301 = x_314;
x_302 = x_324;
x_303 = x_323;
x_304 = lean_box(0);
goto block_312;
}
}
}
else
{
uint8_t x_378; 
x_378 = !lean_is_exclusive(x_50);
if (x_378 == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_379) == 0)
{
uint8_t x_380; 
lean_inc_ref(x_48);
lean_inc(x_47);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_380 = !lean_is_exclusive(x_379);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_381 = lean_ctor_get(x_379, 0);
x_382 = l_Lake_joinRelative(x_6, x_381);
x_383 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_382);
lean_ctor_set(x_379, 0, x_382);
x_384 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_385 = lean_box(0);
x_386 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_386, 0, x_47);
lean_ctor_set(x_386, 1, x_48);
lean_ctor_set(x_386, 2, x_384);
lean_ctor_set(x_386, 3, x_385);
lean_ctor_set(x_386, 4, x_379);
lean_ctor_set_uint8(x_386, sizeof(void*)*5, x_2);
x_387 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_387, 0, x_382);
lean_ctor_set(x_387, 1, x_383);
lean_ctor_set(x_387, 2, x_386);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_387);
return x_50;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_388 = lean_ctor_get(x_379, 0);
lean_inc(x_388);
lean_dec(x_379);
x_389 = l_Lake_joinRelative(x_6, x_388);
x_390 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_389);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_392 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_393 = lean_box(0);
x_394 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_394, 0, x_47);
lean_ctor_set(x_394, 1, x_48);
lean_ctor_set(x_394, 2, x_392);
lean_ctor_set(x_394, 3, x_393);
lean_ctor_set(x_394, 4, x_391);
lean_ctor_set_uint8(x_394, sizeof(void*)*5, x_2);
x_395 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_395, 0, x_389);
lean_ctor_set(x_395, 1, x_390);
lean_ctor_set(x_395, 2, x_394);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_395);
return x_50;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_405; 
lean_free_object(x_50);
lean_dec_ref(x_6);
x_396 = lean_ctor_get(x_379, 0);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_379, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_379, 2);
lean_inc(x_398);
lean_dec_ref(x_379);
x_399 = 0;
lean_inc(x_47);
x_400 = l_Lean_Name_toString(x_47, x_399);
lean_inc_ref(x_396);
x_405 = l_Lake_Git_filterUrl_x3f(x_396);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; 
x_406 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_401 = x_406;
goto block_404;
}
else
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
lean_dec_ref(x_405);
x_401 = x_407;
goto block_404;
}
block_404:
{
lean_object* x_402; lean_object* x_403; 
lean_inc_ref(x_400);
x_402 = l_Lake_joinRelative(x_5, x_400);
x_403 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__1(x_7, x_1, x_2, x_3, x_4, x_400, x_402, x_396, x_401, x_397, x_398);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_403;
}
}
}
else
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_50, 0);
lean_inc(x_408);
lean_dec(x_50);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_inc_ref(x_48);
lean_inc(x_47);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_409 = lean_ctor_get(x_408, 0);
lean_inc_ref(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
x_411 = l_Lake_joinRelative(x_6, x_409);
x_412 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
lean_inc_ref(x_411);
if (lean_is_scalar(x_410)) {
 x_413 = lean_alloc_ctor(0, 1, 0);
} else {
 x_413 = x_410;
}
lean_ctor_set(x_413, 0, x_411);
x_414 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0;
x_415 = lean_box(0);
x_416 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_416, 0, x_47);
lean_ctor_set(x_416, 1, x_48);
lean_ctor_set(x_416, 2, x_414);
lean_ctor_set(x_416, 3, x_415);
lean_ctor_set(x_416, 4, x_413);
lean_ctor_set_uint8(x_416, sizeof(void*)*5, x_2);
x_417 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_417, 0, x_411);
lean_ctor_set(x_417, 1, x_412);
lean_ctor_set(x_417, 2, x_416);
x_418 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_418, 0, x_417);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_428; 
lean_dec_ref(x_6);
x_419 = lean_ctor_get(x_408, 0);
lean_inc_ref(x_419);
x_420 = lean_ctor_get(x_408, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_408, 2);
lean_inc(x_421);
lean_dec_ref(x_408);
x_422 = 0;
lean_inc(x_47);
x_423 = l_Lean_Name_toString(x_47, x_422);
lean_inc_ref(x_419);
x_428 = l_Lake_Git_filterUrl_x3f(x_419);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; 
x_429 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_424 = x_429;
goto block_427;
}
else
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
lean_dec_ref(x_428);
x_424 = x_430;
goto block_427;
}
block_427:
{
lean_object* x_425; lean_object* x_426; 
lean_inc_ref(x_423);
x_425 = l_Lake_joinRelative(x_5, x_423);
x_426 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__1(x_7, x_1, x_2, x_3, x_4, x_423, x_425, x_419, x_424, x_420, x_421);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_426;
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
lean_ctor_set(x_33, 0, x_27);
x_34 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_31, x_26, x_30, x_32, x_33, x_28, x_29);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_34;
}
block_46:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_44; 
x_44 = l_Lake_instInhabitedMaterializedDep_default___closed__1;
x_25 = lean_box(0);
x_26 = x_36;
x_27 = x_41;
x_28 = x_37;
x_29 = x_42;
x_30 = x_39;
x_31 = x_40;
x_32 = x_44;
goto block_35;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec_ref(x_38);
x_25 = lean_box(0);
x_26 = x_36;
x_27 = x_41;
x_28 = x_37;
x_29 = x_42;
x_30 = x_39;
x_31 = x_40;
x_32 = x_45;
goto block_35;
}
}
block_68:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_52);
x_55 = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
x_56 = lean_string_append(x_48, x_55);
x_57 = lean_string_append(x_56, x_53);
lean_dec_ref(x_53);
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
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
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
x_104 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__0(x_71, x_101, x_100, x_99, x_102, x_103, x_101);
lean_dec(x_99);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = lean_box(0);
x_52 = x_71;
x_53 = x_72;
goto block_68;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_inc_ref(x_48);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = lean_box(0);
x_52 = x_71;
x_53 = x_72;
goto block_68;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_71);
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
x_38 = x_74;
x_39 = x_73;
x_40 = x_75;
x_41 = x_109;
x_42 = x_7;
x_43 = lean_box(0);
goto block_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_14;
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
x_7 = lean_box(0);
x_8 = x_27;
x_9 = x_29;
goto block_12;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_7 = lean_box(0);
x_8 = x_27;
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
lean_ctor_set(x_10, 0, x_8);
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
