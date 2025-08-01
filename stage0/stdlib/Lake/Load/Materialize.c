// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: Lake.Util.Git Lake.Load.Manifest Lake.Config.Dependency Lake.Config.Package Lake.Reservoir
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__7;
static uint8_t l_Lake_updateGitRepo___closed__11;
static lean_object* l_Lake_updateGitRepo___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__3;
static lean_object* l_Lake_cloneGitPkg___closed__0;
static lean_object* l_Lake_pkgNotIndexed___closed__4;
static lean_object* l_Lake_PackageEntry_materialize___closed__1;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__6;
static lean_object* l_Lake_updateGitPkg___closed__18;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__1;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__9;
static lean_object* l_Lake_updateGitPkg___closed__13;
static lean_object* l_Lake_updateGitRepo___closed__8;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__5;
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitRepo___closed__9;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_materializeGitRepo___closed__1;
static lean_object* l_Lake_updateGitPkg___closed__8;
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__4;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__1;
uint8_t l_Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_6_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__6;
static lean_object* l_Lake_Dependency_materialize___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo___at___Lake_Dependency_materialize_materializeGit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__3;
static lean_object* l_Lake_updateGitPkg___closed__15;
static lean_object* l_Lake_PackageEntry_materialize___closed__3;
static lean_object* l_Lake_updateGitRepo___closed__5;
static lean_object* l_Lake_materializeGitRepo___closed__0;
static lean_object* l_Lake_updateGitRepo___closed__3;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__4;
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg___at___Lake_updateGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitRepo___closed__7;
static lean_object* l_Lake_updateGitRepo___closed__4;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__2;
static lean_object* l_Lake_pkgNotIndexed___closed__5;
static lean_object* l_Lake_updateGitPkg___closed__10;
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__3;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__2;
static lean_object* l_Lake_updateGitPkg___closed__17;
static lean_object* l_Lake_updateGitPkg___closed__16;
static lean_object* l_Lake_updateGitPkg___closed__19;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__0;
static lean_object* l_Lake_cloneGitPkg___closed__3;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___at___Lake_updateGitRepo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lake_updateGitRepo___closed__12;
lean_object* l_Lake_testProc(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__12;
static lean_object* l_Lake_PackageEntry_materialize___closed__0;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__7;
static lean_object* l_Lake_PackageEntry_materialize___closed__6;
static lean_object* l_Lake_Dependency_materialize___closed__0;
static lean_object* l_Lake_updateGitRepo___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_materializeGitRepo___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static size_t l_Lake_materializeGitRepo___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__4;
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
static lean_object* l_Lake_updateGitRepo___closed__6;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__2;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__2;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__6;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__0;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize_mkDep___closed__0;
static lean_object* l_Lake_updateGitRepo___closed__0;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__2;
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__3;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__14;
static uint8_t l_Lake_updateGitRepo___closed__10;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_updateGitPkg___closed__5;
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___at___Lake_materializeGitRepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
static lean_object* l_Lake_PackageEntry_materialize___closed__5;
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__2;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__7;
static lean_object* l_Lake_updateGitPkg___closed__11;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_2, x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateGitPkg___elam__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0___redArg(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": repository '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has local changes", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--detach", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__5;
x_2 = l_Lake_updateGitPkg___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__6;
x_2 = l_Lake_updateGitPkg___closed__9;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__11() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diff", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exit-code", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__13;
x_2 = l_Lake_updateGitPkg___closed__15;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__14;
x_2 = l_Lake_updateGitPkg___closed__16;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("origin", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_136; lean_object* x_140; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = l_Lake_updateGitPkg___closed__19;
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_147 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_144, x_146, x_5);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_192; uint8_t x_193; 
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec_ref(x_148);
x_192 = lean_array_get_size(x_151);
x_193 = lean_nat_dec_lt(x_145, x_192);
if (x_193 == 0)
{
lean_dec(x_192);
lean_dec(x_151);
x_152 = x_149;
goto block_191;
}
else
{
uint8_t x_194; 
x_194 = lean_nat_dec_le(x_192, x_192);
if (x_194 == 0)
{
lean_dec(x_192);
lean_dec(x_151);
x_152 = x_149;
goto block_191;
}
else
{
lean_object* x_195; size_t x_196; size_t x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_box(0);
x_196 = 0;
x_197 = lean_usize_of_nat(x_192);
lean_dec(x_192);
lean_inc_ref(x_4);
x_198 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_151, x_196, x_197, x_195, x_4, x_149);
lean_dec(x_151);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec_ref(x_198);
x_152 = x_199;
goto block_191;
}
}
block_191:
{
lean_object* x_153; lean_object* x_154; 
lean_inc_ref(x_2);
x_153 = l_Lake_GitRepo_getHeadRevision(x_2, x_146, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec_ref(x_154);
x_158 = lean_array_get_size(x_157);
x_159 = lean_nat_dec_lt(x_145, x_158);
if (x_159 == 0)
{
lean_dec(x_158);
lean_dec(x_157);
x_40 = x_150;
x_41 = x_156;
x_42 = x_155;
goto block_135;
}
else
{
uint8_t x_160; 
x_160 = lean_nat_dec_le(x_158, x_158);
if (x_160 == 0)
{
lean_dec(x_158);
lean_dec(x_157);
x_40 = x_150;
x_41 = x_156;
x_42 = x_155;
goto block_135;
}
else
{
lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_box(0);
x_162 = 0;
x_163 = lean_usize_of_nat(x_158);
lean_dec(x_158);
lean_inc_ref(x_4);
x_164 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_157, x_162, x_163, x_161, x_4, x_155);
lean_dec(x_157);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec_ref(x_164);
x_40 = x_150;
x_41 = x_156;
x_42 = x_165;
goto block_135;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_150);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_166 = !lean_is_exclusive(x_153);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_153, 1);
x_168 = lean_ctor_get(x_153, 0);
lean_dec(x_168);
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
lean_dec_ref(x_154);
x_170 = lean_array_get_size(x_169);
x_171 = lean_nat_dec_lt(x_145, x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_4);
x_172 = lean_box(0);
lean_ctor_set_tag(x_153, 1);
lean_ctor_set(x_153, 0, x_172);
return x_153;
}
else
{
uint8_t x_173; 
lean_free_object(x_153);
x_173 = lean_nat_dec_le(x_170, x_170);
if (x_173 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_4);
x_136 = x_167;
goto block_139;
}
else
{
lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_box(0);
x_175 = 0;
x_176 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_177 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_169, x_175, x_176, x_174, x_4, x_167);
lean_dec(x_169);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_136 = x_178;
goto block_139;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_153, 1);
lean_inc(x_179);
lean_dec(x_153);
x_180 = lean_ctor_get(x_154, 1);
lean_inc(x_180);
lean_dec_ref(x_154);
x_181 = lean_array_get_size(x_180);
x_182 = lean_nat_dec_lt(x_145, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_4);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_179);
return x_184;
}
else
{
uint8_t x_185; 
x_185 = lean_nat_dec_le(x_181, x_181);
if (x_185 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_4);
x_136 = x_179;
goto block_139;
}
else
{
lean_object* x_186; size_t x_187; size_t x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_box(0);
x_187 = 0;
x_188 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_189 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_180, x_187, x_188, x_186, x_4, x_179);
lean_dec(x_180);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec_ref(x_189);
x_136 = x_190;
goto block_139;
}
}
}
}
}
}
else
{
uint8_t x_200; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_200 = !lean_is_exclusive(x_147);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_147, 1);
x_202 = lean_ctor_get(x_147, 0);
lean_dec(x_202);
x_203 = lean_ctor_get(x_148, 1);
lean_inc(x_203);
lean_dec_ref(x_148);
x_204 = lean_array_get_size(x_203);
x_205 = lean_nat_dec_lt(x_145, x_204);
if (x_205 == 0)
{
lean_object* x_206; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec_ref(x_4);
x_206 = lean_box(0);
lean_ctor_set_tag(x_147, 1);
lean_ctor_set(x_147, 0, x_206);
return x_147;
}
else
{
uint8_t x_207; 
lean_free_object(x_147);
x_207 = lean_nat_dec_le(x_204, x_204);
if (x_207 == 0)
{
lean_dec(x_204);
lean_dec(x_203);
lean_dec_ref(x_4);
x_140 = x_201;
goto block_143;
}
else
{
lean_object* x_208; size_t x_209; size_t x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_box(0);
x_209 = 0;
x_210 = lean_usize_of_nat(x_204);
lean_dec(x_204);
x_211 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_203, x_209, x_210, x_208, x_4, x_201);
lean_dec(x_203);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec_ref(x_211);
x_140 = x_212;
goto block_143;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_147, 1);
lean_inc(x_213);
lean_dec(x_147);
x_214 = lean_ctor_get(x_148, 1);
lean_inc(x_214);
lean_dec_ref(x_148);
x_215 = lean_array_get_size(x_214);
x_216 = lean_nat_dec_lt(x_145, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_215);
lean_dec(x_214);
lean_dec_ref(x_4);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
return x_218;
}
else
{
uint8_t x_219; 
x_219 = lean_nat_dec_le(x_215, x_215);
if (x_219 == 0)
{
lean_dec(x_215);
lean_dec(x_214);
lean_dec_ref(x_4);
x_140 = x_213;
goto block_143;
}
else
{
lean_object* x_220; size_t x_221; size_t x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_box(0);
x_221 = 0;
x_222 = lean_usize_of_nat(x_215);
lean_dec(x_215);
x_223 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_214, x_221, x_222, x_220, x_4, x_213);
lean_dec(x_214);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec_ref(x_223);
x_140 = x_224;
goto block_143;
}
}
}
}
block_22:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = l_Lake_updateGitPkg___closed__0;
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
lean_dec_ref(x_2);
x_13 = l_Lake_updateGitPkg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = 2;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_2(x_4, x_16, x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
block_35:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_24);
x_28 = lean_nat_dec_lt(x_23, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_24);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_24);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_box(0);
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc_ref(x_4);
x_33 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_24, x_31, x_32, x_30, x_4, x_26);
lean_dec_ref(x_24);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_6 = x_25;
x_7 = x_34;
goto block_22;
}
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
block_135:
{
uint8_t x_43; 
x_43 = lean_string_dec_eq(x_41, x_40);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = l_Lake_updateGitPkg___closed__2;
x_45 = lean_string_append(x_1, x_44);
x_46 = lean_string_append(x_45, x_40);
x_47 = l_Lake_updateGitPkg___closed__3;
x_48 = lean_string_append(x_46, x_47);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
lean_inc_ref(x_4);
x_51 = lean_apply_2(x_4, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lake_updateGitPkg___closed__4;
x_55 = l_Lake_updateGitPkg___closed__7;
x_56 = l_Lake_updateGitPkg___closed__10;
x_57 = lean_array_push(x_56, x_40);
x_58 = lean_array_push(x_57, x_55);
x_59 = l_Lake_updateGitPkg___closed__11;
x_60 = l_Lake_updateGitPkg___closed__12;
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_2);
x_62 = 1;
x_63 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_61);
lean_ctor_set(x_63, 4, x_54);
lean_ctor_set_uint8(x_63, sizeof(void*)*5, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*5 + 1, x_43);
x_64 = l_Lake_proc(x_63, x_62, x_54, x_52);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_64, 1);
x_68 = lean_ctor_get(x_64, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec_ref(x_65);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_53, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_4);
lean_ctor_set(x_64, 0, x_69);
return x_64;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_71, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_4);
lean_ctor_set(x_64, 0, x_69);
return x_64;
}
else
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
lean_free_object(x_64);
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_77 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_70, x_75, x_76, x_74, x_4, x_67);
lean_dec(x_70);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_69);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_64, 1);
lean_inc(x_82);
lean_dec(x_64);
x_83 = lean_ctor_get(x_65, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_dec_ref(x_65);
x_85 = lean_array_get_size(x_84);
x_86 = lean_nat_dec_lt(x_53, x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_4);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_82);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_85, x_85);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_4);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
else
{
lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_box(0);
x_91 = 0;
x_92 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_93 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_84, x_91, x_92, x_90, x_4, x_82);
lean_dec(x_84);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_64);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_64, 1);
x_99 = lean_ctor_get(x_64, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_65, 1);
lean_inc(x_100);
lean_dec_ref(x_65);
x_101 = lean_array_get_size(x_100);
x_102 = lean_nat_dec_lt(x_53, x_101);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec_ref(x_4);
x_103 = lean_box(0);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_103);
return x_64;
}
else
{
uint8_t x_104; 
lean_free_object(x_64);
x_104 = lean_nat_dec_le(x_101, x_101);
if (x_104 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
lean_dec_ref(x_4);
x_36 = x_98;
goto block_39;
}
else
{
lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_box(0);
x_106 = 0;
x_107 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_108 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_100, x_106, x_107, x_105, x_4, x_98);
lean_dec(x_100);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_36 = x_109;
goto block_39;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_64, 1);
lean_inc(x_110);
lean_dec(x_64);
x_111 = lean_ctor_get(x_65, 1);
lean_inc(x_111);
lean_dec_ref(x_65);
x_112 = lean_array_get_size(x_111);
x_113 = lean_nat_dec_lt(x_53, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec_ref(x_4);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_110);
return x_115;
}
else
{
uint8_t x_116; 
x_116 = lean_nat_dec_le(x_112, x_112);
if (x_116 == 0)
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec_ref(x_4);
x_36 = x_110;
goto block_39;
}
else
{
lean_object* x_117; size_t x_118; size_t x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_box(0);
x_118 = 0;
x_119 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_120 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_111, x_118, x_119, x_117, x_4, x_110);
lean_dec(x_111);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec_ref(x_120);
x_36 = x_121;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec_ref(x_40);
x_122 = l_Lake_updateGitPkg___closed__17;
x_123 = l_Lake_updateGitPkg___closed__11;
x_124 = l_Lake_updateGitPkg___closed__12;
lean_inc_ref(x_2);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_2);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lake_updateGitPkg___closed__18;
x_128 = 0;
x_129 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_124);
lean_ctor_set(x_129, 2, x_122);
lean_ctor_set(x_129, 3, x_125);
lean_ctor_set(x_129, 4, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*5, x_43);
lean_ctor_set_uint8(x_129, sizeof(void*)*5 + 1, x_128);
x_130 = l_Lake_testProc(x_129, x_42);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec_ref(x_130);
x_23 = x_126;
x_24 = x_127;
x_25 = x_43;
x_26 = x_133;
goto block_35;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec_ref(x_130);
x_23 = x_126;
x_24 = x_127;
x_25 = x_128;
x_26 = x_134;
goto block_35;
}
}
}
block_139:
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateGitPkg___elam__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateGitPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0_spec__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": cloning ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clone", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_cloneGitPkg___closed__1;
x_2 = l_Lake_cloneGitPkg___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_93; lean_object* x_97; lean_object* x_143; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_147 = l_Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_1);
x_148 = lean_string_append(x_1, x_147);
x_149 = lean_string_append(x_148, x_3);
x_150 = 1;
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
lean_inc_ref(x_5);
x_152 = lean_apply_2(x_5, x_151, x_6);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = lean_unsigned_to_nat(0u);
x_155 = l_Lake_updateGitPkg___closed__4;
x_156 = l_Lake_updateGitPkg___closed__11;
x_157 = l_Lake_updateGitPkg___closed__12;
x_158 = l_Lake_cloneGitPkg___closed__3;
x_159 = lean_array_push(x_158, x_3);
lean_inc_ref(x_2);
x_160 = lean_array_push(x_159, x_2);
x_161 = lean_box(0);
x_162 = 1;
x_163 = 0;
x_164 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_164, 0, x_156);
lean_ctor_set(x_164, 1, x_157);
lean_ctor_set(x_164, 2, x_160);
lean_ctor_set(x_164, 3, x_161);
lean_ctor_set(x_164, 4, x_155);
lean_ctor_set_uint8(x_164, sizeof(void*)*5, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*5 + 1, x_163);
x_165 = l_Lake_proc(x_164, x_162, x_155, x_153);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_array_get_size(x_168);
x_170 = lean_nat_dec_lt(x_154, x_169);
if (x_170 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_97 = x_167;
goto block_142;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_169, x_169);
if (x_171 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_97 = x_167;
goto block_142;
}
else
{
lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_box(0);
x_173 = 0;
x_174 = lean_usize_of_nat(x_169);
lean_dec(x_169);
lean_inc_ref(x_5);
x_175 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_168, x_173, x_174, x_172, x_5, x_167);
lean_dec(x_168);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec_ref(x_175);
x_97 = x_176;
goto block_142;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_177 = !lean_is_exclusive(x_165);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_165, 1);
x_179 = lean_ctor_get(x_165, 0);
lean_dec(x_179);
x_180 = lean_ctor_get(x_166, 1);
lean_inc(x_180);
lean_dec_ref(x_166);
x_181 = lean_array_get_size(x_180);
x_182 = lean_nat_dec_lt(x_154, x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_5);
x_183 = lean_box(0);
lean_ctor_set_tag(x_165, 1);
lean_ctor_set(x_165, 0, x_183);
return x_165;
}
else
{
uint8_t x_184; 
lean_free_object(x_165);
x_184 = lean_nat_dec_le(x_181, x_181);
if (x_184 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_5);
x_143 = x_178;
goto block_146;
}
else
{
lean_object* x_185; size_t x_186; size_t x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_box(0);
x_186 = 0;
x_187 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_188 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_180, x_186, x_187, x_185, x_5, x_178);
lean_dec(x_180);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec_ref(x_188);
x_143 = x_189;
goto block_146;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_165, 1);
lean_inc(x_190);
lean_dec(x_165);
x_191 = lean_ctor_get(x_166, 1);
lean_inc(x_191);
lean_dec_ref(x_166);
x_192 = lean_array_get_size(x_191);
x_193 = lean_nat_dec_lt(x_154, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec_ref(x_5);
x_194 = lean_box(0);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
return x_195;
}
else
{
uint8_t x_196; 
x_196 = lean_nat_dec_le(x_192, x_192);
if (x_196 == 0)
{
lean_dec(x_192);
lean_dec(x_191);
lean_dec_ref(x_5);
x_143 = x_190;
goto block_146;
}
else
{
lean_object* x_197; size_t x_198; size_t x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_box(0);
x_198 = 0;
x_199 = lean_usize_of_nat(x_192);
lean_dec(x_192);
x_200 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_191, x_198, x_199, x_197, x_5, x_190);
lean_dec(x_191);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec_ref(x_200);
x_143 = x_201;
goto block_146;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_92:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_13 = l_Lake_updateGitPkg___closed__2;
x_14 = lean_string_append(x_1, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Lake_updateGitPkg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_5);
x_20 = lean_apply_2(x_5, x_19, x_12);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lake_updateGitPkg___closed__4;
x_24 = l_Lake_updateGitPkg___closed__7;
x_25 = l_Lake_updateGitPkg___closed__10;
x_26 = lean_array_push(x_25, x_11);
x_27 = lean_array_push(x_26, x_24);
x_28 = l_Lake_updateGitPkg___closed__11;
x_29 = l_Lake_updateGitPkg___closed__12;
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = 1;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5 + 1, x_32);
x_34 = l_Lake_proc(x_33, x_31, x_23, x_21);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec_ref(x_35);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_22, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_5);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_5);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_34);
x_44 = lean_box(0);
x_45 = 0;
x_46 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_47 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_40, x_45, x_46, x_44, x_5, x_37);
lean_dec(x_40);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_39);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec_ref(x_35);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_22, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_5);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_5);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_63 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_54, x_61, x_62, x_60, x_5, x_52);
lean_dec(x_54);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_34, 1);
x_69 = lean_ctor_get(x_34, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_dec_ref(x_35);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_22, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_5);
x_73 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_73);
return x_34;
}
else
{
uint8_t x_74; 
lean_free_object(x_34);
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_5);
x_7 = x_68;
goto block_10;
}
else
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = 0;
x_77 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_78 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_70, x_76, x_77, x_75, x_5, x_68);
lean_dec(x_70);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_7 = x_79;
goto block_10;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_dec_ref(x_35);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_22, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_5);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_82, x_82);
if (x_86 == 0)
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_5);
x_7 = x_80;
goto block_10;
}
else
{
lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_box(0);
x_88 = 0;
x_89 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_90 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_81, x_88, x_89, x_87, x_5, x_80);
lean_dec(x_81);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_7 = x_91;
goto block_10;
}
}
}
}
}
block_96:
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
block_142:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_4, 0);
lean_inc(x_100);
lean_dec_ref(x_4);
x_101 = l_Lake_updateGitPkg___closed__19;
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lake_updateGitPkg___closed__4;
lean_inc_ref(x_2);
x_104 = l_Lake_GitRepo_resolveRemoteRevision(x_100, x_101, x_2, x_103, x_97);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec_ref(x_105);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_102, x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_11 = x_107;
x_12 = x_106;
goto block_92;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_109, x_109);
if (x_111 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_11 = x_107;
x_12 = x_106;
goto block_92;
}
else
{
lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_box(0);
x_113 = 0;
x_114 = lean_usize_of_nat(x_109);
lean_dec(x_109);
lean_inc_ref(x_5);
x_115 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_108, x_113, x_114, x_112, x_5, x_106);
lean_dec(x_108);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_11 = x_107;
x_12 = x_116;
goto block_92;
}
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_117 = !lean_is_exclusive(x_104);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_104, 1);
x_119 = lean_ctor_get(x_104, 0);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 1);
lean_inc(x_120);
lean_dec_ref(x_105);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_102, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_5);
x_123 = lean_box(0);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 0, x_123);
return x_104;
}
else
{
uint8_t x_124; 
lean_free_object(x_104);
x_124 = lean_nat_dec_le(x_121, x_121);
if (x_124 == 0)
{
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_5);
x_93 = x_118;
goto block_96;
}
else
{
lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = 0;
x_127 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_128 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_120, x_126, x_127, x_125, x_5, x_118);
lean_dec(x_120);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec_ref(x_128);
x_93 = x_129;
goto block_96;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_104, 1);
lean_inc(x_130);
lean_dec(x_104);
x_131 = lean_ctor_get(x_105, 1);
lean_inc(x_131);
lean_dec_ref(x_105);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_102, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_5);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_132, x_132);
if (x_136 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_5);
x_93 = x_130;
goto block_96;
}
else
{
lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_box(0);
x_138 = 0;
x_139 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_140 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_131, x_138, x_139, x_137, x_5, x_130);
lean_dec(x_131);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_93 = x_141;
goto block_96;
}
}
}
}
}
}
block_146:
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg___at___Lake_updateGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_93; lean_object* x_97; lean_object* x_143; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_147 = l_Lake_cloneGitPkg___closed__0;
lean_inc_ref(x_2);
x_148 = lean_string_append(x_2, x_147);
x_149 = lean_string_append(x_148, x_4);
x_150 = 1;
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
lean_inc_ref(x_1);
x_152 = lean_apply_2(x_1, x_151, x_6);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = lean_unsigned_to_nat(0u);
x_155 = l_Lake_updateGitPkg___closed__4;
x_156 = l_Lake_updateGitPkg___closed__11;
x_157 = l_Lake_updateGitPkg___closed__12;
x_158 = l_Lake_cloneGitPkg___closed__3;
x_159 = lean_array_push(x_158, x_4);
lean_inc_ref(x_3);
x_160 = lean_array_push(x_159, x_3);
x_161 = lean_box(0);
x_162 = 1;
x_163 = 0;
x_164 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_164, 0, x_156);
lean_ctor_set(x_164, 1, x_157);
lean_ctor_set(x_164, 2, x_160);
lean_ctor_set(x_164, 3, x_161);
lean_ctor_set(x_164, 4, x_155);
lean_ctor_set_uint8(x_164, sizeof(void*)*5, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*5 + 1, x_163);
x_165 = l_Lake_proc(x_164, x_162, x_155, x_153);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_array_get_size(x_168);
x_170 = lean_nat_dec_lt(x_154, x_169);
if (x_170 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_97 = x_167;
goto block_142;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_169, x_169);
if (x_171 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_97 = x_167;
goto block_142;
}
else
{
lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_box(0);
x_173 = 0;
x_174 = lean_usize_of_nat(x_169);
lean_dec(x_169);
lean_inc_ref(x_1);
x_175 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_168, x_173, x_174, x_172, x_1, x_167);
lean_dec(x_168);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec_ref(x_175);
x_97 = x_176;
goto block_142;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_177 = !lean_is_exclusive(x_165);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_165, 1);
x_179 = lean_ctor_get(x_165, 0);
lean_dec(x_179);
x_180 = lean_ctor_get(x_166, 1);
lean_inc(x_180);
lean_dec_ref(x_166);
x_181 = lean_array_get_size(x_180);
x_182 = lean_nat_dec_lt(x_154, x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_1);
x_183 = lean_box(0);
lean_ctor_set_tag(x_165, 1);
lean_ctor_set(x_165, 0, x_183);
return x_165;
}
else
{
uint8_t x_184; 
lean_free_object(x_165);
x_184 = lean_nat_dec_le(x_181, x_181);
if (x_184 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_1);
x_143 = x_178;
goto block_146;
}
else
{
lean_object* x_185; size_t x_186; size_t x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_box(0);
x_186 = 0;
x_187 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_188 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_180, x_186, x_187, x_185, x_1, x_178);
lean_dec(x_180);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec_ref(x_188);
x_143 = x_189;
goto block_146;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_165, 1);
lean_inc(x_190);
lean_dec(x_165);
x_191 = lean_ctor_get(x_166, 1);
lean_inc(x_191);
lean_dec_ref(x_166);
x_192 = lean_array_get_size(x_191);
x_193 = lean_nat_dec_lt(x_154, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec_ref(x_1);
x_194 = lean_box(0);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
return x_195;
}
else
{
uint8_t x_196; 
x_196 = lean_nat_dec_le(x_192, x_192);
if (x_196 == 0)
{
lean_dec(x_192);
lean_dec(x_191);
lean_dec_ref(x_1);
x_143 = x_190;
goto block_146;
}
else
{
lean_object* x_197; size_t x_198; size_t x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_box(0);
x_198 = 0;
x_199 = lean_usize_of_nat(x_192);
lean_dec(x_192);
x_200 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_191, x_198, x_199, x_197, x_1, x_190);
lean_dec(x_191);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec_ref(x_200);
x_143 = x_201;
goto block_146;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_92:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_13 = l_Lake_updateGitPkg___closed__2;
x_14 = lean_string_append(x_2, x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Lake_updateGitPkg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_1);
x_20 = lean_apply_2(x_1, x_19, x_12);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lake_updateGitPkg___closed__4;
x_24 = l_Lake_updateGitPkg___closed__7;
x_25 = l_Lake_updateGitPkg___closed__10;
x_26 = lean_array_push(x_25, x_11);
x_27 = lean_array_push(x_26, x_24);
x_28 = l_Lake_updateGitPkg___closed__11;
x_29 = l_Lake_updateGitPkg___closed__12;
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = 1;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5 + 1, x_32);
x_34 = l_Lake_proc(x_33, x_31, x_23, x_21);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec_ref(x_35);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_22, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_1);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_1);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_34);
x_44 = lean_box(0);
x_45 = 0;
x_46 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_47 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_40, x_45, x_46, x_44, x_1, x_37);
lean_dec(x_40);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_39);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec_ref(x_35);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_22, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_63 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_54, x_61, x_62, x_60, x_1, x_52);
lean_dec(x_54);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_34, 1);
x_69 = lean_ctor_get(x_34, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_dec_ref(x_35);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_22, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_73 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_73);
return x_34;
}
else
{
uint8_t x_74; 
lean_free_object(x_34);
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_7 = x_68;
goto block_10;
}
else
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = 0;
x_77 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_78 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_70, x_76, x_77, x_75, x_1, x_68);
lean_dec(x_70);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_7 = x_79;
goto block_10;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_dec_ref(x_35);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_22, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_82, x_82);
if (x_86 == 0)
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_1);
x_7 = x_80;
goto block_10;
}
else
{
lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_box(0);
x_88 = 0;
x_89 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_90 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_81, x_88, x_89, x_87, x_1, x_80);
lean_dec(x_81);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_7 = x_91;
goto block_10;
}
}
}
}
}
block_96:
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
block_142:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_5, 0);
lean_inc(x_100);
lean_dec_ref(x_5);
x_101 = l_Lake_updateGitPkg___closed__19;
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_104 = l_Lake_GitRepo_resolveRemoteRevision(x_100, x_101, x_3, x_103, x_97);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec_ref(x_105);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_102, x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_11 = x_107;
x_12 = x_106;
goto block_92;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_109, x_109);
if (x_111 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_11 = x_107;
x_12 = x_106;
goto block_92;
}
else
{
lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_box(0);
x_113 = 0;
x_114 = lean_usize_of_nat(x_109);
lean_dec(x_109);
lean_inc_ref(x_1);
x_115 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_108, x_113, x_114, x_112, x_1, x_106);
lean_dec(x_108);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_11 = x_107;
x_12 = x_116;
goto block_92;
}
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_117 = !lean_is_exclusive(x_104);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_104, 1);
x_119 = lean_ctor_get(x_104, 0);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 1);
lean_inc(x_120);
lean_dec_ref(x_105);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_102, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_1);
x_123 = lean_box(0);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 0, x_123);
return x_104;
}
else
{
uint8_t x_124; 
lean_free_object(x_104);
x_124 = lean_nat_dec_le(x_121, x_121);
if (x_124 == 0)
{
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_1);
x_93 = x_118;
goto block_96;
}
else
{
lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = 0;
x_127 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_128 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_120, x_126, x_127, x_125, x_1, x_118);
lean_dec(x_120);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec_ref(x_128);
x_93 = x_129;
goto block_96;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_104, 1);
lean_inc(x_130);
lean_dec(x_104);
x_131 = lean_ctor_get(x_105, 1);
lean_inc(x_131);
lean_dec_ref(x_105);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_102, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_1);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_132, x_132);
if (x_136 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_1);
x_93 = x_130;
goto block_96;
}
else
{
lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_box(0);
x_138 = 0;
x_139 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_140 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_131, x_138, x_139, x_137, x_1, x_130);
lean_dec(x_131);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_93 = x_141;
goto block_96;
}
}
}
}
}
}
block_146:
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___at___Lake_updateGitRepo_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_136; lean_object* x_140; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = l_Lake_updateGitPkg___closed__19;
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lake_updateGitPkg___closed__4;
lean_inc_ref(x_3);
x_147 = l_Lake_GitRepo_findRemoteRevision(x_3, x_4, x_144, x_146, x_5);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_192; uint8_t x_193; 
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec_ref(x_148);
x_192 = lean_array_get_size(x_151);
x_193 = lean_nat_dec_lt(x_145, x_192);
if (x_193 == 0)
{
lean_dec(x_192);
lean_dec(x_151);
x_152 = x_149;
goto block_191;
}
else
{
uint8_t x_194; 
x_194 = lean_nat_dec_le(x_192, x_192);
if (x_194 == 0)
{
lean_dec(x_192);
lean_dec(x_151);
x_152 = x_149;
goto block_191;
}
else
{
lean_object* x_195; size_t x_196; size_t x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_box(0);
x_196 = 0;
x_197 = lean_usize_of_nat(x_192);
lean_dec(x_192);
lean_inc_ref(x_1);
x_198 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_151, x_196, x_197, x_195, x_1, x_149);
lean_dec(x_151);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec_ref(x_198);
x_152 = x_199;
goto block_191;
}
}
block_191:
{
lean_object* x_153; lean_object* x_154; 
lean_inc_ref(x_3);
x_153 = l_Lake_GitRepo_getHeadRevision(x_3, x_146, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec_ref(x_154);
x_158 = lean_array_get_size(x_157);
x_159 = lean_nat_dec_lt(x_145, x_158);
if (x_159 == 0)
{
lean_dec(x_158);
lean_dec(x_157);
x_40 = x_150;
x_41 = x_156;
x_42 = x_155;
goto block_135;
}
else
{
uint8_t x_160; 
x_160 = lean_nat_dec_le(x_158, x_158);
if (x_160 == 0)
{
lean_dec(x_158);
lean_dec(x_157);
x_40 = x_150;
x_41 = x_156;
x_42 = x_155;
goto block_135;
}
else
{
lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_box(0);
x_162 = 0;
x_163 = lean_usize_of_nat(x_158);
lean_dec(x_158);
lean_inc_ref(x_1);
x_164 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_157, x_162, x_163, x_161, x_1, x_155);
lean_dec(x_157);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec_ref(x_164);
x_40 = x_150;
x_41 = x_156;
x_42 = x_165;
goto block_135;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_150);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_166 = !lean_is_exclusive(x_153);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_153, 1);
x_168 = lean_ctor_get(x_153, 0);
lean_dec(x_168);
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
lean_dec_ref(x_154);
x_170 = lean_array_get_size(x_169);
x_171 = lean_nat_dec_lt(x_145, x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_1);
x_172 = lean_box(0);
lean_ctor_set_tag(x_153, 1);
lean_ctor_set(x_153, 0, x_172);
return x_153;
}
else
{
uint8_t x_173; 
lean_free_object(x_153);
x_173 = lean_nat_dec_le(x_170, x_170);
if (x_173 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_1);
x_136 = x_167;
goto block_139;
}
else
{
lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_box(0);
x_175 = 0;
x_176 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_177 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_169, x_175, x_176, x_174, x_1, x_167);
lean_dec(x_169);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_136 = x_178;
goto block_139;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_153, 1);
lean_inc(x_179);
lean_dec(x_153);
x_180 = lean_ctor_get(x_154, 1);
lean_inc(x_180);
lean_dec_ref(x_154);
x_181 = lean_array_get_size(x_180);
x_182 = lean_nat_dec_lt(x_145, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_1);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_179);
return x_184;
}
else
{
uint8_t x_185; 
x_185 = lean_nat_dec_le(x_181, x_181);
if (x_185 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_1);
x_136 = x_179;
goto block_139;
}
else
{
lean_object* x_186; size_t x_187; size_t x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_box(0);
x_187 = 0;
x_188 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_189 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_180, x_187, x_188, x_186, x_1, x_179);
lean_dec(x_180);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec_ref(x_189);
x_136 = x_190;
goto block_139;
}
}
}
}
}
}
else
{
uint8_t x_200; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_200 = !lean_is_exclusive(x_147);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_147, 1);
x_202 = lean_ctor_get(x_147, 0);
lean_dec(x_202);
x_203 = lean_ctor_get(x_148, 1);
lean_inc(x_203);
lean_dec_ref(x_148);
x_204 = lean_array_get_size(x_203);
x_205 = lean_nat_dec_lt(x_145, x_204);
if (x_205 == 0)
{
lean_object* x_206; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec_ref(x_1);
x_206 = lean_box(0);
lean_ctor_set_tag(x_147, 1);
lean_ctor_set(x_147, 0, x_206);
return x_147;
}
else
{
uint8_t x_207; 
lean_free_object(x_147);
x_207 = lean_nat_dec_le(x_204, x_204);
if (x_207 == 0)
{
lean_dec(x_204);
lean_dec(x_203);
lean_dec_ref(x_1);
x_140 = x_201;
goto block_143;
}
else
{
lean_object* x_208; size_t x_209; size_t x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_box(0);
x_209 = 0;
x_210 = lean_usize_of_nat(x_204);
lean_dec(x_204);
x_211 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_203, x_209, x_210, x_208, x_1, x_201);
lean_dec(x_203);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec_ref(x_211);
x_140 = x_212;
goto block_143;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_147, 1);
lean_inc(x_213);
lean_dec(x_147);
x_214 = lean_ctor_get(x_148, 1);
lean_inc(x_214);
lean_dec_ref(x_148);
x_215 = lean_array_get_size(x_214);
x_216 = lean_nat_dec_lt(x_145, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_215);
lean_dec(x_214);
lean_dec_ref(x_1);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
return x_218;
}
else
{
uint8_t x_219; 
x_219 = lean_nat_dec_le(x_215, x_215);
if (x_219 == 0)
{
lean_dec(x_215);
lean_dec(x_214);
lean_dec_ref(x_1);
x_140 = x_213;
goto block_143;
}
else
{
lean_object* x_220; size_t x_221; size_t x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_box(0);
x_221 = 0;
x_222 = lean_usize_of_nat(x_215);
lean_dec(x_215);
x_223 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_214, x_221, x_222, x_220, x_1, x_213);
lean_dec(x_214);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec_ref(x_223);
x_140 = x_224;
goto block_143;
}
}
}
}
block_22:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = l_Lake_updateGitPkg___closed__0;
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec_ref(x_3);
x_13 = l_Lake_updateGitPkg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = 2;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_2(x_1, x_16, x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
block_35:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_24);
x_28 = lean_nat_dec_lt(x_23, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_24);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec_ref(x_24);
x_6 = x_25;
x_7 = x_26;
goto block_22;
}
else
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_box(0);
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc_ref(x_1);
x_33 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_24, x_31, x_32, x_30, x_1, x_26);
lean_dec_ref(x_24);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_6 = x_25;
x_7 = x_34;
goto block_22;
}
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
block_135:
{
uint8_t x_43; 
x_43 = lean_string_dec_eq(x_41, x_40);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = l_Lake_updateGitPkg___closed__2;
x_45 = lean_string_append(x_2, x_44);
x_46 = lean_string_append(x_45, x_40);
x_47 = l_Lake_updateGitPkg___closed__3;
x_48 = lean_string_append(x_46, x_47);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
lean_inc_ref(x_1);
x_51 = lean_apply_2(x_1, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lake_updateGitPkg___closed__4;
x_55 = l_Lake_updateGitPkg___closed__7;
x_56 = l_Lake_updateGitPkg___closed__10;
x_57 = lean_array_push(x_56, x_40);
x_58 = lean_array_push(x_57, x_55);
x_59 = l_Lake_updateGitPkg___closed__11;
x_60 = l_Lake_updateGitPkg___closed__12;
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_3);
x_62 = 1;
x_63 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_61);
lean_ctor_set(x_63, 4, x_54);
lean_ctor_set_uint8(x_63, sizeof(void*)*5, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*5 + 1, x_43);
x_64 = l_Lake_proc(x_63, x_62, x_54, x_52);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_64, 1);
x_68 = lean_ctor_get(x_64, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec_ref(x_65);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_53, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
lean_ctor_set(x_64, 0, x_69);
return x_64;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_71, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
lean_ctor_set(x_64, 0, x_69);
return x_64;
}
else
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
lean_free_object(x_64);
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_77 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_70, x_75, x_76, x_74, x_1, x_67);
lean_dec(x_70);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_69);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_64, 1);
lean_inc(x_82);
lean_dec(x_64);
x_83 = lean_ctor_get(x_65, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_dec_ref(x_65);
x_85 = lean_array_get_size(x_84);
x_86 = lean_nat_dec_lt(x_53, x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_1);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_82);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_85, x_85);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
else
{
lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_box(0);
x_91 = 0;
x_92 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_93 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_84, x_91, x_92, x_90, x_1, x_82);
lean_dec(x_84);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_64);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_64, 1);
x_99 = lean_ctor_get(x_64, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_65, 1);
lean_inc(x_100);
lean_dec_ref(x_65);
x_101 = lean_array_get_size(x_100);
x_102 = lean_nat_dec_lt(x_53, x_101);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec_ref(x_1);
x_103 = lean_box(0);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_103);
return x_64;
}
else
{
uint8_t x_104; 
lean_free_object(x_64);
x_104 = lean_nat_dec_le(x_101, x_101);
if (x_104 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
lean_dec_ref(x_1);
x_36 = x_98;
goto block_39;
}
else
{
lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_box(0);
x_106 = 0;
x_107 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_108 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_100, x_106, x_107, x_105, x_1, x_98);
lean_dec(x_100);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_36 = x_109;
goto block_39;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_64, 1);
lean_inc(x_110);
lean_dec(x_64);
x_111 = lean_ctor_get(x_65, 1);
lean_inc(x_111);
lean_dec_ref(x_65);
x_112 = lean_array_get_size(x_111);
x_113 = lean_nat_dec_lt(x_53, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec_ref(x_1);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_110);
return x_115;
}
else
{
uint8_t x_116; 
x_116 = lean_nat_dec_le(x_112, x_112);
if (x_116 == 0)
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec_ref(x_1);
x_36 = x_110;
goto block_39;
}
else
{
lean_object* x_117; size_t x_118; size_t x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_box(0);
x_118 = 0;
x_119 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_120 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_111, x_118, x_119, x_117, x_1, x_110);
lean_dec(x_111);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec_ref(x_120);
x_36 = x_121;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec_ref(x_40);
x_122 = l_Lake_updateGitPkg___closed__17;
x_123 = l_Lake_updateGitPkg___closed__11;
x_124 = l_Lake_updateGitPkg___closed__12;
lean_inc_ref(x_3);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_3);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lake_updateGitPkg___closed__18;
x_128 = 0;
x_129 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_124);
lean_ctor_set(x_129, 2, x_122);
lean_ctor_set(x_129, 3, x_125);
lean_ctor_set(x_129, 4, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*5, x_43);
lean_ctor_set_uint8(x_129, sizeof(void*)*5 + 1, x_128);
x_130 = l_Lake_testProc(x_129, x_42);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec_ref(x_130);
x_23 = x_126;
x_24 = x_127;
x_25 = x_43;
x_26 = x_133;
goto block_35;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec_ref(x_130);
x_23 = x_126;
x_24 = x_127;
x_25 = x_128;
x_26 = x_134;
goto block_35;
}
}
}
block_139:
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; deleting '", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' and cloning again", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; you might need to delete '", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' manually", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("remote", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get-url", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitRepo___closed__4;
x_2 = l_Lake_cloneGitPkg___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitRepo___closed__5;
x_2 = l_Lake_updateGitRepo___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__19;
x_2 = l_Lake_updateGitRepo___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_updateGitPkg___closed__18;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_updateGitRepo___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_updateGitRepo___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_updateGitRepo___closed__11() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_updateGitRepo___closed__9;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_updateGitRepo___closed__12() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_updateGitRepo___closed__9;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_46 = l_Lake_updateGitRepo___closed__8;
x_47 = l_Lake_updateGitPkg___closed__11;
x_48 = l_Lake_updateGitPkg___closed__12;
lean_inc_ref(x_2);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_2);
x_50 = l_Lake_updateGitPkg___closed__18;
x_51 = 1;
x_52 = 0;
x_53 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*5 + 1, x_52);
x_54 = l_Lake_captureProc_x3f(x_53, x_6);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
if (lean_obj_tag(x_55) == 0)
{
x_57 = x_52;
x_58 = x_56;
goto block_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
lean_dec_ref(x_55);
x_68 = lean_string_dec_eq(x_67, x_3);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_io_realpath(x_67, x_56);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
lean_inc_ref(x_3);
x_72 = lean_io_realpath(x_3, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_string_dec_eq(x_70, x_73);
lean_dec(x_73);
lean_dec(x_70);
x_57 = x_75;
x_58 = x_74;
goto block_66;
}
else
{
lean_object* x_76; 
lean_dec(x_70);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec_ref(x_72);
x_57 = x_52;
x_58 = x_76;
goto block_66;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec_ref(x_69);
x_57 = x_52;
x_58 = x_77;
goto block_66;
}
}
else
{
lean_dec(x_67);
x_57 = x_51;
x_58 = x_56;
goto block_66;
}
}
block_45:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l_System_Platform_isWindows;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lake_updateGitRepo___closed__0;
lean_inc_ref(x_1);
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lake_updateGitRepo___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_5);
x_17 = lean_apply_2(x_5, x_16, x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_IO_FS_removeDirAll(x_2, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lake_cloneGitPkg___at___Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec_ref(x_19);
x_24 = lean_io_error_to_string(x_22);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_apply_2(x_5, x_26, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_3);
x_34 = l_Lake_updateGitRepo___closed__2;
lean_inc_ref(x_1);
x_35 = lean_string_append(x_1, x_34);
x_36 = lean_string_append(x_35, x_2);
x_37 = l_Lake_updateGitRepo___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_inc_ref(x_5);
x_41 = lean_apply_2(x_5, x_40, x_8);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lake_updateGitPkg___at___Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4, x_42);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_3);
x_44 = l_Lake_updateGitPkg___at___Lake_updateGitRepo_spec__1(x_5, x_1, x_2, x_4, x_8);
return x_44;
}
}
block_66:
{
uint8_t x_59; 
x_59 = l_Lake_updateGitRepo___closed__10;
if (x_59 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_45;
}
else
{
uint8_t x_60; 
x_60 = l_Lake_updateGitRepo___closed__11;
if (x_60 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_45;
}
else
{
lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_box(0);
x_62 = 0;
x_63 = l_Lake_updateGitRepo___closed__12;
lean_inc_ref(x_5);
x_64 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_50, x_62, x_63, x_61, x_5, x_58);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_7 = x_57;
x_8 = x_65;
goto block_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___at___Lake_materializeGitRepo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_46 = l_Lake_updateGitRepo___closed__8;
x_47 = l_Lake_updateGitPkg___closed__11;
x_48 = l_Lake_updateGitPkg___closed__12;
lean_inc_ref(x_3);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_3);
x_50 = l_Lake_updateGitPkg___closed__18;
x_51 = 1;
x_52 = 0;
x_53 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*5 + 1, x_52);
x_54 = l_Lake_captureProc_x3f(x_53, x_6);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
if (lean_obj_tag(x_55) == 0)
{
x_57 = x_52;
x_58 = x_56;
goto block_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
lean_dec_ref(x_55);
x_68 = lean_string_dec_eq(x_67, x_4);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_io_realpath(x_67, x_56);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
lean_inc_ref(x_4);
x_72 = lean_io_realpath(x_4, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_string_dec_eq(x_70, x_73);
lean_dec(x_73);
lean_dec(x_70);
x_57 = x_75;
x_58 = x_74;
goto block_66;
}
else
{
lean_object* x_76; 
lean_dec(x_70);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec_ref(x_72);
x_57 = x_52;
x_58 = x_76;
goto block_66;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec_ref(x_69);
x_57 = x_52;
x_58 = x_77;
goto block_66;
}
}
else
{
lean_dec(x_67);
x_57 = x_51;
x_58 = x_56;
goto block_66;
}
}
block_45:
{
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = l_System_Platform_isWindows;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lake_updateGitRepo___closed__0;
lean_inc_ref(x_2);
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_string_append(x_11, x_3);
x_13 = l_Lake_updateGitRepo___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_inc_ref(x_1);
x_17 = lean_apply_2(x_1, x_16, x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_IO_FS_removeDirAll(x_3, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lake_cloneGitPkg___at___Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec_ref(x_19);
x_24 = lean_io_error_to_string(x_22);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_apply_2(x_1, x_26, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_4);
x_34 = l_Lake_updateGitRepo___closed__2;
lean_inc_ref(x_2);
x_35 = lean_string_append(x_2, x_34);
x_36 = lean_string_append(x_35, x_3);
x_37 = l_Lake_updateGitRepo___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_inc_ref(x_1);
x_41 = lean_apply_2(x_1, x_40, x_8);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lake_updateGitPkg___at___Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5, x_42);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_4);
x_44 = l_Lake_updateGitPkg___at___Lake_updateGitRepo_spec__1(x_1, x_2, x_3, x_5, x_8);
return x_44;
}
}
block_66:
{
uint8_t x_59; 
x_59 = l_Lake_updateGitRepo___closed__10;
if (x_59 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_45;
}
else
{
uint8_t x_60; 
x_60 = l_Lake_updateGitRepo___closed__11;
if (x_60 == 0)
{
x_7 = x_57;
x_8 = x_58;
goto block_45;
}
else
{
lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_box(0);
x_62 = 0;
x_63 = l_Lake_updateGitRepo___closed__12;
lean_inc_ref(x_1);
x_64 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_50, x_62, x_63, x_61, x_1, x_58);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_7 = x_57;
x_8 = x_65;
goto block_45;
}
}
}
}
}
static lean_object* _init_l_Lake_materializeGitRepo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_updateGitPkg___closed__4;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_materializeGitRepo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_materializeGitRepo___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_materializeGitRepo___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_materializeGitRepo___closed__0;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_materializeGitRepo___closed__3() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_materializeGitRepo___closed__0;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; 
x_7 = l_System_FilePath_isDir(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_15 = l_Lake_updateGitPkg___closed__4;
x_16 = l_Lake_materializeGitRepo___closed__1;
if (x_16 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = l_Lake_materializeGitRepo___closed__2;
if (x_17 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(0);
x_19 = 0;
x_20 = l_Lake_materializeGitRepo___closed__3;
lean_inc_ref(x_5);
x_21 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_15, x_19, x_20, x_18, x_5, x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_10 = x_22;
goto block_14;
}
}
block_14:
{
uint8_t x_11; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lake_cloneGitPkg___at___Lake_updateGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lake_updateGitRepo___at___Lake_materializeGitRepo_spec__0(x_5, x_1, x_2, x_3, x_4, x_10);
return x_13;
}
}
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_instInhabitedMaterializedDep___closed__1;
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedMaterializedDep___closed__2;
x_2 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedMaterializedDep___closed__3;
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
static lean_object* _init_l_Lake_pkgNotIndexed___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_pkgNotIndexed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package not found on Reservoir.\n\n  If the package is on GitHub, you can add a Git source. For example:\n\n    require ...\n      from git \"https://github.com/", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lake_pkgNotIndexed___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_pkgNotIndexed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n  or, if using TOML:\n\n    [[require]]\n    git = \"https://github.com/", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lake_pkgNotIndexed___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    ...\n", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_pkgNotIndexed___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" @ ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_pkgNotIndexed___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    rev = ", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_27; 
x_27 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_4 = x_27;
x_5 = x_27;
goto block_26;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = l_Lake_pkgNotIndexed___closed__5;
x_31 = l_String_quote(x_29);
lean_dec(x_29);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_31);
x_32 = lean_unsigned_to_nat(120u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_format_pretty(x_3, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
x_36 = l_Lake_pkgNotIndexed___closed__6;
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
x_39 = l_Lake_pkgNotIndexed___closed__5;
x_40 = l_String_quote(x_38);
lean_dec(x_38);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_unsigned_to_nat(120u);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_format_pretty(x_41, x_42, x_43, x_43);
x_45 = lean_string_append(x_39, x_44);
x_46 = l_Lake_pkgNotIndexed___closed__6;
x_47 = lean_string_append(x_46, x_44);
lean_dec_ref(x_44);
x_4 = x_45;
x_5 = x_47;
goto block_26;
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = l_Lake_pkgNotIndexed___closed__0;
lean_inc_ref(x_1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_string_append(x_7, x_2);
x_9 = l_Lake_pkgNotIndexed___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_1);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_string_append(x_12, x_2);
x_14 = l_Lake_pkgNotIndexed___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_4);
lean_dec_ref(x_4);
x_17 = l_Lake_pkgNotIndexed___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec_ref(x_1);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_14);
x_23 = lean_string_append(x_22, x_5);
lean_dec_ref(x_5);
x_24 = l_Lake_pkgNotIndexed___closed__4;
x_25 = lean_string_append(x_23, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_pkgNotIndexed(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Dependency_materialize_mkDep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lakefile", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lake_Dependency_materialize_mkDep___closed__0;
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lake_Dependency_materialize_mkDep(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo___at___Lake_Dependency_materialize_materializeGit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; 
x_7 = l_System_FilePath_isDir(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_15 = l_Lake_updateGitPkg___closed__4;
x_16 = l_Lake_materializeGitRepo___closed__1;
if (x_16 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = l_Lake_materializeGitRepo___closed__2;
if (x_17 == 0)
{
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(0);
x_19 = 0;
x_20 = l_Lake_materializeGitRepo___closed__3;
lean_inc_ref(x_1);
x_21 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_15, x_19, x_20, x_18, x_1, x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_10 = x_22;
goto block_14;
}
}
block_14:
{
uint8_t x_11; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lake_cloneGitPkg___at___Lake_updateGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lake_updateGitRepo___at___Lake_materializeGitRepo_spec__0(x_1, x_2, x_3, x_4, x_5, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_86; 
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_37 = l_Lake_joinRelative(x_4, x_6);
x_86 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_86) == 0)
{
x_38 = x_7;
goto block_85;
}
else
{
lean_object* x_87; 
lean_dec_ref(x_7);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_38 = x_87;
goto block_85;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_10);
x_25 = l_Lake_Dependency_materialize_mkDep___closed__0;
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_10) == 0)
{
x_20 = x_31;
x_21 = x_33;
x_22 = x_32;
x_23 = x_6;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = l_Lake_joinRelative(x_6, x_34);
lean_dec(x_34);
x_20 = x_31;
x_21 = x_33;
x_22 = x_32;
x_23 = x_35;
goto block_30;
}
}
block_85:
{
lean_object* x_39; 
lean_inc(x_9);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_11);
x_39 = l_Lake_materializeGitRepo___at___Lake_Dependency_materialize_materializeGit_spec__0(x_11, x_5, x_37, x_38, x_9, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lake_updateGitPkg___closed__4;
x_43 = l_Lake_GitRepo_getHeadRevision(x_37, x_42, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec_ref(x_44);
x_48 = lean_array_get_size(x_47);
x_49 = lean_nat_dec_lt(x_41, x_48);
if (x_49 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_46;
x_33 = x_45;
goto block_36;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_48, x_48);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_11);
x_31 = x_38;
x_32 = x_46;
x_33 = x_45;
goto block_36;
}
else
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_box(0);
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_54 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_47, x_52, x_53, x_51, x_11, x_45);
lean_dec(x_47);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_31 = x_38;
x_32 = x_46;
x_33 = x_55;
goto block_36;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_56 = !lean_is_exclusive(x_43);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_43, 1);
x_58 = lean_ctor_get(x_43, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_dec_ref(x_44);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_lt(x_41, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_11);
x_62 = lean_box(0);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_62);
return x_43;
}
else
{
uint8_t x_63; 
lean_free_object(x_43);
x_63 = lean_nat_dec_le(x_60, x_60);
if (x_63 == 0)
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_11);
x_13 = x_57;
goto block_16;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_67 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_59, x_65, x_66, x_64, x_11, x_57);
lean_dec(x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_13 = x_68;
goto block_16;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_43, 1);
lean_inc(x_69);
lean_dec(x_43);
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_dec_ref(x_44);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_41, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_11);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_71, x_71);
if (x_75 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_11);
x_13 = x_69;
goto block_16;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_79 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_70, x_77, x_78, x_76, x_11, x_69);
lean_dec(x_70);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_13 = x_80;
goto block_16;
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_81 = !lean_is_exclusive(x_39);
if (x_81 == 0)
{
return x_39;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_39, 0);
x_83 = lean_ctor_get(x_39, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_39);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lake_Dependency_materialize_materializeGit(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_86; 
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_37 = l_Lake_joinRelative(x_5, x_7);
x_86 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_86) == 0)
{
x_38 = x_8;
goto block_85;
}
else
{
lean_object* x_87; 
lean_dec_ref(x_8);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_38 = x_87;
goto block_85;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
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
x_25 = l_Lake_Dependency_materialize_mkDep___closed__0;
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
block_36:
{
if (lean_obj_tag(x_11) == 0)
{
x_20 = x_33;
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
lean_dec(x_34);
x_20 = x_33;
x_21 = x_32;
x_22 = x_31;
x_23 = x_35;
goto block_30;
}
}
block_85:
{
lean_object* x_39; 
lean_inc(x_10);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_39 = l_Lake_materializeGitRepo___at___Lake_Dependency_materialize_materializeGit_spec__0(x_1, x_6, x_37, x_38, x_10, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lake_updateGitPkg___closed__4;
x_43 = l_Lake_GitRepo_getHeadRevision(x_37, x_42, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec_ref(x_44);
x_48 = lean_array_get_size(x_47);
x_49 = lean_nat_dec_lt(x_41, x_48);
if (x_49 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_46;
x_33 = x_45;
goto block_36;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_48, x_48);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_1);
x_31 = x_38;
x_32 = x_46;
x_33 = x_45;
goto block_36;
}
else
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_box(0);
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_54 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_47, x_52, x_53, x_51, x_1, x_45);
lean_dec(x_47);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_31 = x_38;
x_32 = x_46;
x_33 = x_55;
goto block_36;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_56 = !lean_is_exclusive(x_43);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_43, 1);
x_58 = lean_ctor_get(x_43, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_dec_ref(x_44);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_lt(x_41, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_1);
x_62 = lean_box(0);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_62);
return x_43;
}
else
{
uint8_t x_63; 
lean_free_object(x_43);
x_63 = lean_nat_dec_le(x_60, x_60);
if (x_63 == 0)
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_1);
x_13 = x_57;
goto block_16;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_67 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_59, x_65, x_66, x_64, x_1, x_57);
lean_dec(x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_13 = x_68;
goto block_16;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_43, 1);
lean_inc(x_69);
lean_dec(x_43);
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_dec_ref(x_44);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_41, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_71, x_71);
if (x_75 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_13 = x_69;
goto block_16;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_79 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_70, x_77, x_78, x_76, x_1, x_69);
lean_dec(x_70);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_13 = x_80;
goto block_16;
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_39);
if (x_81 == 0)
{
return x_39;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_39, 0);
x_83 = lean_ctor_get(x_39, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_39);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
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
x_1 = lean_mk_string_unchecked(": could not materialize package: this may be a transient error or a bug in Lake or Reservoir", 92, 92);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git#", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Dependency_materialize___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Dependency_materialize___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Dependency_materialize___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": unsupported dependency version format '", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (should be \"git#<rev>\")", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir", 92, 92);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_6);
x_82 = lean_string_utf8_byte_size(x_37);
x_83 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_eq(x_82, x_83);
lean_dec(x_82);
if (x_98 == 0)
{
if (lean_obj_tag(x_38) == 0)
{
x_99 = x_38;
x_100 = x_8;
goto block_113;
}
else
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_38);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_115 = lean_ctor_get(x_38, 0);
x_116 = lean_string_utf8_byte_size(x_115);
lean_inc(x_116);
lean_inc(x_115);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_83);
lean_ctor_set(x_117, 2, x_116);
x_118 = lean_unsigned_to_nat(4u);
x_119 = l_Substring_nextn(x_117, x_118, x_83);
lean_dec_ref(x_117);
lean_inc(x_119);
lean_inc(x_115);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_83);
lean_ctor_set(x_120, 2, x_119);
x_121 = l_Lake_Dependency_materialize___closed__4;
x_122 = l_Substring_beq(x_120, x_121);
if (x_122 == 0)
{
uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_119);
lean_dec(x_116);
lean_free_object(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_123 = 1;
x_124 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_36, x_123);
x_125 = l_Lake_Dependency_materialize___closed__5;
x_126 = lean_string_append(x_124, x_125);
x_127 = lean_string_append(x_126, x_115);
lean_dec(x_115);
x_128 = l_Lake_Dependency_materialize___closed__6;
x_129 = lean_string_append(x_127, x_128);
x_130 = 3;
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_apply_2(x_7, x_131, x_8);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
lean_dec(x_134);
x_135 = lean_box(0);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 0, x_135);
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
lean_dec(x_132);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; 
x_139 = lean_string_utf8_extract(x_115, x_119, x_116);
lean_dec(x_116);
lean_dec(x_119);
lean_dec(x_115);
lean_ctor_set(x_38, 0, x_139);
x_99 = x_38;
x_100 = x_8;
goto block_113;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_140 = lean_ctor_get(x_38, 0);
lean_inc(x_140);
lean_dec(x_38);
x_141 = lean_string_utf8_byte_size(x_140);
lean_inc(x_141);
lean_inc(x_140);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_83);
lean_ctor_set(x_142, 2, x_141);
x_143 = lean_unsigned_to_nat(4u);
x_144 = l_Substring_nextn(x_142, x_143, x_83);
lean_dec_ref(x_142);
lean_inc(x_144);
lean_inc(x_140);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set(x_145, 1, x_83);
lean_ctor_set(x_145, 2, x_144);
x_146 = l_Lake_Dependency_materialize___closed__4;
x_147 = l_Substring_beq(x_145, x_146);
if (x_147 == 0)
{
uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_144);
lean_dec(x_141);
lean_dec_ref(x_37);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_148 = 1;
x_149 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_36, x_148);
x_150 = l_Lake_Dependency_materialize___closed__5;
x_151 = lean_string_append(x_149, x_150);
x_152 = lean_string_append(x_151, x_140);
lean_dec(x_140);
x_153 = l_Lake_Dependency_materialize___closed__6;
x_154 = lean_string_append(x_152, x_153);
x_155 = 3;
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_apply_2(x_7, x_156, x_8);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_159;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_string_utf8_extract(x_140, x_144, x_141);
lean_dec(x_141);
lean_dec(x_144);
lean_dec(x_140);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_99 = x_163;
x_100 = x_8;
goto block_113;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_164 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_36, x_98);
x_165 = l_Lake_Dependency_materialize___closed__7;
x_166 = lean_string_append(x_164, x_165);
x_167 = 3;
x_168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_167);
x_169 = lean_apply_2(x_7, x_168, x_8);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_169, 0);
lean_dec(x_171);
x_172 = lean_box(0);
lean_ctor_set_tag(x_169, 1);
lean_ctor_set(x_169, 0, x_172);
return x_169;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_dec(x_169);
x_174 = lean_box(0);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
block_97:
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_array_get_size(x_88);
x_90 = lean_nat_dec_lt(x_83, x_89);
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec_ref(x_88);
x_40 = x_84;
x_41 = x_86;
x_42 = x_87;
x_43 = x_85;
goto block_81;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_89, x_89);
if (x_91 == 0)
{
lean_dec(x_89);
lean_dec_ref(x_88);
x_40 = x_84;
x_41 = x_86;
x_42 = x_87;
x_43 = x_85;
goto block_81;
}
else
{
lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = 0;
x_94 = lean_usize_of_nat(x_89);
lean_dec(x_89);
lean_inc_ref(x_7);
x_95 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_88, x_93, x_94, x_92, x_7, x_85);
lean_dec_ref(x_88);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_40 = x_84;
x_41 = x_86;
x_42 = x_87;
x_43 = x_96;
goto block_81;
}
}
}
block_113:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_36, x_98);
x_102 = l_Lake_updateGitPkg___closed__4;
lean_inc_ref(x_37);
lean_inc_ref(x_3);
x_103 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_37, x_101, x_102, x_100);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec_ref(x_104);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_106);
x_84 = x_101;
x_85 = x_105;
x_86 = x_99;
x_87 = x_108;
x_88 = x_107;
goto block_97;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
lean_dec_ref(x_103);
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_dec_ref(x_104);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_110);
x_84 = x_101;
x_85 = x_109;
x_86 = x_99;
x_87 = x_112;
x_88 = x_111;
goto block_97;
}
}
}
else
{
lean_object* x_176; 
lean_dec(x_38);
x_176 = lean_ctor_get(x_39, 0);
lean_inc(x_176);
lean_dec_ref(x_39);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = l_Lake_joinRelative(x_6, x_178);
lean_dec_ref(x_178);
x_180 = l_Lake_instInhabitedMaterializedDep___closed__0;
lean_inc_ref(x_179);
lean_ctor_set(x_176, 0, x_179);
x_181 = l_Lake_Dependency_materialize_mkDep___closed__0;
x_182 = lean_box(0);
x_183 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_183, 0, x_36);
lean_ctor_set(x_183, 1, x_37);
lean_ctor_set(x_183, 2, x_181);
lean_ctor_set(x_183, 3, x_182);
lean_ctor_set(x_183, 4, x_176);
lean_ctor_set_uint8(x_183, sizeof(void*)*5, x_2);
x_184 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set(x_184, 2, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_8);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_186 = lean_ctor_get(x_176, 0);
lean_inc(x_186);
lean_dec(x_176);
x_187 = l_Lake_joinRelative(x_6, x_186);
lean_dec_ref(x_186);
x_188 = l_Lake_instInhabitedMaterializedDep___closed__0;
lean_inc_ref(x_187);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_187);
x_190 = l_Lake_Dependency_materialize_mkDep___closed__0;
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_192, 0, x_36);
lean_ctor_set(x_192, 1, x_37);
lean_ctor_set(x_192, 2, x_190);
lean_ctor_set(x_192, 3, x_191);
lean_ctor_set(x_192, 4, x_189);
lean_ctor_set_uint8(x_192, sizeof(void*)*5, x_2);
x_193 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_193, 0, x_187);
lean_ctor_set(x_193, 1, x_188);
lean_ctor_set(x_193, 2, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_8);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_204; 
lean_dec_ref(x_37);
lean_dec_ref(x_6);
x_195 = lean_ctor_get(x_176, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_176, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_176, 2);
lean_inc(x_197);
lean_dec_ref(x_176);
x_198 = 0;
x_199 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_36, x_198);
lean_inc_ref(x_195);
x_204 = l_Lake_Git_filterUrl_x3f(x_195);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_200 = x_205;
goto block_203;
}
else
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec_ref(x_204);
x_200 = x_206;
goto block_203;
}
block_203:
{
lean_object* x_201; lean_object* x_202; 
x_201 = l_Lake_joinRelative(x_5, x_199);
x_202 = l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_199, x_201, x_195, x_200, x_196, x_197, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_202;
}
}
}
block_24:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_9);
x_13 = l_Lake_Dependency_materialize___closed__0;
x_14 = lean_string_append(x_12, x_13);
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_2(x_10, x_16, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
block_35:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_33; 
x_33 = l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_27, x_31, x_29, x_32, x_28, x_26, x_25);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_28);
x_34 = l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0(x_7, x_1, x_2, x_3, x_4, x_27, x_31, x_29, x_32, x_30, x_26, x_25);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_34;
}
}
block_81:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_44 = l_Lake_pkgNotIndexed___closed__0;
x_45 = lean_string_append(x_37, x_44);
x_46 = lean_string_append(x_45, x_40);
lean_dec_ref(x_40);
x_47 = l_Lake_Dependency_materialize___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_apply_2(x_7, x_50, x_43);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_42, 0);
lean_inc(x_58);
lean_dec_ref(x_42);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_59 = l_Lake_pkgNotIndexed(x_37, x_40, x_41);
lean_dec_ref(x_40);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_apply_2(x_7, x_61, x_43);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_40);
lean_dec_ref(x_37);
x_69 = lean_ctor_get(x_58, 0);
lean_inc(x_69);
lean_dec_ref(x_58);
x_70 = l_Lake_RegistryPkg_gitSrc_x3f(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_dec(x_41);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_9 = x_69;
x_10 = x_7;
x_11 = x_43;
goto block_24;
}
else
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 4);
lean_inc(x_75);
lean_dec_ref(x_71);
x_76 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_77);
lean_dec(x_69);
x_78 = l_Lake_joinRelative(x_5, x_76);
lean_dec_ref(x_76);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_79; 
x_79 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_25 = x_43;
x_26 = x_75;
x_27 = x_77;
x_28 = x_74;
x_29 = x_72;
x_30 = x_41;
x_31 = x_78;
x_32 = x_79;
goto block_35;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec_ref(x_73);
x_25 = x_43;
x_26 = x_75;
x_27 = x_77;
x_28 = x_74;
x_29 = x_72;
x_30 = x_41;
x_31 = x_78;
x_32 = x_80;
goto block_35;
}
}
else
{
lean_dec_ref(x_71);
lean_dec(x_41);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_9 = x_69;
x_10 = x_7;
x_11 = x_43;
goto block_24;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lake_Dependency_materialize_materializeGit___at___Lake_Dependency_materialize_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_10 = l_Lake_Dependency_materialize(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize_mkDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--verify", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--end-of-options", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__1;
x_2 = l_Lake_updateGitPkg___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__2;
x_2 = l_Lake_PackageEntry_materialize___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__3;
x_2 = l_Lake_PackageEntry_materialize___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__0;
x_2 = l_Lake_PackageEntry_materialize___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; lean_object* x_47; uint8_t x_56; lean_object* x_57; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_132; uint8_t x_133; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_13, 3);
lean_inc(x_21);
lean_dec_ref(x_13);
x_28 = 0;
lean_inc(x_18);
x_29 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_18, x_28);
x_30 = l_Lake_joinRelative(x_4, x_29);
x_35 = l_Lake_joinRelative(x_3, x_30);
x_103 = l_System_FilePath_isDir(x_35, x_6);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_132 = l_Lake_updateGitPkg___closed__4;
x_133 = l_Lake_materializeGitRepo___closed__1;
if (x_133 == 0)
{
x_106 = x_105;
goto block_131;
}
else
{
uint8_t x_134; 
x_134 = l_Lake_materializeGitRepo___closed__2;
if (x_134 == 0)
{
x_106 = x_105;
goto block_131;
}
else
{
lean_object* x_135; size_t x_136; size_t x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_box(0);
x_136 = 0;
x_137 = l_Lake_materializeGitRepo___closed__3;
lean_inc_ref(x_5);
x_138 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_132, x_136, x_137, x_135, x_5, x_105);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
x_106 = x_139;
goto block_131;
}
}
block_27:
{
lean_object* x_24; 
x_24 = l_Lake_Git_filterUrl_x3f(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_7 = x_22;
x_8 = x_23;
x_9 = x_25;
goto block_12;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
x_7 = x_22;
x_8 = x_23;
x_9 = x_26;
goto block_12;
}
}
block_34:
{
if (lean_obj_tag(x_21) == 0)
{
x_22 = x_31;
x_23 = x_30;
goto block_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec_ref(x_21);
x_33 = l_Lake_joinRelative(x_30, x_32);
lean_dec(x_32);
x_22 = x_31;
x_23 = x_33;
goto block_27;
}
}
block_45:
{
lean_object* x_39; 
x_39 = l_Lake_updateGitRepo___at___Lake_materializeGitRepo_spec__0(x_5, x_29, x_35, x_38, x_36, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_31 = x_40;
goto block_34;
}
else
{
uint8_t x_41; 
lean_dec_ref(x_30);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_55:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_20);
x_49 = l_Lake_cloneGitPkg___at___Lake_updateGitRepo_spec__0(x_5, x_29, x_35, x_47, x_48, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
x_31 = x_50;
goto block_34;
}
else
{
uint8_t x_51; 
lean_dec_ref(x_30);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_49);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_67:
{
if (x_56 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec_ref(x_5);
x_31 = x_57;
goto block_34;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = l_Lake_updateGitPkg___closed__0;
x_59 = lean_string_append(x_29, x_58);
x_60 = lean_string_append(x_59, x_35);
lean_dec_ref(x_35);
x_61 = l_Lake_updateGitPkg___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = 2;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_apply_2(x_5, x_64, x_57);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_31 = x_66;
goto block_34;
}
}
block_80:
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_array_get_size(x_69);
x_73 = lean_nat_dec_lt(x_68, x_72);
if (x_73 == 0)
{
lean_dec(x_72);
lean_dec_ref(x_69);
x_56 = x_70;
x_57 = x_71;
goto block_67;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_72, x_72);
if (x_74 == 0)
{
lean_dec(x_72);
lean_dec_ref(x_69);
x_56 = x_70;
x_57 = x_71;
goto block_67;
}
else
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = 0;
x_77 = lean_usize_of_nat(x_72);
lean_dec(x_72);
lean_inc_ref(x_5);
x_78 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_69, x_76, x_77, x_75, x_5, x_71);
lean_dec_ref(x_69);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_56 = x_70;
x_57 = x_79;
goto block_67;
}
}
}
block_102:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_20);
lean_inc_ref(x_85);
x_86 = l_Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_6_(x_84, x_82, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_2, 5);
x_88 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_87, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_88) == 0)
{
lean_inc_ref(x_19);
x_36 = x_85;
x_37 = x_83;
x_38 = x_19;
goto block_45;
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_36 = x_85;
x_37 = x_83;
x_38 = x_89;
goto block_45;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec_ref(x_85);
lean_dec(x_18);
x_90 = l_Lake_updateGitPkg___closed__17;
x_91 = l_Lake_updateGitPkg___closed__11;
x_92 = l_Lake_updateGitPkg___closed__12;
lean_inc_ref(x_35);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_35);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Lake_updateGitPkg___closed__18;
x_96 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_90);
lean_ctor_set(x_96, 3, x_93);
lean_ctor_set(x_96, 4, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*5, x_81);
lean_ctor_set_uint8(x_96, sizeof(void*)*5 + 1, x_28);
x_97 = l_Lake_testProc(x_96, x_83);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec_ref(x_97);
x_68 = x_94;
x_69 = x_95;
x_70 = x_81;
x_71 = x_100;
goto block_80;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec_ref(x_97);
x_68 = x_94;
x_69 = x_95;
x_70 = x_28;
x_71 = x_101;
goto block_80;
}
}
}
block_131:
{
uint8_t x_107; 
x_107 = lean_unbox(x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_104);
x_108 = lean_ctor_get(x_2, 5);
x_109 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_108, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_109) == 0)
{
lean_inc_ref(x_19);
x_46 = x_106;
x_47 = x_19;
goto block_55;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_46 = x_106;
x_47 = x_110;
goto block_55;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_111 = l_Lake_PackageEntry_materialize___closed__7;
x_112 = l_Lake_updateGitPkg___closed__11;
x_113 = l_Lake_updateGitPkg___closed__12;
lean_inc_ref(x_35);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_35);
x_115 = l_Lake_updateGitPkg___closed__18;
x_116 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 3, x_114);
lean_ctor_set(x_116, 4, x_115);
x_117 = lean_unbox(x_104);
lean_ctor_set_uint8(x_116, sizeof(void*)*5, x_117);
lean_ctor_set_uint8(x_116, sizeof(void*)*5 + 1, x_28);
x_118 = l_Lake_captureProc_x3f(x_116, x_106);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = l_Lake_updateGitRepo___closed__10;
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = lean_unbox(x_104);
lean_dec(x_104);
x_81 = x_122;
x_82 = x_119;
x_83 = x_120;
goto block_102;
}
else
{
uint8_t x_123; 
x_123 = l_Lake_updateGitRepo___closed__11;
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = lean_unbox(x_104);
lean_dec(x_104);
x_81 = x_124;
x_82 = x_119;
x_83 = x_120;
goto block_102;
}
else
{
lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_125 = lean_box(0);
x_126 = 0;
x_127 = l_Lake_updateGitRepo___closed__12;
lean_inc_ref(x_5);
x_128 = l_Array_foldlMUnsafe_fold___at___Lake_updateGitPkg_spec__0(x_115, x_126, x_127, x_125, x_5, x_120);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = lean_unbox(x_104);
lean_dec(x_104);
x_81 = x_130;
x_82 = x_119;
x_83 = x_129;
goto block_102;
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
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_PackageEntry_materialize(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Materialize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_updateGitPkg___closed__0 = _init_l_Lake_updateGitPkg___closed__0();
lean_mark_persistent(l_Lake_updateGitPkg___closed__0);
l_Lake_updateGitPkg___closed__1 = _init_l_Lake_updateGitPkg___closed__1();
lean_mark_persistent(l_Lake_updateGitPkg___closed__1);
l_Lake_updateGitPkg___closed__2 = _init_l_Lake_updateGitPkg___closed__2();
lean_mark_persistent(l_Lake_updateGitPkg___closed__2);
l_Lake_updateGitPkg___closed__3 = _init_l_Lake_updateGitPkg___closed__3();
lean_mark_persistent(l_Lake_updateGitPkg___closed__3);
l_Lake_updateGitPkg___closed__4 = _init_l_Lake_updateGitPkg___closed__4();
lean_mark_persistent(l_Lake_updateGitPkg___closed__4);
l_Lake_updateGitPkg___closed__5 = _init_l_Lake_updateGitPkg___closed__5();
lean_mark_persistent(l_Lake_updateGitPkg___closed__5);
l_Lake_updateGitPkg___closed__6 = _init_l_Lake_updateGitPkg___closed__6();
lean_mark_persistent(l_Lake_updateGitPkg___closed__6);
l_Lake_updateGitPkg___closed__7 = _init_l_Lake_updateGitPkg___closed__7();
lean_mark_persistent(l_Lake_updateGitPkg___closed__7);
l_Lake_updateGitPkg___closed__8 = _init_l_Lake_updateGitPkg___closed__8();
lean_mark_persistent(l_Lake_updateGitPkg___closed__8);
l_Lake_updateGitPkg___closed__9 = _init_l_Lake_updateGitPkg___closed__9();
lean_mark_persistent(l_Lake_updateGitPkg___closed__9);
l_Lake_updateGitPkg___closed__10 = _init_l_Lake_updateGitPkg___closed__10();
lean_mark_persistent(l_Lake_updateGitPkg___closed__10);
l_Lake_updateGitPkg___closed__11 = _init_l_Lake_updateGitPkg___closed__11();
lean_mark_persistent(l_Lake_updateGitPkg___closed__11);
l_Lake_updateGitPkg___closed__12 = _init_l_Lake_updateGitPkg___closed__12();
lean_mark_persistent(l_Lake_updateGitPkg___closed__12);
l_Lake_updateGitPkg___closed__13 = _init_l_Lake_updateGitPkg___closed__13();
lean_mark_persistent(l_Lake_updateGitPkg___closed__13);
l_Lake_updateGitPkg___closed__14 = _init_l_Lake_updateGitPkg___closed__14();
lean_mark_persistent(l_Lake_updateGitPkg___closed__14);
l_Lake_updateGitPkg___closed__15 = _init_l_Lake_updateGitPkg___closed__15();
lean_mark_persistent(l_Lake_updateGitPkg___closed__15);
l_Lake_updateGitPkg___closed__16 = _init_l_Lake_updateGitPkg___closed__16();
lean_mark_persistent(l_Lake_updateGitPkg___closed__16);
l_Lake_updateGitPkg___closed__17 = _init_l_Lake_updateGitPkg___closed__17();
lean_mark_persistent(l_Lake_updateGitPkg___closed__17);
l_Lake_updateGitPkg___closed__18 = _init_l_Lake_updateGitPkg___closed__18();
lean_mark_persistent(l_Lake_updateGitPkg___closed__18);
l_Lake_updateGitPkg___closed__19 = _init_l_Lake_updateGitPkg___closed__19();
lean_mark_persistent(l_Lake_updateGitPkg___closed__19);
l_Lake_cloneGitPkg___closed__0 = _init_l_Lake_cloneGitPkg___closed__0();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__0);
l_Lake_cloneGitPkg___closed__1 = _init_l_Lake_cloneGitPkg___closed__1();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__1);
l_Lake_cloneGitPkg___closed__2 = _init_l_Lake_cloneGitPkg___closed__2();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__2);
l_Lake_cloneGitPkg___closed__3 = _init_l_Lake_cloneGitPkg___closed__3();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__3);
l_Lake_updateGitRepo___closed__0 = _init_l_Lake_updateGitRepo___closed__0();
lean_mark_persistent(l_Lake_updateGitRepo___closed__0);
l_Lake_updateGitRepo___closed__1 = _init_l_Lake_updateGitRepo___closed__1();
lean_mark_persistent(l_Lake_updateGitRepo___closed__1);
l_Lake_updateGitRepo___closed__2 = _init_l_Lake_updateGitRepo___closed__2();
lean_mark_persistent(l_Lake_updateGitRepo___closed__2);
l_Lake_updateGitRepo___closed__3 = _init_l_Lake_updateGitRepo___closed__3();
lean_mark_persistent(l_Lake_updateGitRepo___closed__3);
l_Lake_updateGitRepo___closed__4 = _init_l_Lake_updateGitRepo___closed__4();
lean_mark_persistent(l_Lake_updateGitRepo___closed__4);
l_Lake_updateGitRepo___closed__5 = _init_l_Lake_updateGitRepo___closed__5();
lean_mark_persistent(l_Lake_updateGitRepo___closed__5);
l_Lake_updateGitRepo___closed__6 = _init_l_Lake_updateGitRepo___closed__6();
lean_mark_persistent(l_Lake_updateGitRepo___closed__6);
l_Lake_updateGitRepo___closed__7 = _init_l_Lake_updateGitRepo___closed__7();
lean_mark_persistent(l_Lake_updateGitRepo___closed__7);
l_Lake_updateGitRepo___closed__8 = _init_l_Lake_updateGitRepo___closed__8();
lean_mark_persistent(l_Lake_updateGitRepo___closed__8);
l_Lake_updateGitRepo___closed__9 = _init_l_Lake_updateGitRepo___closed__9();
lean_mark_persistent(l_Lake_updateGitRepo___closed__9);
l_Lake_updateGitRepo___closed__10 = _init_l_Lake_updateGitRepo___closed__10();
l_Lake_updateGitRepo___closed__11 = _init_l_Lake_updateGitRepo___closed__11();
l_Lake_updateGitRepo___closed__12 = _init_l_Lake_updateGitRepo___closed__12();
l_Lake_materializeGitRepo___closed__0 = _init_l_Lake_materializeGitRepo___closed__0();
lean_mark_persistent(l_Lake_materializeGitRepo___closed__0);
l_Lake_materializeGitRepo___closed__1 = _init_l_Lake_materializeGitRepo___closed__1();
l_Lake_materializeGitRepo___closed__2 = _init_l_Lake_materializeGitRepo___closed__2();
l_Lake_materializeGitRepo___closed__3 = _init_l_Lake_materializeGitRepo___closed__3();
l_Lake_instInhabitedMaterializedDep___closed__0 = _init_l_Lake_instInhabitedMaterializedDep___closed__0();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__0);
l_Lake_instInhabitedMaterializedDep___closed__1 = _init_l_Lake_instInhabitedMaterializedDep___closed__1();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__1);
l_Lake_instInhabitedMaterializedDep___closed__2 = _init_l_Lake_instInhabitedMaterializedDep___closed__2();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__2);
l_Lake_instInhabitedMaterializedDep___closed__3 = _init_l_Lake_instInhabitedMaterializedDep___closed__3();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__3);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
l_Lake_pkgNotIndexed___closed__0 = _init_l_Lake_pkgNotIndexed___closed__0();
lean_mark_persistent(l_Lake_pkgNotIndexed___closed__0);
l_Lake_pkgNotIndexed___closed__1 = _init_l_Lake_pkgNotIndexed___closed__1();
lean_mark_persistent(l_Lake_pkgNotIndexed___closed__1);
l_Lake_pkgNotIndexed___closed__2 = _init_l_Lake_pkgNotIndexed___closed__2();
lean_mark_persistent(l_Lake_pkgNotIndexed___closed__2);
l_Lake_pkgNotIndexed___closed__3 = _init_l_Lake_pkgNotIndexed___closed__3();
lean_mark_persistent(l_Lake_pkgNotIndexed___closed__3);
l_Lake_pkgNotIndexed___closed__4 = _init_l_Lake_pkgNotIndexed___closed__4();
lean_mark_persistent(l_Lake_pkgNotIndexed___closed__4);
l_Lake_pkgNotIndexed___closed__5 = _init_l_Lake_pkgNotIndexed___closed__5();
lean_mark_persistent(l_Lake_pkgNotIndexed___closed__5);
l_Lake_pkgNotIndexed___closed__6 = _init_l_Lake_pkgNotIndexed___closed__6();
lean_mark_persistent(l_Lake_pkgNotIndexed___closed__6);
l_Lake_Dependency_materialize_mkDep___closed__0 = _init_l_Lake_Dependency_materialize_mkDep___closed__0();
lean_mark_persistent(l_Lake_Dependency_materialize_mkDep___closed__0);
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
l_Lake_PackageEntry_materialize___closed__0 = _init_l_Lake_PackageEntry_materialize___closed__0();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__0);
l_Lake_PackageEntry_materialize___closed__1 = _init_l_Lake_PackageEntry_materialize___closed__1();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__1);
l_Lake_PackageEntry_materialize___closed__2 = _init_l_Lake_PackageEntry_materialize___closed__2();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__2);
l_Lake_PackageEntry_materialize___closed__3 = _init_l_Lake_PackageEntry_materialize___closed__3();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__3);
l_Lake_PackageEntry_materialize___closed__4 = _init_l_Lake_PackageEntry_materialize___closed__4();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__4);
l_Lake_PackageEntry_materialize___closed__5 = _init_l_Lake_PackageEntry_materialize___closed__5();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__5);
l_Lake_PackageEntry_materialize___closed__6 = _init_l_Lake_PackageEntry_materialize___closed__6();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__6);
l_Lake_PackageEntry_materialize___closed__7 = _init_l_Lake_PackageEntry_materialize___closed__7();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
