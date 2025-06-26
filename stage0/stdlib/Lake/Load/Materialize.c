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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__7;
static lean_object* l_Lake_updateGitRepo___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__3;
static lean_object* l_Lake_cloneGitPkg___closed__0;
static lean_object* l_Lake_pkgNotIndexed___closed__4;
static lean_object* l_Lake_PackageEntry_materialize___closed__1;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
uint8_t l_Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_5_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__5;
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__8;
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__4;
static lean_object* l_Lake_updateGitPkg___closed__1;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__6;
static lean_object* l_Lake_Dependency_materialize___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__3;
static lean_object* l_Lake_updateGitPkg___closed__15;
static lean_object* l_Lake_PackageEntry_materialize___closed__3;
static lean_object* l_Lake_updateGitRepo___closed__5;
static lean_object* l_Lake_updateGitRepo___closed__3;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__4;
static lean_object* l_Lake_updateGitRepo___closed__7;
static lean_object* l_Lake_updateGitRepo___closed__4;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__2;
static lean_object* l_Lake_pkgNotIndexed___closed__5;
static lean_object* l_Lake_updateGitPkg___closed__10;
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__3;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__2;
static lean_object* l_Lake_updateGitPkg___closed__17;
static lean_object* l_Lake_updateGitPkg___closed__16;
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__0;
static lean_object* l_Lake_cloneGitPkg___closed__3;
lean_object* l_Lake_testProc(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__2(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__12;
static lean_object* l_Lake_PackageEntry_materialize___closed__0;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__1;
static lean_object* l_Lake_Dependency_materialize___closed__7;
static lean_object* l_Lake_PackageEntry_materialize___closed__6;
static lean_object* l_Lake_Dependency_materialize___closed__0;
static lean_object* l_Lake_updateGitRepo___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static lean_object* l_Lake_PackageEntry_materialize___closed__8;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_Lake_pkgNotIndexed___closed__0;
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__1;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize_mkDep___closed__0;
static lean_object* l_Lake_updateGitRepo___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__2___boxed(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__2;
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__3;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__14;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__0(uint8_t, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__5;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
static lean_object* l_Lake_PackageEntry_materialize___closed__5;
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__2;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__7;
static lean_object* l_Lake_updateGitPkg___closed__11;
static lean_object* _init_l_Lake_updateGitPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("origin", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--detach", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__3;
x_2 = l_Lake_updateGitPkg___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__4;
x_2 = l_Lake_updateGitPkg___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diff", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exit-code", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__12;
x_2 = l_Lake_updateGitPkg___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": repository '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has local changes", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lake_updateGitPkg___closed__0;
lean_inc(x_2);
x_7 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_2);
x_12 = l_Lake_GitRepo_getHeadRevision(x_2, x_11, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_string_dec_eq(x_16, x_10);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
lean_free_object(x_13);
x_19 = l_Lake_updateGitPkg___closed__1;
x_20 = lean_string_append(x_1, x_19);
x_21 = lean_string_append(x_20, x_10);
x_22 = l_Lake_updateGitPkg___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_array_push(x_17, x_25);
x_28 = l_Lake_updateGitPkg___closed__5;
x_29 = l_Lake_updateGitPkg___closed__8;
x_30 = lean_array_push(x_29, x_10);
x_31 = lean_array_push(x_30, x_28);
x_32 = l_Lake_updateGitPkg___closed__9;
x_33 = l_Lake_updateGitPkg___closed__10;
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_2);
x_35 = l_Lake_updateGitPkg___closed__11;
x_36 = lean_box(1);
x_37 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_38);
lean_ctor_set_uint8(x_37, sizeof(void*)*5 + 1, x_18);
x_39 = lean_unbox(x_36);
x_40 = l_Lake_proc(x_37, x_39, x_27, x_14);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_10);
x_41 = l_Lake_updateGitPkg___closed__16;
x_42 = l_Lake_updateGitPkg___closed__9;
x_43 = l_Lake_updateGitPkg___closed__10;
lean_inc(x_2);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_2);
x_45 = l_Lake_updateGitPkg___closed__11;
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*5, x_18);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*5 + 1, x_48);
x_49 = l_Lake_testProc(x_47, x_14);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = l_Lake_updateGitPkg___closed__17;
x_55 = lean_string_append(x_1, x_54);
x_56 = lean_string_append(x_55, x_2);
lean_dec(x_2);
x_57 = l_Lake_updateGitPkg___closed__18;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_box(2);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_unbox(x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_61);
x_62 = lean_box(0);
x_63 = lean_array_push(x_17, x_60);
lean_ctor_set(x_13, 1, x_63);
lean_ctor_set(x_13, 0, x_62);
lean_ctor_set(x_49, 0, x_13);
return x_49;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_dec(x_49);
x_65 = l_Lake_updateGitPkg___closed__17;
x_66 = lean_string_append(x_1, x_65);
x_67 = lean_string_append(x_66, x_2);
lean_dec(x_2);
x_68 = l_Lake_updateGitPkg___closed__18;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_box(2);
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
x_72 = lean_unbox(x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_72);
x_73 = lean_box(0);
x_74 = lean_array_push(x_17, x_71);
lean_ctor_set(x_13, 1, x_74);
lean_ctor_set(x_13, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_13);
lean_ctor_set(x_75, 1, x_64);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_49);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_49, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_13, 0, x_78);
lean_ctor_set(x_49, 0, x_13);
return x_49;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_49, 1);
lean_inc(x_79);
lean_dec(x_49);
x_80 = lean_box(0);
lean_ctor_set(x_13, 0, x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_13);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_13, 0);
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_13);
x_84 = lean_string_dec_eq(x_82, x_10);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; 
x_85 = l_Lake_updateGitPkg___closed__1;
x_86 = lean_string_append(x_1, x_85);
x_87 = lean_string_append(x_86, x_10);
x_88 = l_Lake_updateGitPkg___closed__2;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_box(1);
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_92);
x_93 = lean_array_push(x_83, x_91);
x_94 = l_Lake_updateGitPkg___closed__5;
x_95 = l_Lake_updateGitPkg___closed__8;
x_96 = lean_array_push(x_95, x_10);
x_97 = lean_array_push(x_96, x_94);
x_98 = l_Lake_updateGitPkg___closed__9;
x_99 = l_Lake_updateGitPkg___closed__10;
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_2);
x_101 = l_Lake_updateGitPkg___closed__11;
x_102 = lean_box(1);
x_103 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_97);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_101);
x_104 = lean_unbox(x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*5, x_104);
lean_ctor_set_uint8(x_103, sizeof(void*)*5 + 1, x_84);
x_105 = lean_unbox(x_102);
x_106 = l_Lake_proc(x_103, x_105, x_93, x_14);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_10);
x_107 = l_Lake_updateGitPkg___closed__16;
x_108 = l_Lake_updateGitPkg___closed__9;
x_109 = l_Lake_updateGitPkg___closed__10;
lean_inc(x_2);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_2);
x_111 = l_Lake_updateGitPkg___closed__11;
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_107);
lean_ctor_set(x_113, 3, x_110);
lean_ctor_set(x_113, 4, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*5, x_84);
x_114 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*5 + 1, x_114);
x_115 = l_Lake_testProc(x_113, x_14);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_119 = x_115;
} else {
 lean_dec_ref(x_115);
 x_119 = lean_box(0);
}
x_120 = l_Lake_updateGitPkg___closed__17;
x_121 = lean_string_append(x_1, x_120);
x_122 = lean_string_append(x_121, x_2);
lean_dec(x_2);
x_123 = l_Lake_updateGitPkg___closed__18;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_box(2);
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
x_127 = lean_unbox(x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_127);
x_128 = lean_box(0);
x_129 = lean_array_push(x_83, x_126);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
if (lean_is_scalar(x_119)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_119;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_118);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_115, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_133 = x_115;
} else {
 lean_dec_ref(x_115);
 x_133 = lean_box(0);
}
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_83);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_133;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
return x_136;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_12);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_12, 0);
lean_dec(x_138);
x_139 = !lean_is_exclusive(x_13);
if (x_139 == 0)
{
return x_12;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_13, 0);
x_141 = lean_ctor_get(x_13, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_13);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_12, 0, x_142);
return x_12;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_12, 1);
lean_inc(x_143);
lean_dec(x_12);
x_144 = lean_ctor_get(x_13, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_13, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_146 = x_13;
} else {
 lean_dec_ref(x_13);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_143);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_7);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_7, 0);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_8);
if (x_151 == 0)
{
return x_7;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_8, 0);
x_153 = lean_ctor_get(x_8, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_8);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_7, 0, x_154);
return x_7;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_7, 1);
lean_inc(x_155);
lean_dec(x_7);
x_156 = lean_ctor_get(x_8, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_8, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_158 = x_8;
} else {
 lean_dec_ref(x_8);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_155);
return x_160;
}
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_7 = l_Lake_cloneGitPkg___closed__0;
lean_inc(x_1);
x_8 = lean_string_append(x_1, x_7);
x_9 = lean_string_append(x_8, x_3);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_array_push(x_5, x_11);
x_14 = l_Lake_updateGitPkg___closed__9;
x_15 = l_Lake_updateGitPkg___closed__10;
x_16 = l_Lake_cloneGitPkg___closed__3;
x_17 = lean_array_push(x_16, x_3);
lean_inc(x_2);
x_18 = lean_array_push(x_17, x_2);
x_19 = lean_box(0);
x_20 = l_Lake_updateGitPkg___closed__11;
x_21 = lean_box(1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_24);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_25);
x_26 = lean_unbox(x_21);
x_27 = l_Lake_proc(x_23, x_26, x_13, x_6);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_28, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_39 = x_28;
} else {
 lean_dec_ref(x_28);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = l_Lake_updateGitPkg___closed__0;
lean_inc(x_2);
x_48 = l_Lake_GitRepo_resolveRemoteRevision(x_46, x_47, x_2, x_44, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lake_updateGitPkg___closed__1;
x_54 = lean_string_append(x_1, x_53);
x_55 = lean_string_append(x_54, x_51);
x_56 = l_Lake_updateGitPkg___closed__2;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_unbox(x_10);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_59);
x_60 = lean_array_push(x_52, x_58);
x_61 = l_Lake_updateGitPkg___closed__5;
x_62 = l_Lake_updateGitPkg___closed__8;
x_63 = lean_array_push(x_62, x_51);
x_64 = lean_array_push(x_63, x_61);
lean_ctor_set(x_4, 0, x_2);
x_65 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_65, 0, x_14);
lean_ctor_set(x_65, 1, x_15);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_4);
lean_ctor_set(x_65, 4, x_20);
x_66 = lean_unbox(x_21);
lean_ctor_set_uint8(x_65, sizeof(void*)*5, x_66);
x_67 = lean_unbox(x_22);
lean_ctor_set_uint8(x_65, sizeof(void*)*5 + 1, x_67);
x_68 = lean_unbox(x_21);
x_69 = l_Lake_proc(x_65, x_68, x_60, x_50);
return x_69;
}
else
{
uint8_t x_70; 
lean_free_object(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_48, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_49);
if (x_72 == 0)
{
return x_48;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_49, 0);
x_74 = lean_ctor_get(x_49, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_49);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_48, 0, x_75);
return x_48;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
lean_dec(x_48);
x_77 = lean_ctor_get(x_49, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_49, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_79 = x_49;
} else {
 lean_dec_ref(x_49);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
lean_dec(x_4);
x_83 = l_Lake_updateGitPkg___closed__0;
lean_inc(x_2);
x_84 = l_Lake_GitRepo_resolveRemoteRevision(x_82, x_83, x_2, x_44, x_43);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = l_Lake_updateGitPkg___closed__1;
x_90 = lean_string_append(x_1, x_89);
x_91 = lean_string_append(x_90, x_87);
x_92 = l_Lake_updateGitPkg___closed__2;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_unbox(x_10);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_95);
x_96 = lean_array_push(x_88, x_94);
x_97 = l_Lake_updateGitPkg___closed__5;
x_98 = l_Lake_updateGitPkg___closed__8;
x_99 = lean_array_push(x_98, x_87);
x_100 = lean_array_push(x_99, x_97);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_2);
x_102 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_102, 0, x_14);
lean_ctor_set(x_102, 1, x_15);
lean_ctor_set(x_102, 2, x_100);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set(x_102, 4, x_20);
x_103 = lean_unbox(x_21);
lean_ctor_set_uint8(x_102, sizeof(void*)*5, x_103);
x_104 = lean_unbox(x_22);
lean_ctor_set_uint8(x_102, sizeof(void*)*5 + 1, x_104);
x_105 = lean_unbox(x_21);
x_106 = l_Lake_proc(x_102, x_105, x_96, x_86);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_84, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_108 = x_84;
} else {
 lean_dec_ref(x_84);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_85, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_85, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_111 = x_85;
} else {
 lean_dec_ref(x_85);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
if (lean_is_scalar(x_108)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_108;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_107);
return x_113;
}
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_27;
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
x_1 = l_Lake_updateGitPkg___closed__0;
x_2 = l_Lake_updateGitRepo___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_52 = l_Lake_updateGitRepo___closed__8;
x_53 = l_Lake_updateGitPkg___closed__9;
x_54 = l_Lake_updateGitPkg___closed__10;
lean_inc(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_2);
x_56 = l_Lake_updateGitPkg___closed__11;
x_57 = lean_box(1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_56);
x_60 = lean_unbox(x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_60);
x_61 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 1, x_61);
x_62 = l_Lake_captureProc_x3f(x_59, x_6);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_7 = x_5;
x_8 = x_64;
goto block_51;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_string_dec_eq(x_66, x_3);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_io_realpath(x_66, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_3);
x_71 = lean_io_realpath(x_3, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_string_dec_eq(x_69, x_72);
lean_dec(x_72);
lean_dec(x_69);
if (x_74 == 0)
{
x_7 = x_5;
x_8 = x_73;
goto block_51;
}
else
{
lean_object* x_75; 
lean_dec(x_3);
x_75 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_5, x_73);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_69);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_dec(x_71);
x_7 = x_5;
x_8 = x_76;
goto block_51;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec(x_68);
x_7 = x_5;
x_8 = x_77;
goto block_51;
}
}
else
{
lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_3);
x_78 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_5, x_65);
return x_78;
}
}
block_51:
{
uint8_t x_9; 
x_9 = l_System_Platform_isWindows;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lake_updateGitRepo___closed__0;
lean_inc(x_1);
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lake_updateGitRepo___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_array_push(x_7, x_16);
x_19 = l_IO_FS_removeDirAll(x_2, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_18, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_io_error_to_string(x_23);
x_25 = lean_box(3);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_array_get_size(x_18);
x_29 = lean_array_push(x_18, x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_io_error_to_string(x_31);
x_34 = lean_box(3);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_get_size(x_18);
x_38 = lean_array_push(x_18, x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
x_41 = l_Lake_updateGitRepo___closed__2;
lean_inc(x_1);
x_42 = lean_string_append(x_1, x_41);
x_43 = lean_string_append(x_42, x_2);
x_44 = l_Lake_updateGitRepo___closed__3;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_array_push(x_7, x_47);
x_50 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_49, x_8);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_System_FilePath_isDir(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lake_updateGitRepo(x_1, x_2, x_3, x_4, x_5, x_12);
return x_13;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = l_Lake_instInhabitedMaterializedDep___closed__1;
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_7);
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
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_scope(x_1);
lean_dec(x_1);
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
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_configFile(x_1);
lean_dec(x_1);
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
lean_dec(x_34);
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
lean_dec(x_44);
x_4 = x_45;
x_5 = x_47;
goto block_26;
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = l_Lake_pkgNotIndexed___closed__0;
lean_inc(x_1);
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
lean_dec(x_4);
x_17 = l_Lake_pkgNotIndexed___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec(x_1);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_14);
x_23 = lean_string_append(x_22, x_5);
lean_dec(x_5);
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
lean_dec(x_2);
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
lean_inc(x_7);
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
lean_dec(x_2);
x_7 = l_Lake_Dependency_materialize_mkDep(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_29; lean_object* x_30; lean_object* x_70; 
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_29 = l_Lake_joinRelative(x_4, x_6);
x_70 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_13, x_14);
if (lean_obj_tag(x_70) == 0)
{
x_30 = x_7;
goto block_69;
}
else
{
lean_object* x_71; 
lean_dec(x_7);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_30 = x_71;
goto block_69;
}
block_28:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_10);
x_22 = l_Lake_Dependency_materialize_mkDep___closed__0;
x_23 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
x_24 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_2);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
return x_27;
}
block_69:
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_9);
lean_inc(x_30);
lean_inc(x_29);
x_31 = l_Lake_materializeGitRepo(x_5, x_29, x_30, x_9, x_11, x_12);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lake_GitRepo_getHeadRevision(x_29, x_34, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_16 = x_30;
x_17 = x_37;
x_18 = x_39;
x_19 = x_38;
x_20 = x_6;
goto block_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = l_Lake_joinRelative(x_6, x_43);
lean_dec(x_43);
x_16 = x_30;
x_17 = x_40;
x_18 = x_42;
x_19 = x_41;
x_20 = x_44;
goto block_28;
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_35, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_35;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_35, 0, x_50);
return x_35;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_dec(x_35);
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_54 = x_36;
} else {
 lean_dec_ref(x_36);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_31);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_31, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_32);
if (x_59 == 0)
{
return x_31;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_32, 0);
x_61 = lean_ctor_get(x_32, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_32);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_31, 0, x_62);
return x_31;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_31, 1);
lean_inc(x_63);
lean_dec(x_31);
x_64 = lean_ctor_get(x_32, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_66 = x_32;
} else {
 lean_dec_ref(x_32);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
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
lean_dec(x_2);
x_14 = l_Lake_Dependency_materialize_materializeGit(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_6);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_string_utf8_byte_size(x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_box(x_41);
x_43 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__0___boxed), 2, 1);
lean_closure_set(x_43, 0, x_42);
if (lean_obj_tag(x_38) == 0)
{
x_44 = x_38;
x_45 = x_7;
x_46 = x_8;
goto block_135;
}
else
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_38);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_137 = lean_ctor_get(x_38, 0);
x_138 = lean_string_utf8_byte_size(x_137);
lean_inc(x_138);
lean_inc(x_137);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_40);
lean_ctor_set(x_139, 2, x_138);
x_140 = lean_unsigned_to_nat(4u);
x_141 = l_Substring_nextn(x_139, x_140, x_40);
lean_dec(x_139);
lean_inc(x_141);
lean_inc(x_137);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_40);
lean_ctor_set(x_142, 2, x_141);
x_143 = l_Lake_Dependency_materialize___closed__4;
x_144 = l_Substring_beq(x_142, x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_141);
lean_dec(x_138);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_145 = lean_box(1);
x_146 = lean_unbox(x_145);
x_147 = l_Lean_Name_toString(x_36, x_146, x_43);
x_148 = l_Lake_Dependency_materialize___closed__5;
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_string_append(x_149, x_137);
lean_dec(x_137);
x_151 = l_Lake_Dependency_materialize___closed__6;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_box(3);
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_152);
x_155 = lean_unbox(x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_155);
x_156 = lean_array_get_size(x_7);
x_157 = lean_array_push(x_7, x_154);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_8);
return x_159;
}
else
{
lean_object* x_160; 
x_160 = lean_string_utf8_extract(x_137, x_141, x_138);
lean_dec(x_138);
lean_dec(x_141);
lean_dec(x_137);
lean_ctor_set(x_38, 0, x_160);
x_44 = x_38;
x_45 = x_7;
x_46 = x_8;
goto block_135;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_161 = lean_ctor_get(x_38, 0);
lean_inc(x_161);
lean_dec(x_38);
x_162 = lean_string_utf8_byte_size(x_161);
lean_inc(x_162);
lean_inc(x_161);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_40);
lean_ctor_set(x_163, 2, x_162);
x_164 = lean_unsigned_to_nat(4u);
x_165 = l_Substring_nextn(x_163, x_164, x_40);
lean_dec(x_163);
lean_inc(x_165);
lean_inc(x_161);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_40);
lean_ctor_set(x_166, 2, x_165);
x_167 = l_Lake_Dependency_materialize___closed__4;
x_168 = l_Substring_beq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_165);
lean_dec(x_162);
lean_dec(x_37);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_box(1);
x_170 = lean_unbox(x_169);
x_171 = l_Lean_Name_toString(x_36, x_170, x_43);
x_172 = l_Lake_Dependency_materialize___closed__5;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_string_append(x_173, x_161);
lean_dec(x_161);
x_175 = l_Lake_Dependency_materialize___closed__6;
x_176 = lean_string_append(x_174, x_175);
x_177 = lean_box(3);
x_178 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_178, 0, x_176);
x_179 = lean_unbox(x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_179);
x_180 = lean_array_get_size(x_7);
x_181 = lean_array_push(x_7, x_178);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_8);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_string_utf8_extract(x_161, x_165, x_162);
lean_dec(x_162);
lean_dec(x_165);
lean_dec(x_161);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_44 = x_185;
x_45 = x_7;
x_46 = x_8;
goto block_135;
}
}
}
block_135:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Lean_Name_toString(x_36, x_41, x_43);
lean_inc(x_37);
lean_inc(x_3);
x_48 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_37, x_47, x_45, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_48, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = l_Lake_pkgNotIndexed(x_37, x_47, x_44);
lean_dec(x_47);
x_57 = lean_box(3);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_59);
x_60 = lean_array_get_size(x_54);
x_61 = lean_array_push(x_54, x_58);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 1, x_61);
lean_ctor_set(x_49, 0, x_60);
return x_48;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_dec(x_49);
x_63 = l_Lake_pkgNotIndexed(x_37, x_47, x_44);
lean_dec(x_47);
x_64 = lean_box(3);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_66);
x_67 = lean_array_get_size(x_62);
x_68 = lean_array_push(x_62, x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_48, 0, x_69);
return x_48;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_48, 1);
lean_inc(x_70);
lean_dec(x_48);
x_71 = lean_ctor_get(x_49, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_72 = x_49;
} else {
 lean_dec_ref(x_49);
 x_72 = lean_box(0);
}
x_73 = l_Lake_pkgNotIndexed(x_37, x_47, x_44);
lean_dec(x_47);
x_74 = lean_box(3);
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_unbox(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_76);
x_77 = lean_array_get_size(x_71);
x_78 = lean_array_push(x_71, x_75);
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 1);
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_47);
lean_dec(x_37);
x_81 = lean_ctor_get(x_48, 1);
lean_inc(x_81);
lean_dec(x_48);
x_82 = lean_ctor_get(x_49, 1);
lean_inc(x_82);
lean_dec(x_49);
x_83 = lean_ctor_get(x_50, 0);
lean_inc(x_83);
lean_dec(x_50);
x_84 = l_Lake_RegistryPkg_gitSrc_x3f(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = x_83;
x_22 = x_82;
x_23 = x_81;
goto block_34;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 4);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
x_92 = l_Lake_joinRelative(x_5, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_93; 
x_93 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_9 = x_92;
x_10 = x_89;
x_11 = x_88;
x_12 = x_44;
x_13 = x_86;
x_14 = x_81;
x_15 = x_82;
x_16 = x_91;
x_17 = x_93;
goto block_20;
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
lean_dec(x_87);
x_9 = x_92;
x_10 = x_89;
x_11 = x_88;
x_12 = x_44;
x_13 = x_86;
x_14 = x_81;
x_15 = x_82;
x_16 = x_91;
x_17 = x_94;
goto block_20;
}
}
else
{
lean_dec(x_85);
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = x_83;
x_22 = x_82;
x_23 = x_81;
goto block_34;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_48);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_48, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_49);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_49, 1);
x_99 = l_Lake_pkgNotIndexed___closed__0;
x_100 = lean_string_append(x_37, x_99);
x_101 = lean_string_append(x_100, x_47);
lean_dec(x_47);
x_102 = l_Lake_Dependency_materialize___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_box(3);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
x_106 = lean_unbox(x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_106);
x_107 = lean_array_push(x_98, x_105);
lean_ctor_set(x_49, 1, x_107);
return x_48;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_49, 0);
x_109 = lean_ctor_get(x_49, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_49);
x_110 = l_Lake_pkgNotIndexed___closed__0;
x_111 = lean_string_append(x_37, x_110);
x_112 = lean_string_append(x_111, x_47);
lean_dec(x_47);
x_113 = l_Lake_Dependency_materialize___closed__1;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_box(3);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_unbox(x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_117);
x_118 = lean_array_push(x_109, x_116);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_48, 0, x_119);
return x_48;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get(x_48, 1);
lean_inc(x_120);
lean_dec(x_48);
x_121 = lean_ctor_get(x_49, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_49, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_123 = x_49;
} else {
 lean_dec_ref(x_49);
 x_123 = lean_box(0);
}
x_124 = l_Lake_pkgNotIndexed___closed__0;
x_125 = lean_string_append(x_37, x_124);
x_126 = lean_string_append(x_125, x_47);
lean_dec(x_47);
x_127 = l_Lake_Dependency_materialize___closed__1;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_box(3);
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_128);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_131);
x_132 = lean_array_push(x_122, x_130);
if (lean_is_scalar(x_123)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_123;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
return x_134;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_186 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__2___boxed), 1, 0);
x_187 = l_Lean_Name_toString(x_36, x_41, x_186);
x_188 = l_Lake_Dependency_materialize___closed__7;
x_189 = lean_string_append(x_187, x_188);
x_190 = lean_box(3);
x_191 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_191, 0, x_189);
x_192 = lean_unbox(x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*1, x_192);
x_193 = lean_array_get_size(x_7);
x_194 = lean_array_push(x_7, x_191);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_8);
return x_196;
}
}
else
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_35, 0);
lean_inc(x_197);
lean_dec(x_35);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_198 = lean_ctor_get(x_1, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_1, 1);
lean_inc(x_199);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_197, 0);
x_202 = l_Lake_joinRelative(x_6, x_201);
lean_dec(x_201);
x_203 = l_Lake_instInhabitedMaterializedDep___closed__0;
lean_inc(x_202);
lean_ctor_set(x_197, 0, x_202);
x_204 = l_Lake_Dependency_materialize_mkDep___closed__0;
x_205 = lean_box(0);
x_206 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_206, 0, x_198);
lean_ctor_set(x_206, 1, x_199);
lean_ctor_set(x_206, 2, x_204);
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 4, x_197);
lean_ctor_set_uint8(x_206, sizeof(void*)*5, x_2);
x_207 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_7);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_8);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_210 = lean_ctor_get(x_197, 0);
lean_inc(x_210);
lean_dec(x_197);
x_211 = l_Lake_joinRelative(x_6, x_210);
lean_dec(x_210);
x_212 = l_Lake_instInhabitedMaterializedDep___closed__0;
lean_inc(x_211);
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_211);
x_214 = l_Lake_Dependency_materialize_mkDep___closed__0;
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_216, 0, x_198);
lean_ctor_set(x_216, 1, x_199);
lean_ctor_set(x_216, 2, x_214);
lean_ctor_set(x_216, 3, x_215);
lean_ctor_set(x_216, 4, x_213);
lean_ctor_set_uint8(x_216, sizeof(void*)*5, x_2);
x_217 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_212);
lean_ctor_set(x_217, 2, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_7);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_8);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_232; 
lean_dec(x_6);
x_220 = lean_ctor_get(x_1, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_197, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_197, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_197, 2);
lean_inc(x_223);
lean_dec(x_197);
x_224 = lean_box(0);
x_225 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__0___boxed), 2, 1);
lean_closure_set(x_225, 0, x_224);
x_226 = lean_unbox(x_224);
x_227 = l_Lean_Name_toString(x_220, x_226, x_225);
lean_inc(x_221);
x_232 = l_Lake_Git_filterUrl_x3f(x_221);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_228 = x_233;
goto block_231;
}
else
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
lean_dec(x_232);
x_228 = x_234;
goto block_231;
}
block_231:
{
lean_object* x_229; lean_object* x_230; 
x_229 = l_Lake_joinRelative(x_5, x_227);
x_230 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_227, x_229, x_221, x_228, x_222, x_223, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_230;
}
}
}
block_20:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_18; 
x_18 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_16, x_9, x_13, x_17, x_11, x_10, x_15, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_11);
x_19 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_16, x_9, x_13, x_17, x_12, x_10, x_15, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_19;
}
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lake_Dependency_materialize___closed__0;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(3);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_array_get_size(x_22);
x_31 = lean_array_push(x_22, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Dependency_materialize___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Dependency_materialize___lam__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--verify", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--end-of-options", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__2;
x_2 = l_Lake_updateGitPkg___closed__6;
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
x_1 = l_Lake_PackageEntry_materialize___closed__4;
x_2 = l_Lake_PackageEntry_materialize___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__1;
x_2 = l_Lake_PackageEntry_materialize___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_65; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 3);
lean_inc(x_24);
lean_dec(x_15);
x_32 = lean_box(0);
x_33 = l_Lake_PackageEntry_materialize___closed__0;
x_34 = lean_unbox(x_32);
lean_inc(x_21);
x_35 = l_Lean_Name_toString(x_21, x_34, x_33);
x_36 = l_Lake_joinRelative(x_4, x_35);
x_42 = l_Lake_joinRelative(x_3, x_36);
x_43 = l_System_FilePath_isDir(x_42, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_65 = lean_unbox(x_44);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_44);
x_66 = lean_ctor_get(x_2, 5);
x_67 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_66, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_67) == 0)
{
lean_inc(x_22);
x_46 = x_22;
goto block_64;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_46 = x_68;
goto block_64;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_100; 
x_69 = l_Lake_PackageEntry_materialize___closed__8;
x_70 = l_Lake_updateGitPkg___closed__9;
x_71 = l_Lake_updateGitPkg___closed__10;
lean_inc(x_42);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_42);
x_73 = l_Lake_updateGitPkg___closed__11;
lean_inc(x_72);
x_74 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
x_75 = lean_unbox(x_44);
lean_ctor_set_uint8(x_74, sizeof(void*)*5, x_75);
x_76 = lean_unbox(x_32);
lean_ctor_set_uint8(x_74, sizeof(void*)*5 + 1, x_76);
x_77 = l_Lake_captureProc_x3f(x_74, x_45);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_23);
lean_inc(x_81);
x_100 = l_Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_5_(x_80, x_78, x_81);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_72);
lean_dec(x_44);
x_101 = lean_ctor_get(x_2, 5);
x_102 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_101, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_102) == 0)
{
lean_inc(x_22);
x_82 = x_22;
goto block_99;
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_82 = x_103;
goto block_99;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_81);
lean_dec(x_21);
x_104 = l_Lake_updateGitPkg___closed__16;
x_105 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_105, 0, x_70);
lean_ctor_set(x_105, 1, x_71);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_72);
lean_ctor_set(x_105, 4, x_73);
x_106 = lean_unbox(x_44);
lean_dec(x_44);
lean_ctor_set_uint8(x_105, sizeof(void*)*5, x_106);
x_107 = lean_unbox(x_32);
lean_ctor_set_uint8(x_105, sizeof(void*)*5 + 1, x_107);
x_108 = l_Lake_testProc(x_105, x_79);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = l_Lake_updateGitPkg___closed__17;
x_113 = lean_string_append(x_35, x_112);
x_114 = lean_string_append(x_113, x_42);
lean_dec(x_42);
x_115 = l_Lake_updateGitPkg___closed__18;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_box(2);
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
x_119 = lean_unbox(x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_119);
x_120 = lean_array_push(x_5, x_118);
x_37 = x_120;
x_38 = x_111;
goto block_41;
}
else
{
lean_object* x_121; 
lean_dec(x_42);
lean_dec(x_35);
x_121 = lean_ctor_get(x_108, 1);
lean_inc(x_121);
lean_dec(x_108);
x_37 = x_5;
x_38 = x_121;
goto block_41;
}
}
block_99:
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lake_updateGitRepo(x_35, x_42, x_82, x_81, x_5, x_79);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_37 = x_86;
x_38 = x_85;
goto block_41;
}
else
{
uint8_t x_87; 
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_83, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
return x_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_83, 0, x_92);
return x_83;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
lean_dec(x_83);
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
return x_98;
}
}
}
}
block_31:
{
lean_object* x_28; 
x_28 = l_Lake_Git_filterUrl_x3f(x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = l_Lake_instInhabitedMaterializedDep___closed__0;
x_7 = x_27;
x_8 = x_25;
x_9 = x_26;
x_10 = x_29;
goto block_14;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_7 = x_27;
x_8 = x_25;
x_9 = x_26;
x_10 = x_30;
goto block_14;
}
}
block_41:
{
if (lean_obj_tag(x_24) == 0)
{
x_25 = x_38;
x_26 = x_37;
x_27 = x_36;
goto block_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
lean_dec(x_24);
x_40 = l_Lake_joinRelative(x_36, x_39);
lean_dec(x_39);
x_25 = x_38;
x_26 = x_37;
x_27 = x_40;
goto block_31;
}
}
block_64:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_23);
x_48 = l_Lake_cloneGitPkg(x_35, x_42, x_46, x_47, x_5, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_37 = x_51;
x_38 = x_50;
goto block_41;
}
else
{
uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_48, 0, x_57);
return x_48;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_61 = x_49;
} else {
 lean_dec_ref(x_49);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_PackageEntry_materialize(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
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
l_Lake_PackageEntry_materialize___closed__8 = _init_l_Lake_PackageEntry_materialize___closed__8();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
