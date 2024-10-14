// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: Init Lake.Util.Git Lake.Load.Manifest Lake.Config.Dependency Lake.Config.Package Lake.Reservoir
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
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__7;
static lean_object* l_Lake_updateGitRepo___closed__1;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__4;
static lean_object* l_Lake_PackageEntry_materialize___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__18;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__5;
static lean_object* l_Lake_updateGitPkg___closed__9;
static lean_object* l_Lake_updateGitPkg___closed__13;
static lean_object* l_Lake_updateGitRepo___closed__8;
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitRepo___closed__9;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__8;
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__4;
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__1;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__1;
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
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__8;
static lean_object* l_Lake_updateGitPkg___closed__10;
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__3;
static lean_object* l_Lake_PackageEntry_materialize___closed__2;
static lean_object* l_Lake_updateGitPkg___closed__17;
static lean_object* l_Lake_updateGitPkg___closed__16;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkEntry___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__3;
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__9;
lean_object* l_Lake_testProc(lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__7;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__12;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__1;
static lean_object* l_Lake_PackageEntry_materialize___closed__6;
static lean_object* l_Lake_updateGitRepo___closed__2;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__10;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__3;
static lean_object* l_Lake_updateGitRepo___closed__6;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkEntry(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__6;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__8;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__1;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__2;
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__3;
static lean_object* l_Lake_PackageEntry_materialize___closed__9;
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lambda__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__14;
static lean_object* l_Lake_updateGitRepo___closed__10;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_updateGitPkg___closed__5;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
static lean_object* l_Lake_PackageEntry_materialize___closed__5;
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__2;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__7;
static lean_object* l_Lake_updateGitPkg___closed__11;
static lean_object* _init_l_Lake_updateGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": repository '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has local changes", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": updating repository '", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to revision '", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_updateGitPkg___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--detach", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_updateGitPkg___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diff", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__16;
x_2 = l_Lake_updateGitPkg___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_updateGitPkg___closed__17;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Lake_Git_defaultRemote;
lean_inc(x_2);
x_49 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_48, x_4, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_2);
x_54 = l_Lake_GitRepo_getHeadRevision(x_2, x_53, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
x_60 = lean_string_dec_eq(x_58, x_52);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
lean_free_object(x_55);
x_61 = l_Lake_updateGitPkg___closed__1;
x_62 = lean_string_append(x_61, x_1);
x_63 = l_Lake_updateGitPkg___closed__4;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_2);
x_66 = l_Lake_updateGitPkg___closed__5;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_52);
x_69 = l_Lake_updateGitPkg___closed__6;
x_70 = lean_string_append(x_68, x_69);
x_71 = 1;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_push(x_59, x_72);
x_74 = l_Lake_updateGitPkg___closed__8;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_52);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lake_updateGitPkg___closed__9;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lake_updateGitPkg___closed__10;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_mk(x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_2);
x_82 = l_Lake_updateGitPkg___closed__11;
x_83 = l_Lake_updateGitPkg___closed__13;
x_84 = l_Lake_updateGitPkg___closed__12;
x_85 = 0;
x_86 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_80);
lean_ctor_set(x_86, 3, x_81);
lean_ctor_set(x_86, 4, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*5, x_85);
x_87 = 1;
x_88 = l_Lake_proc(x_86, x_87, x_73, x_56);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_52);
lean_inc(x_2);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_2);
x_90 = l_Lake_updateGitPkg___closed__11;
x_91 = l_Lake_updateGitPkg___closed__13;
x_92 = l_Lake_updateGitPkg___closed__18;
x_93 = l_Lake_updateGitPkg___closed__12;
x_94 = 0;
x_95 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_91);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_89);
lean_ctor_set(x_95, 4, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*5, x_94);
x_96 = l_Lake_testProc(x_95, x_56);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = 1;
x_101 = lean_box(x_100);
lean_ctor_set(x_55, 0, x_101);
x_6 = x_55;
x_7 = x_99;
goto block_47;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_box(x_94);
lean_ctor_set(x_55, 0, x_103);
x_6 = x_55;
x_7 = x_102;
goto block_47;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_55, 0);
x_105 = lean_ctor_get(x_55, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_55);
x_106 = lean_string_dec_eq(x_104, x_52);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_107 = l_Lake_updateGitPkg___closed__1;
x_108 = lean_string_append(x_107, x_1);
x_109 = l_Lake_updateGitPkg___closed__4;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_string_append(x_110, x_2);
x_112 = l_Lake_updateGitPkg___closed__5;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_string_append(x_113, x_52);
x_115 = l_Lake_updateGitPkg___closed__6;
x_116 = lean_string_append(x_114, x_115);
x_117 = 1;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
x_119 = lean_array_push(x_105, x_118);
x_120 = l_Lake_updateGitPkg___closed__8;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_52);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lake_updateGitPkg___closed__9;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lake_updateGitPkg___closed__10;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_array_mk(x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_2);
x_128 = l_Lake_updateGitPkg___closed__11;
x_129 = l_Lake_updateGitPkg___closed__13;
x_130 = l_Lake_updateGitPkg___closed__12;
x_131 = 0;
x_132 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_126);
lean_ctor_set(x_132, 3, x_127);
lean_ctor_set(x_132, 4, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*5, x_131);
x_133 = 1;
x_134 = l_Lake_proc(x_132, x_133, x_119, x_56);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_52);
lean_inc(x_2);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_2);
x_136 = l_Lake_updateGitPkg___closed__11;
x_137 = l_Lake_updateGitPkg___closed__13;
x_138 = l_Lake_updateGitPkg___closed__18;
x_139 = l_Lake_updateGitPkg___closed__12;
x_140 = 0;
x_141 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set(x_141, 1, x_137);
lean_ctor_set(x_141, 2, x_138);
lean_ctor_set(x_141, 3, x_135);
lean_ctor_set(x_141, 4, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*5, x_140);
x_142 = l_Lake_testProc(x_141, x_56);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = 1;
x_147 = lean_box(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_105);
x_6 = x_148;
x_7 = x_145;
goto block_47;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_142, 1);
lean_inc(x_149);
lean_dec(x_142);
x_150 = lean_box(x_140);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_105);
x_6 = x_151;
x_7 = x_149;
goto block_47;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_52);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_54);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_54, 0);
lean_dec(x_153);
x_154 = !lean_is_exclusive(x_55);
if (x_154 == 0)
{
return x_54;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_55, 0);
x_156 = lean_ctor_get(x_55, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_55);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_54, 0, x_157);
return x_54;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_54, 1);
lean_inc(x_158);
lean_dec(x_54);
x_159 = lean_ctor_get(x_55, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_55, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_161 = x_55;
} else {
 lean_dec_ref(x_55);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_158);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_49);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_49, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_50);
if (x_166 == 0)
{
return x_49;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_50, 0);
x_168 = lean_ctor_get(x_50, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_50);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_49, 0, x_169);
return x_49;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = lean_ctor_get(x_49, 1);
lean_inc(x_170);
lean_dec(x_49);
x_171 = lean_ctor_get(x_50, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_50, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_173 = x_50;
} else {
 lean_dec_ref(x_50);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
return x_175;
}
}
block_47:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_6, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = l_Lake_updateGitPkg___closed__1;
x_22 = lean_string_append(x_21, x_1);
x_23 = l_Lake_updateGitPkg___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_2);
lean_dec(x_2);
x_26 = l_Lake_updateGitPkg___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_push(x_19, x_29);
x_31 = lean_box(0);
lean_ctor_set(x_6, 1, x_30);
lean_ctor_set(x_6, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = l_Lake_updateGitPkg___closed__1;
x_35 = lean_string_append(x_34, x_1);
x_36 = l_Lake_updateGitPkg___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_2);
lean_dec(x_2);
x_39 = l_Lake_updateGitPkg___closed__3;
x_40 = lean_string_append(x_38, x_39);
x_41 = 2;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_33, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_updateGitPkg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": cloning ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" to '", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clone", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_7 = l_Lake_updateGitPkg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lake_cloneGitPkg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_3);
x_12 = l_Lake_cloneGitPkg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_2);
x_15 = l_Lake_updateGitPkg___closed__6;
x_16 = lean_string_append(x_14, x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_push(x_5, x_18);
x_20 = lean_box(0);
lean_inc(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_cloneGitPkg___closed__3;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_array_mk(x_24);
x_26 = lean_box(0);
x_27 = l_Lake_updateGitPkg___closed__11;
x_28 = l_Lake_updateGitPkg___closed__13;
x_29 = l_Lake_updateGitPkg___closed__12;
x_30 = 0;
x_31 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_30);
x_32 = 1;
x_33 = l_Lake_proc(x_31, x_32, x_19, x_6);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_34, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_33, 0, x_42);
return x_33;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_45 = x_34;
} else {
 lean_dec_ref(x_34);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_dec(x_33);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = l_Lake_Git_defaultRemote;
lean_inc(x_2);
x_54 = l_Lake_GitRepo_resolveRemoteRevision(x_52, x_53, x_2, x_50, x_49);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_Lake_updateGitPkg___closed__8;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lake_updateGitPkg___closed__9;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lake_updateGitPkg___closed__10;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_mk(x_64);
lean_ctor_set(x_4, 0, x_2);
x_66 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_28);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_4);
lean_ctor_set(x_66, 4, x_29);
lean_ctor_set_uint8(x_66, sizeof(void*)*5, x_30);
x_67 = l_Lake_proc(x_66, x_32, x_58, x_56);
return x_67;
}
else
{
uint8_t x_68; 
lean_free_object(x_4);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_54);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_54, 0);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_55);
if (x_70 == 0)
{
return x_54;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_55, 0);
x_72 = lean_ctor_get(x_55, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_55);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_54, 0, x_73);
return x_54;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
lean_dec(x_54);
x_75 = lean_ctor_get(x_55, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_55, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_77 = x_55;
} else {
 lean_dec_ref(x_55);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
lean_dec(x_4);
x_81 = l_Lake_Git_defaultRemote;
lean_inc(x_2);
x_82 = l_Lake_GitRepo_resolveRemoteRevision(x_80, x_81, x_2, x_50, x_49);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = l_Lake_updateGitPkg___closed__8;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lake_updateGitPkg___closed__9;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lake_updateGitPkg___closed__10;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_mk(x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_2);
x_95 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_95, 0, x_27);
lean_ctor_set(x_95, 1, x_28);
lean_ctor_set(x_95, 2, x_93);
lean_ctor_set(x_95, 3, x_94);
lean_ctor_set(x_95, 4, x_29);
lean_ctor_set_uint8(x_95, sizeof(void*)*5, x_30);
x_96 = l_Lake_proc(x_95, x_32, x_86, x_84);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_2);
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_98 = x_82;
} else {
 lean_dec_ref(x_82);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_101 = x_83;
} else {
 lean_dec_ref(x_83);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_4);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_33);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_33, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_34);
if (x_106 == 0)
{
return x_33;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_34, 0);
x_108 = lean_ctor_get(x_34, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_34);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_33, 0, x_109);
return x_33;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_33, 1);
lean_inc(x_110);
lean_dec(x_33);
x_111 = lean_ctor_get(x_34, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_34, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_113 = x_34;
} else {
 lean_dec_ref(x_34);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_110);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_realpath(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_io_realpath(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_string_dec_eq(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
x_12 = lean_box(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_string_dec_eq(x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_6);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; deleting '", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' and cloning again", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": URL has changed; you might need to delete '", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' manually", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Git_defaultRemote;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get-url", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitRepo___closed__6;
x_2 = l_Lake_updateGitRepo___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("remote", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitRepo___closed__8;
x_2 = l_Lake_updateGitRepo___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_updateGitRepo___closed__9;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_inc(x_2);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_2);
x_94 = l_Lake_updateGitPkg___closed__11;
x_95 = l_Lake_updateGitPkg___closed__13;
x_96 = l_Lake_updateGitRepo___closed__10;
x_97 = l_Lake_updateGitPkg___closed__12;
x_98 = 0;
x_99 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_93);
lean_ctor_set(x_99, 4, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*5, x_98);
x_100 = l_Lake_captureProc_x3f(x_99, x_6);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_100, 1);
x_104 = lean_ctor_get(x_100, 0);
lean_dec(x_104);
x_105 = lean_box(x_98);
lean_ctor_set(x_100, 1, x_5);
lean_ctor_set(x_100, 0, x_105);
x_7 = x_100;
x_8 = x_103;
goto block_92;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_dec(x_100);
x_107 = lean_box(x_98);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_5);
x_7 = x_108;
x_8 = x_106;
goto block_92;
}
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_100, 1);
x_111 = lean_ctor_get(x_100, 0);
lean_dec(x_111);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
lean_dec(x_101);
x_113 = lean_string_dec_eq(x_112, x_3);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_free_object(x_100);
x_114 = lean_box(0);
lean_inc(x_3);
x_115 = l_Lake_updateGitRepo___lambda__1(x_112, x_3, x_114, x_110);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 1);
lean_ctor_set(x_115, 1, x_5);
x_7 = x_115;
x_8 = x_117;
goto block_92;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_115, 0);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_5);
x_7 = x_120;
x_8 = x_119;
goto block_92;
}
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_115);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_115, 1);
x_123 = lean_ctor_get(x_115, 0);
lean_dec(x_123);
x_124 = lean_box(x_98);
lean_ctor_set_tag(x_115, 0);
lean_ctor_set(x_115, 1, x_5);
lean_ctor_set(x_115, 0, x_124);
x_7 = x_115;
x_8 = x_122;
goto block_92;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
lean_dec(x_115);
x_126 = lean_box(x_98);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
x_7 = x_127;
x_8 = x_125;
goto block_92;
}
}
}
else
{
uint8_t x_128; lean_object* x_129; 
lean_dec(x_112);
x_128 = 1;
x_129 = lean_box(x_128);
lean_ctor_set(x_100, 1, x_5);
lean_ctor_set(x_100, 0, x_129);
x_7 = x_100;
x_8 = x_110;
goto block_92;
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_100, 1);
lean_inc(x_130);
lean_dec(x_100);
x_131 = lean_ctor_get(x_101, 0);
lean_inc(x_131);
lean_dec(x_101);
x_132 = lean_string_dec_eq(x_131, x_3);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_box(0);
lean_inc(x_3);
x_134 = l_Lake_updateGitRepo___lambda__1(x_131, x_3, x_133, x_130);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_5);
x_7 = x_138;
x_8 = x_136;
goto block_92;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_140 = x_134;
} else {
 lean_dec_ref(x_134);
 x_140 = lean_box(0);
}
x_141 = lean_box(x_98);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
 lean_ctor_set_tag(x_142, 0);
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_5);
x_7 = x_142;
x_8 = x_139;
goto block_92;
}
}
else
{
uint8_t x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_131);
x_143 = 1;
x_144 = lean_box(x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_5);
x_7 = x_145;
x_8 = x_130;
goto block_92;
}
}
}
block_92:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = l_System_Platform_isWindows;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = l_Lake_updateGitPkg___closed__1;
x_16 = lean_string_append(x_15, x_1);
x_17 = l_Lake_updateGitRepo___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_2);
x_20 = l_Lake_updateGitRepo___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_array_push(x_12, x_23);
x_25 = l_IO_FS_removeDirAll(x_2, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_7);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_24, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_io_error_to_string(x_29);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_get_size(x_24);
x_34 = lean_array_push(x_24, x_32);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_33);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 0, x_7);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_io_error_to_string(x_35);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_24);
x_41 = lean_array_push(x_24, x_39);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_41);
lean_ctor_set(x_7, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_7);
lean_dec(x_3);
x_43 = l_Lake_updateGitPkg___closed__1;
x_44 = lean_string_append(x_43, x_1);
x_45 = l_Lake_updateGitRepo___closed__3;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_2);
x_48 = l_Lake_updateGitRepo___closed__4;
x_49 = lean_string_append(x_47, x_48);
x_50 = 1;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_push(x_12, x_51);
x_53 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_52, x_8);
return x_53;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_dec(x_7);
x_55 = l_System_Platform_isWindows;
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = l_Lake_updateGitPkg___closed__1;
x_57 = lean_string_append(x_56, x_1);
x_58 = l_Lake_updateGitRepo___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_2);
x_61 = l_Lake_updateGitRepo___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_array_push(x_54, x_64);
x_66 = l_IO_FS_removeDirAll(x_2, x_8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_65, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
x_72 = lean_io_error_to_string(x_69);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_65);
x_76 = lean_array_push(x_65, x_74);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
if (lean_is_scalar(x_71)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_71;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_79 = l_Lake_updateGitPkg___closed__1;
x_80 = lean_string_append(x_79, x_1);
x_81 = l_Lake_updateGitRepo___closed__3;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_string_append(x_82, x_2);
x_84 = l_Lake_updateGitRepo___closed__4;
x_85 = lean_string_append(x_83, x_84);
x_86 = 1;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_push(x_54, x_87);
x_89 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_88, x_8);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
lean_dec(x_7);
x_91 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_90, x_8);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateGitRepo___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_updateGitRepo(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_materializeGitRepo(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_updateGitPkg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lake_updateGitPkg___closed__1;
x_4 = 0;
x_5 = l_Lake_instInhabitedMaterializedDep___closed__1;
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__1;
x_2 = l_Lake_instInhabitedMaterializedDep___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkEntry(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_box(0);
x_7 = l_Lake_defaultConfigFile;
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*5, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Dependency_materialize_mkEntry(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_13 = l_System_FilePath_join(x_4, x_6);
x_80 = lean_ctor_get(x_3, 5);
x_81 = lean_ctor_get(x_1, 0);
x_82 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_80, x_81);
if (lean_obj_tag(x_82) == 0)
{
x_14 = x_7;
goto block_79;
}
else
{
lean_object* x_83; 
lean_dec(x_7);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_14 = x_83;
goto block_79;
}
block_79:
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_9);
lean_inc(x_14);
lean_inc(x_13);
x_15 = l_Lake_materializeGitRepo(x_5, x_13, x_14, x_9, x_11, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lake_GitRepo_getHeadRevision(x_13, x_18, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_10);
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_9);
lean_ctor_set(x_25, 3, x_10);
x_26 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_25);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_8);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_20, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_29 = l_System_FilePath_join(x_6, x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_20, 0, x_30);
return x_19;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
lean_inc(x_10);
x_33 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_9);
lean_ctor_set(x_33, 3, x_10);
x_34 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_33);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_8);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_19, 0, x_36);
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_10, 0);
lean_inc(x_37);
lean_dec(x_10);
x_38 = l_System_FilePath_join(x_6, x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
lean_ctor_set(x_39, 2, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_19, 0, x_40);
return x_19;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_44 = x_20;
} else {
 lean_dec_ref(x_20);
 x_44 = lean_box(0);
}
lean_inc(x_10);
x_45 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_9);
lean_ctor_set(x_45, 3, x_10);
x_46 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_45);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_8);
lean_ctor_set(x_47, 2, x_46);
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_44;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_10, 0);
lean_inc(x_50);
lean_dec(x_10);
x_51 = l_System_FilePath_join(x_6, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
lean_ctor_set(x_52, 2, x_46);
if (lean_is_scalar(x_44)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_44;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_19, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_19;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_19, 0, x_60);
return x_19;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
lean_dec(x_19);
x_62 = lean_ctor_get(x_20, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_20, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_64 = x_20;
} else {
 lean_dec_ref(x_20);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_15);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_15, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_16);
if (x_69 == 0)
{
return x_15;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_16, 0);
x_71 = lean_ctor_get(x_16, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_16);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_15, 0, x_72);
return x_15;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_15, 1);
lean_inc(x_73);
lean_dec(x_15);
x_74 = lean_ctor_get(x_16, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_16, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_76 = x_16;
} else {
 lean_dec_ref(x_16);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
return x_78;
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": could not materialize package: dependency has no explicit source and was not found on Reservoir", 97, 97);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": Git source not found on Reservoir", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git#", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Dependency_materialize___lambda__2___closed__5;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Dependency_materialize___lambda__2___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Dependency_materialize___lambda__2___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Dependency_materialize___lambda__2___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" unsupported dependency version format '", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_materialize___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (should be \"git#>rev>\")", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_248; 
x_248 = lean_ctor_get(x_1, 2);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_box(0);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_7);
x_9 = x_250;
x_10 = x_8;
goto block_247;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_262; 
x_251 = lean_ctor_get(x_248, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
x_253 = lean_string_utf8_byte_size(x_251);
x_254 = lean_unsigned_to_nat(0u);
lean_inc(x_253);
lean_inc(x_251);
x_255 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_255, 0, x_251);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_255, 2, x_253);
x_256 = l_Lake_Dependency_materialize___lambda__2___closed__6;
x_257 = l_Substring_nextn(x_255, x_256, x_254);
x_258 = lean_nat_add(x_254, x_257);
lean_dec(x_257);
lean_inc(x_251);
x_259 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_259, 0, x_251);
lean_ctor_set(x_259, 1, x_254);
lean_ctor_set(x_259, 2, x_258);
x_260 = l_Lake_Dependency_materialize___lambda__2___closed__8;
x_261 = l_Substring_beq(x_259, x_260);
if (x_261 == 0)
{
uint8_t x_286; 
x_286 = 0;
x_262 = x_286;
goto block_285;
}
else
{
uint8_t x_287; 
x_287 = 1;
x_262 = x_287;
goto block_285;
}
block_285:
{
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_252);
x_263 = lean_ctor_get(x_1, 0);
lean_inc(x_263);
x_264 = 1;
x_265 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_266 = l_Lean_Name_toString(x_263, x_264, x_265);
x_267 = l_Lake_updateGitPkg___closed__1;
x_268 = lean_string_append(x_267, x_266);
lean_dec(x_266);
x_269 = l_Lake_Dependency_materialize___lambda__2___closed__9;
x_270 = lean_string_append(x_268, x_269);
x_271 = lean_string_append(x_270, x_251);
lean_dec(x_251);
x_272 = l_Lake_Dependency_materialize___lambda__2___closed__10;
x_273 = lean_string_append(x_271, x_272);
x_274 = 3;
x_275 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_274);
x_276 = lean_array_get_size(x_7);
x_277 = lean_array_push(x_7, x_275);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_9 = x_278;
x_10 = x_8;
goto block_247;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_279 = lean_unsigned_to_nat(4u);
x_280 = l_Substring_nextn(x_255, x_279, x_254);
lean_dec(x_255);
x_281 = lean_nat_add(x_254, x_280);
lean_dec(x_280);
x_282 = lean_string_utf8_extract(x_251, x_281, x_253);
lean_dec(x_253);
lean_dec(x_281);
lean_dec(x_251);
if (lean_is_scalar(x_252)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_252;
}
lean_ctor_set(x_283, 0, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_7);
x_9 = x_284;
x_10 = x_8;
goto block_247;
}
}
}
block_247:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = 0;
x_15 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_16 = l_Lean_Name_toString(x_13, x_14, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = l_Lake_Reservoir_fetchPkg_x3f(x_2, x_17, x_16, x_12, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = l_Lake_updateGitPkg___closed__1;
x_27 = lean_string_append(x_26, x_17);
lean_dec(x_17);
x_28 = l_Lake_Dependency_materialize___lambda__2___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_16);
lean_dec(x_16);
x_31 = l_Lake_Dependency_materialize___lambda__2___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_24);
x_36 = lean_array_push(x_24, x_34);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_36);
lean_ctor_set(x_19, 0, x_35);
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_dec(x_19);
x_38 = l_Lake_updateGitPkg___closed__1;
x_39 = lean_string_append(x_38, x_17);
lean_dec(x_17);
x_40 = l_Lake_Dependency_materialize___lambda__2___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_16);
lean_dec(x_16);
x_43 = l_Lake_Dependency_materialize___lambda__2___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_get_size(x_37);
x_48 = lean_array_push(x_37, x_46);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_18, 0, x_49);
return x_18;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_dec(x_18);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_52 = x_19;
} else {
 lean_dec_ref(x_19);
 x_52 = lean_box(0);
}
x_53 = l_Lake_updateGitPkg___closed__1;
x_54 = lean_string_append(x_53, x_17);
lean_dec(x_17);
x_55 = l_Lake_Dependency_materialize___lambda__2___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_16);
lean_dec(x_16);
x_58 = l_Lake_Dependency_materialize___lambda__2___closed__3;
x_59 = lean_string_append(x_57, x_58);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_get_size(x_51);
x_63 = lean_array_push(x_51, x_61);
if (lean_is_scalar(x_52)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_52;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_50);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_17);
lean_dec(x_16);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_18, 1);
x_68 = lean_ctor_get(x_18, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_19);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_19, 1);
x_71 = lean_ctor_get(x_19, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_20, 0);
lean_inc(x_72);
lean_dec(x_20);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = l_System_FilePath_join(x_3, x_73);
lean_dec(x_73);
x_75 = l_Lake_RegistryPkg_gitSrc_x3f(x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_74);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = l_Lake_updateGitPkg___closed__1;
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
x_79 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_80 = lean_string_append(x_78, x_79);
x_81 = 3;
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_83 = lean_array_get_size(x_70);
x_84 = lean_array_push(x_70, x_82);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_84);
lean_ctor_set(x_19, 0, x_83);
return x_18;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_dec(x_75);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_free_object(x_19);
lean_free_object(x_18);
x_86 = lean_ctor_get(x_85, 2);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 4);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
lean_dec(x_72);
x_91 = l_Lake_updateGitPkg___closed__1;
x_92 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_90, x_74, x_87, x_91, x_88, x_89, x_70, x_67);
lean_dec(x_90);
lean_dec(x_1);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 4);
lean_inc(x_94);
lean_dec(x_85);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
lean_dec(x_72);
x_96 = !lean_is_exclusive(x_11);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Lake_updateGitPkg___closed__1;
x_98 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_95, x_74, x_93, x_97, x_11, x_94, x_70, x_67);
lean_dec(x_95);
lean_dec(x_1);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_11, 0);
lean_inc(x_99);
lean_dec(x_11);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lake_updateGitPkg___closed__1;
x_102 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_95, x_74, x_93, x_101, x_100, x_94, x_70, x_67);
lean_dec(x_95);
lean_dec(x_1);
return x_102;
}
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_85, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_85, 4);
lean_inc(x_105);
lean_dec(x_85);
x_106 = lean_ctor_get(x_72, 1);
lean_inc(x_106);
lean_dec(x_72);
x_107 = lean_ctor_get(x_86, 0);
lean_inc(x_107);
lean_dec(x_86);
x_108 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_106, x_74, x_103, x_107, x_104, x_105, x_70, x_67);
lean_dec(x_106);
lean_dec(x_1);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_85, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_85, 4);
lean_inc(x_110);
lean_dec(x_85);
x_111 = lean_ctor_get(x_72, 1);
lean_inc(x_111);
lean_dec(x_72);
x_112 = lean_ctor_get(x_86, 0);
lean_inc(x_112);
lean_dec(x_86);
x_113 = !lean_is_exclusive(x_11);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_111, x_74, x_109, x_112, x_11, x_110, x_70, x_67);
lean_dec(x_111);
lean_dec(x_1);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_11, 0);
lean_inc(x_115);
lean_dec(x_11);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_111, x_74, x_109, x_112, x_116, x_110, x_70, x_67);
lean_dec(x_111);
lean_dec(x_1);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_85);
lean_dec(x_74);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_118 = lean_ctor_get(x_72, 1);
lean_inc(x_118);
lean_dec(x_72);
x_119 = l_Lake_updateGitPkg___closed__1;
x_120 = lean_string_append(x_119, x_118);
lean_dec(x_118);
x_121 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_122 = lean_string_append(x_120, x_121);
x_123 = 3;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_array_get_size(x_70);
x_126 = lean_array_push(x_70, x_124);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_126);
lean_ctor_set(x_19, 0, x_125);
return x_18;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_19, 1);
lean_inc(x_127);
lean_dec(x_19);
x_128 = lean_ctor_get(x_20, 0);
lean_inc(x_128);
lean_dec(x_20);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = l_System_FilePath_join(x_3, x_129);
lean_dec(x_129);
x_131 = l_Lake_RegistryPkg_gitSrc_x3f(x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_130);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = l_Lake_updateGitPkg___closed__1;
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_136 = lean_string_append(x_134, x_135);
x_137 = 3;
x_138 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_137);
x_139 = lean_array_get_size(x_127);
x_140 = lean_array_push(x_127, x_138);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_18, 0, x_141);
return x_18;
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_131, 0);
lean_inc(x_142);
lean_dec(x_131);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_free_object(x_18);
x_143 = lean_ctor_get(x_142, 2);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 4);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
lean_dec(x_128);
x_148 = l_Lake_updateGitPkg___closed__1;
x_149 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_147, x_130, x_144, x_148, x_145, x_146, x_127, x_67);
lean_dec(x_147);
lean_dec(x_1);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_142, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_142, 4);
lean_inc(x_151);
lean_dec(x_142);
x_152 = lean_ctor_get(x_128, 1);
lean_inc(x_152);
lean_dec(x_128);
x_153 = lean_ctor_get(x_11, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_154 = x_11;
} else {
 lean_dec_ref(x_11);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
x_156 = l_Lake_updateGitPkg___closed__1;
x_157 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_152, x_130, x_150, x_156, x_155, x_151, x_127, x_67);
lean_dec(x_152);
lean_dec(x_1);
return x_157;
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_142, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_142, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_142, 4);
lean_inc(x_160);
lean_dec(x_142);
x_161 = lean_ctor_get(x_128, 1);
lean_inc(x_161);
lean_dec(x_128);
x_162 = lean_ctor_get(x_143, 0);
lean_inc(x_162);
lean_dec(x_143);
x_163 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_161, x_130, x_158, x_162, x_159, x_160, x_127, x_67);
lean_dec(x_161);
lean_dec(x_1);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_142, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_142, 4);
lean_inc(x_165);
lean_dec(x_142);
x_166 = lean_ctor_get(x_128, 1);
lean_inc(x_166);
lean_dec(x_128);
x_167 = lean_ctor_get(x_143, 0);
lean_inc(x_167);
lean_dec(x_143);
x_168 = lean_ctor_get(x_11, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_169 = x_11;
} else {
 lean_dec_ref(x_11);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
x_171 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_166, x_130, x_164, x_167, x_170, x_165, x_127, x_67);
lean_dec(x_166);
lean_dec(x_1);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_142);
lean_dec(x_130);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_172 = lean_ctor_get(x_128, 1);
lean_inc(x_172);
lean_dec(x_128);
x_173 = l_Lake_updateGitPkg___closed__1;
x_174 = lean_string_append(x_173, x_172);
lean_dec(x_172);
x_175 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_176 = lean_string_append(x_174, x_175);
x_177 = 3;
x_178 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_177);
x_179 = lean_array_get_size(x_127);
x_180 = lean_array_push(x_127, x_178);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_18, 0, x_181);
return x_18;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_182 = lean_ctor_get(x_18, 1);
lean_inc(x_182);
lean_dec(x_18);
x_183 = lean_ctor_get(x_19, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_184 = x_19;
} else {
 lean_dec_ref(x_19);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_20, 0);
lean_inc(x_185);
lean_dec(x_20);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = l_System_FilePath_join(x_3, x_186);
lean_dec(x_186);
x_188 = l_Lake_RegistryPkg_gitSrc_x3f(x_185);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_187);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_190 = l_Lake_updateGitPkg___closed__1;
x_191 = lean_string_append(x_190, x_189);
lean_dec(x_189);
x_192 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_193 = lean_string_append(x_191, x_192);
x_194 = 3;
x_195 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_194);
x_196 = lean_array_get_size(x_183);
x_197 = lean_array_push(x_183, x_195);
if (lean_is_scalar(x_184)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_184;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_182);
return x_199;
}
else
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_188, 0);
lean_inc(x_200);
lean_dec(x_188);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
lean_dec(x_184);
x_201 = lean_ctor_get(x_200, 2);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 4);
lean_inc(x_204);
lean_dec(x_200);
x_205 = lean_ctor_get(x_185, 1);
lean_inc(x_205);
lean_dec(x_185);
x_206 = l_Lake_updateGitPkg___closed__1;
x_207 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_205, x_187, x_202, x_206, x_203, x_204, x_183, x_182);
lean_dec(x_205);
lean_dec(x_1);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 4);
lean_inc(x_209);
lean_dec(x_200);
x_210 = lean_ctor_get(x_185, 1);
lean_inc(x_210);
lean_dec(x_185);
x_211 = lean_ctor_get(x_11, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_212 = x_11;
} else {
 lean_dec_ref(x_11);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
x_214 = l_Lake_updateGitPkg___closed__1;
x_215 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_210, x_187, x_208, x_214, x_213, x_209, x_183, x_182);
lean_dec(x_210);
lean_dec(x_1);
return x_215;
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_200, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_200, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_200, 4);
lean_inc(x_218);
lean_dec(x_200);
x_219 = lean_ctor_get(x_185, 1);
lean_inc(x_219);
lean_dec(x_185);
x_220 = lean_ctor_get(x_201, 0);
lean_inc(x_220);
lean_dec(x_201);
x_221 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_219, x_187, x_216, x_220, x_217, x_218, x_183, x_182);
lean_dec(x_219);
lean_dec(x_1);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_200, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_200, 4);
lean_inc(x_223);
lean_dec(x_200);
x_224 = lean_ctor_get(x_185, 1);
lean_inc(x_224);
lean_dec(x_185);
x_225 = lean_ctor_get(x_201, 0);
lean_inc(x_225);
lean_dec(x_201);
x_226 = lean_ctor_get(x_11, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_227 = x_11;
} else {
 lean_dec_ref(x_11);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
x_229 = l_Lake_Dependency_materialize_materializeGit(x_1, x_4, x_2, x_5, x_224, x_187, x_222, x_225, x_228, x_223, x_183, x_182);
lean_dec(x_224);
lean_dec(x_1);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_200);
lean_dec(x_187);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_230 = lean_ctor_get(x_185, 1);
lean_inc(x_230);
lean_dec(x_185);
x_231 = l_Lake_updateGitPkg___closed__1;
x_232 = lean_string_append(x_231, x_230);
lean_dec(x_230);
x_233 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_234 = lean_string_append(x_232, x_233);
x_235 = 3;
x_236 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set_uint8(x_236, sizeof(void*)*1, x_235);
x_237 = lean_array_get_size(x_183);
x_238 = lean_array_push(x_183, x_236);
if (lean_is_scalar(x_184)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_184;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_182);
return x_240;
}
}
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_9);
if (x_241 == 0)
{
lean_object* x_242; 
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_9);
lean_ctor_set(x_242, 1, x_10);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_9, 0);
x_244 = lean_ctor_get(x_9, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_9);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_10);
return x_246;
}
}
}
}
}
static lean_object* _init_l_Lake_Dependency_materialize___closed__1() {
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
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_string_utf8_byte_size(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lake_Dependency_materialize___lambda__2(x_1, x_3, x_5, x_2, x_4, x_14, x_7, x_8);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = 1;
x_18 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_19 = l_Lean_Name_toString(x_16, x_17, x_18);
x_20 = l_Lake_updateGitPkg___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lake_Dependency_materialize___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_7);
x_27 = lean_array_push(x_7, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_System_FilePath_join(x_6, x_32);
lean_dec(x_32);
lean_inc(x_33);
lean_ctor_set(x_30, 0, x_33);
x_34 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_30);
lean_dec(x_1);
x_35 = l_Lake_updateGitPkg___closed__1;
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = l_System_FilePath_join(x_6, x_39);
lean_dec(x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_41);
lean_dec(x_1);
x_43 = l_Lake_updateGitPkg___closed__1;
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_8);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_6);
x_47 = lean_ctor_get(x_30, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_30, 2);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = 0;
x_52 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_53 = l_Lean_Name_toString(x_50, x_51, x_52);
lean_inc(x_47);
x_54 = l_Lake_Git_filterUrl_x3f(x_47);
x_55 = l_System_FilePath_join(x_5, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lake_updateGitPkg___closed__1;
x_57 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_53, x_55, x_47, x_56, x_48, x_49, x_7, x_8);
lean_dec(x_53);
lean_dec(x_1);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
lean_dec(x_54);
x_59 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_53, x_55, x_47, x_58, x_48, x_49, x_7, x_8);
lean_dec(x_53);
lean_dec(x_1);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Dependency_materialize___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lake_Dependency_materialize___lambda__2(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Dependency_materialize(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Git_filterUrl_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lake_updateGitPkg___closed__1;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_System_FilePath_join(x_3, x_17);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lake_updateGitPkg___closed__1;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageEntry_materialize___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
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
x_1 = l_Lake_PackageEntry_materialize___closed__3;
x_2 = l_Lake_PackageEntry_materialize___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--verify", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__5;
x_2 = l_Lake_PackageEntry_materialize___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageEntry_materialize___closed__7;
x_2 = l_Lake_PackageEntry_materialize___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageEntry_materialize___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageEntry_materialize___closed__8;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_updateGitPkg___closed__1;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_46; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = 0;
x_18 = l_Lake_Dependency_materialize___lambda__2___closed__1;
lean_inc(x_16);
x_19 = l_Lean_Name_toString(x_16, x_17, x_18);
x_20 = l_System_FilePath_join(x_4, x_19);
x_21 = l_System_FilePath_join(x_3, x_20);
x_22 = l_System_FilePath_isDir(x_21, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_46 = lean_unbox(x_23);
lean_dec(x_23);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_2, 5);
x_48 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_47, x_16);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_inc(x_13);
x_50 = l_Lake_cloneGitPkg(x_19, x_21, x_13, x_49, x_5, x_24);
lean_dec(x_19);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_20, x_1, x_53, x_54, x_52);
lean_dec(x_53);
lean_dec(x_15);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_50, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_50, 0, x_61);
return x_50;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_dec(x_50);
x_63 = lean_ctor_get(x_51, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_65 = x_51;
} else {
 lean_dec_ref(x_51);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_48, 0);
lean_inc(x_68);
lean_dec(x_48);
x_69 = l_Lake_cloneGitPkg(x_19, x_21, x_68, x_49, x_5, x_24);
lean_dec(x_19);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_20, x_1, x_72, x_73, x_71);
lean_dec(x_72);
lean_dec(x_15);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_69);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_69, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_70);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_69, 0, x_80);
return x_69;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_dec(x_69);
x_82 = lean_ctor_get(x_70, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_84 = x_70;
} else {
 lean_dec_ref(x_70);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_inc(x_21);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_21);
x_88 = l_Lake_updateGitPkg___closed__11;
x_89 = l_Lake_updateGitPkg___closed__13;
x_90 = l_Lake_PackageEntry_materialize___closed__9;
x_91 = l_Lake_updateGitPkg___closed__12;
lean_inc(x_87);
x_92 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_87);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*5, x_17);
x_93 = l_Lake_captureProc_x3f(x_92, x_24);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_14);
x_97 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(x_94, x_96);
lean_dec(x_94);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_87);
x_98 = lean_ctor_get(x_2, 5);
x_99 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_98, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_inc(x_13);
x_100 = l_Lake_updateGitRepo(x_19, x_21, x_13, x_96, x_5, x_95);
lean_dec(x_19);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_20, x_1, x_103, x_104, x_102);
lean_dec(x_103);
lean_dec(x_15);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_100);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_100, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_101);
if (x_108 == 0)
{
return x_100;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_101, 0);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_101);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_100, 0, x_111);
return x_100;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_dec(x_100);
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_115 = x_101;
} else {
 lean_dec_ref(x_101);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_99, 0);
lean_inc(x_118);
lean_dec(x_99);
x_119 = l_Lake_updateGitRepo(x_19, x_21, x_118, x_96, x_5, x_95);
lean_dec(x_19);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_20, x_1, x_122, x_123, x_121);
lean_dec(x_122);
lean_dec(x_15);
return x_124;
}
else
{
uint8_t x_125; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_119);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_119, 0);
lean_dec(x_126);
x_127 = !lean_is_exclusive(x_120);
if (x_127 == 0)
{
return x_119;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_120, 0);
x_129 = lean_ctor_get(x_120, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_120);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_119, 0, x_130);
return x_119;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_119, 1);
lean_inc(x_131);
lean_dec(x_119);
x_132 = lean_ctor_get(x_120, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_120, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_134 = x_120;
} else {
 lean_dec_ref(x_120);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_131);
return x_136;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_96);
lean_dec(x_16);
x_137 = l_Lake_updateGitPkg___closed__18;
x_138 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_138, 0, x_88);
lean_ctor_set(x_138, 1, x_89);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_87);
lean_ctor_set(x_138, 4, x_91);
lean_ctor_set_uint8(x_138, sizeof(void*)*5, x_17);
x_139 = l_Lake_testProc(x_138, x_95);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_139);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_139, 1);
x_144 = lean_ctor_get(x_139, 0);
lean_dec(x_144);
x_145 = 1;
x_146 = lean_box(x_145);
lean_ctor_set(x_139, 1, x_5);
lean_ctor_set(x_139, 0, x_146);
x_25 = x_139;
x_26 = x_143;
goto block_45;
}
else
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_139, 1);
lean_inc(x_147);
lean_dec(x_139);
x_148 = 1;
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_5);
x_25 = x_150;
x_26 = x_147;
goto block_45;
}
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_139);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_139, 1);
x_153 = lean_ctor_get(x_139, 0);
lean_dec(x_153);
x_154 = lean_box(x_17);
lean_ctor_set(x_139, 1, x_5);
lean_ctor_set(x_139, 0, x_154);
x_25 = x_139;
x_26 = x_152;
goto block_45;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_139, 1);
lean_inc(x_155);
lean_dec(x_139);
x_156 = lean_box(x_17);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_5);
x_25 = x_157;
x_26 = x_155;
goto block_45;
}
}
}
}
block_45:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_19);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_20, x_1, x_30, x_29, x_26);
lean_dec(x_15);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lake_updateGitPkg___closed__1;
x_34 = lean_string_append(x_33, x_19);
lean_dec(x_19);
x_35 = l_Lake_updateGitPkg___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_21);
lean_dec(x_21);
x_38 = l_Lake_updateGitPkg___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = 2;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_push(x_32, x_41);
x_43 = lean_box(0);
x_44 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_20, x_1, x_43, x_42, x_26);
lean_dec(x_15);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_PackageEntry_materialize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_8;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
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
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lake_cloneGitPkg___closed__1 = _init_l_Lake_cloneGitPkg___closed__1();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__1);
l_Lake_cloneGitPkg___closed__2 = _init_l_Lake_cloneGitPkg___closed__2();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__2);
l_Lake_cloneGitPkg___closed__3 = _init_l_Lake_cloneGitPkg___closed__3();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__3);
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
lean_mark_persistent(l_Lake_updateGitRepo___closed__10);
l_Lake_instInhabitedMaterializedDep___closed__1 = _init_l_Lake_instInhabitedMaterializedDep___closed__1();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__1);
l_Lake_instInhabitedMaterializedDep___closed__2 = _init_l_Lake_instInhabitedMaterializedDep___closed__2();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__2);
l_Lake_instInhabitedMaterializedDep___closed__3 = _init_l_Lake_instInhabitedMaterializedDep___closed__3();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__3);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
l_Lake_Dependency_materialize___lambda__2___closed__1 = _init_l_Lake_Dependency_materialize___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__1);
l_Lake_Dependency_materialize___lambda__2___closed__2 = _init_l_Lake_Dependency_materialize___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__2);
l_Lake_Dependency_materialize___lambda__2___closed__3 = _init_l_Lake_Dependency_materialize___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__3);
l_Lake_Dependency_materialize___lambda__2___closed__4 = _init_l_Lake_Dependency_materialize___lambda__2___closed__4();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__4);
l_Lake_Dependency_materialize___lambda__2___closed__5 = _init_l_Lake_Dependency_materialize___lambda__2___closed__5();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__5);
l_Lake_Dependency_materialize___lambda__2___closed__6 = _init_l_Lake_Dependency_materialize___lambda__2___closed__6();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__6);
l_Lake_Dependency_materialize___lambda__2___closed__7 = _init_l_Lake_Dependency_materialize___lambda__2___closed__7();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__7);
l_Lake_Dependency_materialize___lambda__2___closed__8 = _init_l_Lake_Dependency_materialize___lambda__2___closed__8();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__8);
l_Lake_Dependency_materialize___lambda__2___closed__9 = _init_l_Lake_Dependency_materialize___lambda__2___closed__9();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__9);
l_Lake_Dependency_materialize___lambda__2___closed__10 = _init_l_Lake_Dependency_materialize___lambda__2___closed__10();
lean_mark_persistent(l_Lake_Dependency_materialize___lambda__2___closed__10);
l_Lake_Dependency_materialize___closed__1 = _init_l_Lake_Dependency_materialize___closed__1();
lean_mark_persistent(l_Lake_Dependency_materialize___closed__1);
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
l_Lake_PackageEntry_materialize___closed__9 = _init_l_Lake_PackageEntry_materialize___closed__9();
lean_mark_persistent(l_Lake_PackageEntry_materialize___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
