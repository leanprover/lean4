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
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__5;
static lean_object* l_Lake_updateGitPkg___closed__9;
static lean_object* l_Lake_updateGitPkg___closed__13;
static lean_object* l_Lake_updateGitRepo___closed__8;
static lean_object* l_Lake_Dependency_materialize___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitRepo___closed__9;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageEntry_materialize___closed__2;
static lean_object* l_Lake_updateGitPkg___closed__17;
static lean_object* l_Lake_updateGitPkg___closed__16;
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
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
x_1 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_updateGitPkg___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--detach", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__10() {
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
static lean_object* _init_l_Lake_updateGitPkg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
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
x_1 = lean_mk_string_unchecked("--exit-code", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_updateGitPkg___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diff", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__15;
x_2 = l_Lake_updateGitPkg___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_updateGitPkg___closed__16;
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
lean_free_object(x_55);
x_61 = l_Lake_updateGitPkg___closed__1;
x_62 = lean_string_append(x_61, x_1);
x_63 = l_Lake_updateGitPkg___closed__4;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_52);
x_66 = l_Lake_updateGitPkg___closed__5;
x_67 = lean_string_append(x_65, x_66);
x_68 = 1;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_array_push(x_59, x_69);
x_71 = l_Lake_updateGitPkg___closed__7;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_52);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lake_updateGitPkg___closed__8;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lake_updateGitPkg___closed__9;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_array_mk(x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_2);
x_79 = l_Lake_updateGitPkg___closed__10;
x_80 = l_Lake_updateGitPkg___closed__12;
x_81 = l_Lake_updateGitPkg___closed__11;
x_82 = 0;
x_83 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_77);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_82);
x_84 = 1;
x_85 = l_Lake_proc(x_83, x_84, x_70, x_56);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_52);
lean_inc(x_2);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_2);
x_87 = l_Lake_updateGitPkg___closed__10;
x_88 = l_Lake_updateGitPkg___closed__12;
x_89 = l_Lake_updateGitPkg___closed__17;
x_90 = l_Lake_updateGitPkg___closed__11;
x_91 = 0;
x_92 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_86);
lean_ctor_set(x_92, 4, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*5, x_91);
x_93 = l_Lake_testProc(x_92, x_56);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = 1;
x_98 = lean_box(x_97);
lean_ctor_set(x_55, 0, x_98);
x_6 = x_55;
x_7 = x_96;
goto block_47;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_box(x_91);
lean_ctor_set(x_55, 0, x_100);
x_6 = x_55;
x_7 = x_99;
goto block_47;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_55, 0);
x_102 = lean_ctor_get(x_55, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_55);
x_103 = lean_string_dec_eq(x_101, x_52);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; 
x_104 = l_Lake_updateGitPkg___closed__1;
x_105 = lean_string_append(x_104, x_1);
x_106 = l_Lake_updateGitPkg___closed__4;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_52);
x_109 = l_Lake_updateGitPkg___closed__5;
x_110 = lean_string_append(x_108, x_109);
x_111 = 1;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_push(x_102, x_112);
x_114 = l_Lake_updateGitPkg___closed__7;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_52);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lake_updateGitPkg___closed__8;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lake_updateGitPkg___closed__9;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = lean_array_mk(x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_2);
x_122 = l_Lake_updateGitPkg___closed__10;
x_123 = l_Lake_updateGitPkg___closed__12;
x_124 = l_Lake_updateGitPkg___closed__11;
x_125 = 0;
x_126 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_120);
lean_ctor_set(x_126, 3, x_121);
lean_ctor_set(x_126, 4, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*5, x_125);
x_127 = 1;
x_128 = l_Lake_proc(x_126, x_127, x_113, x_56);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_52);
lean_inc(x_2);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_2);
x_130 = l_Lake_updateGitPkg___closed__10;
x_131 = l_Lake_updateGitPkg___closed__12;
x_132 = l_Lake_updateGitPkg___closed__17;
x_133 = l_Lake_updateGitPkg___closed__11;
x_134 = 0;
x_135 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_129);
lean_ctor_set(x_135, 4, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*5, x_134);
x_136 = l_Lake_testProc(x_135, x_56);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = 1;
x_141 = lean_box(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_102);
x_6 = x_142;
x_7 = x_139;
goto block_47;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_dec(x_136);
x_144 = lean_box(x_134);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_102);
x_6 = x_145;
x_7 = x_143;
goto block_47;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_52);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_54);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_54, 0);
lean_dec(x_147);
x_148 = !lean_is_exclusive(x_55);
if (x_148 == 0)
{
return x_54;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_55, 0);
x_150 = lean_ctor_get(x_55, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_55);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_54, 0, x_151);
return x_54;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_54, 1);
lean_inc(x_152);
lean_dec(x_54);
x_153 = lean_ctor_get(x_55, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_55, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_155 = x_55;
} else {
 lean_dec_ref(x_55);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_49);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_49, 0);
lean_dec(x_159);
x_160 = !lean_is_exclusive(x_50);
if (x_160 == 0)
{
return x_49;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_50, 0);
x_162 = lean_ctor_get(x_50, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_50);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_49, 0, x_163);
return x_49;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_ctor_get(x_49, 1);
lean_inc(x_164);
lean_dec(x_49);
x_165 = lean_ctor_get(x_50, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_50, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_167 = x_50;
} else {
 lean_dec_ref(x_50);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
return x_169;
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
x_1 = lean_mk_string_unchecked("clone", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_7 = l_Lake_updateGitPkg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lake_cloneGitPkg___closed__1;
lean_inc(x_8);
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_3);
x_12 = lean_string_append(x_11, x_7);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_array_push(x_5, x_14);
x_16 = lean_box(0);
lean_inc(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_cloneGitPkg___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_mk(x_20);
x_22 = lean_box(0);
x_23 = l_Lake_updateGitPkg___closed__10;
x_24 = l_Lake_updateGitPkg___closed__12;
x_25 = l_Lake_updateGitPkg___closed__11;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_26);
x_28 = 1;
x_29 = l_Lake_proc(x_27, x_28, x_15, x_6);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_30, 0, x_35);
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_29, 0, x_38);
return x_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec(x_29);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec(x_30);
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = l_Lake_Git_defaultRemote;
lean_inc(x_2);
x_50 = l_Lake_GitRepo_resolveRemoteRevision(x_48, x_49, x_2, x_46, x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lake_updateGitPkg___closed__4;
x_56 = lean_string_append(x_8, x_55);
x_57 = lean_string_append(x_56, x_53);
x_58 = l_Lake_updateGitPkg___closed__5;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_13);
x_61 = lean_array_push(x_54, x_60);
x_62 = l_Lake_updateGitPkg___closed__7;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lake_updateGitPkg___closed__8;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lake_updateGitPkg___closed__9;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_array_mk(x_67);
lean_ctor_set(x_4, 0, x_2);
x_69 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_69, 0, x_23);
lean_ctor_set(x_69, 1, x_24);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_4);
lean_ctor_set(x_69, 4, x_25);
lean_ctor_set_uint8(x_69, sizeof(void*)*5, x_26);
x_70 = l_Lake_proc(x_69, x_28, x_61, x_52);
return x_70;
}
else
{
uint8_t x_71; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_50);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_50, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_51);
if (x_73 == 0)
{
return x_50;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_51, 0);
x_75 = lean_ctor_get(x_51, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_51);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_50, 0, x_76);
return x_50;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_50, 1);
lean_inc(x_77);
lean_dec(x_50);
x_78 = lean_ctor_get(x_51, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_51, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_80 = x_51;
} else {
 lean_dec_ref(x_51);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_4, 0);
lean_inc(x_83);
lean_dec(x_4);
x_84 = l_Lake_Git_defaultRemote;
lean_inc(x_2);
x_85 = l_Lake_GitRepo_resolveRemoteRevision(x_83, x_84, x_2, x_46, x_45);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lake_updateGitPkg___closed__4;
x_91 = lean_string_append(x_8, x_90);
x_92 = lean_string_append(x_91, x_88);
x_93 = l_Lake_updateGitPkg___closed__5;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_13);
x_96 = lean_array_push(x_89, x_95);
x_97 = l_Lake_updateGitPkg___closed__7;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lake_updateGitPkg___closed__8;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lake_updateGitPkg___closed__9;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_mk(x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_2);
x_105 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_105, 0, x_23);
lean_ctor_set(x_105, 1, x_24);
lean_ctor_set(x_105, 2, x_103);
lean_ctor_set(x_105, 3, x_104);
lean_ctor_set(x_105, 4, x_25);
lean_ctor_set_uint8(x_105, sizeof(void*)*5, x_26);
x_106 = l_Lake_proc(x_105, x_28, x_96, x_87);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_8);
lean_dec(x_2);
x_107 = lean_ctor_get(x_85, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_108 = x_85;
} else {
 lean_dec_ref(x_85);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_86, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_86, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_111 = x_86;
} else {
 lean_dec_ref(x_86);
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
uint8_t x_114; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_29);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_29, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_30);
if (x_116 == 0)
{
return x_29;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_30, 0);
x_118 = lean_ctor_get(x_30, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_30);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_29, 0, x_119);
return x_29;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_29, 1);
lean_inc(x_120);
lean_dec(x_29);
x_121 = lean_ctor_get(x_30, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_30, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_123 = x_30;
} else {
 lean_dec_ref(x_30);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_120);
return x_125;
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
x_94 = l_Lake_updateGitPkg___closed__10;
x_95 = l_Lake_updateGitPkg___closed__12;
x_96 = l_Lake_updateGitRepo___closed__10;
x_97 = l_Lake_updateGitPkg___closed__11;
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_box(0);
x_9 = l_Lake_defaultConfigFile;
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_8);
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
lean_object* x_13; lean_object* x_14; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_13 = l_System_FilePath_join(x_4, x_6);
x_92 = lean_ctor_get(x_3, 5);
x_93 = lean_ctor_get(x_1, 0);
x_94 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_92, x_93);
if (lean_obj_tag(x_94) == 0)
{
x_14 = x_7;
goto block_91;
}
else
{
lean_object* x_95; 
lean_dec(x_7);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec(x_94);
x_14 = x_95;
goto block_91;
}
block_91:
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_10);
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_9);
lean_ctor_set(x_25, 3, x_10);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_box(0);
x_29 = l_Lake_defaultConfigFile;
lean_inc(x_27);
lean_inc(x_26);
x_30 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_20, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
x_33 = l_System_FilePath_join(x_6, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_20, 0, x_34);
return x_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
lean_inc(x_10);
x_37 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_9);
lean_ctor_set(x_37, 3, x_10);
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_box(0);
x_41 = l_Lake_defaultConfigFile;
lean_inc(x_39);
lean_inc(x_38);
x_42 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*5, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_8);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
lean_dec(x_10);
x_46 = l_System_FilePath_join(x_6, x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
lean_ctor_set(x_47, 2, x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_36);
lean_ctor_set(x_19, 0, x_48);
return x_19;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_dec(x_19);
x_50 = lean_ctor_get(x_20, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_52 = x_20;
} else {
 lean_dec_ref(x_20);
 x_52 = lean_box(0);
}
lean_inc(x_10);
x_53 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_9);
lean_ctor_set(x_53, 3, x_10);
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
x_56 = lean_box(0);
x_57 = l_Lake_defaultConfigFile;
lean_inc(x_55);
lean_inc(x_54);
x_58 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_56);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_8);
lean_ctor_set(x_59, 2, x_58);
if (lean_is_scalar(x_52)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_52;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_10, 0);
lean_inc(x_62);
lean_dec(x_10);
x_63 = l_System_FilePath_join(x_6, x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_8);
lean_ctor_set(x_64, 2, x_58);
if (lean_is_scalar(x_52)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_52;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_49);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_19);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_19, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_20);
if (x_69 == 0)
{
return x_19;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_20, 0);
x_71 = lean_ctor_get(x_20, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_20);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_19, 0, x_72);
return x_19;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_dec(x_19);
x_74 = lean_ctor_get(x_20, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_76 = x_20;
} else {
 lean_dec_ref(x_20);
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
else
{
uint8_t x_79; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_15, 0);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_16);
if (x_81 == 0)
{
return x_15;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_16, 0);
x_83 = lean_ctor_get(x_16, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_16);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_15, 0, x_84);
return x_15;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_dec(x_15);
x_86 = lean_ctor_get(x_16, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_16, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_88 = x_16;
} else {
 lean_dec_ref(x_16);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
return x_90;
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
x_1 = lean_mk_string_unchecked(": unsupported dependency version format '", 41, 41);
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_7);
x_250 = lean_box(0);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_9);
x_11 = x_251;
x_12 = x_10;
goto block_249;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_263; 
x_252 = lean_ctor_get(x_1, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_253 = x_1;
} else {
 lean_dec_ref(x_1);
 x_253 = lean_box(0);
}
x_254 = lean_string_utf8_byte_size(x_252);
x_255 = lean_unsigned_to_nat(0u);
lean_inc(x_254);
lean_inc(x_252);
x_256 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_256, 0, x_252);
lean_ctor_set(x_256, 1, x_255);
lean_ctor_set(x_256, 2, x_254);
x_257 = l_Lake_Dependency_materialize___lambda__2___closed__6;
x_258 = l_Substring_nextn(x_256, x_257, x_255);
x_259 = lean_nat_add(x_255, x_258);
lean_dec(x_258);
lean_inc(x_252);
x_260 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_255);
lean_ctor_set(x_260, 2, x_259);
x_261 = l_Lake_Dependency_materialize___lambda__2___closed__8;
x_262 = l_Substring_beq(x_260, x_261);
if (x_262 == 0)
{
uint8_t x_286; 
x_286 = 0;
x_263 = x_286;
goto block_285;
}
else
{
uint8_t x_287; 
x_287 = 1;
x_263 = x_287;
goto block_285;
}
block_285:
{
if (x_263 == 0)
{
uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_253);
x_264 = 1;
x_265 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_266 = l_Lean_Name_toString(x_7, x_264, x_265);
x_267 = l_Lake_updateGitPkg___closed__1;
x_268 = lean_string_append(x_267, x_266);
lean_dec(x_266);
x_269 = l_Lake_Dependency_materialize___lambda__2___closed__9;
x_270 = lean_string_append(x_268, x_269);
x_271 = lean_string_append(x_270, x_252);
lean_dec(x_252);
x_272 = l_Lake_Dependency_materialize___lambda__2___closed__10;
x_273 = lean_string_append(x_271, x_272);
x_274 = 3;
x_275 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_274);
x_276 = lean_array_get_size(x_9);
x_277 = lean_array_push(x_9, x_275);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_11 = x_278;
x_12 = x_10;
goto block_249;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_7);
x_279 = lean_unsigned_to_nat(4u);
x_280 = l_Substring_nextn(x_256, x_279, x_255);
lean_dec(x_256);
x_281 = lean_nat_add(x_255, x_280);
lean_dec(x_280);
x_282 = lean_string_utf8_extract(x_252, x_281, x_254);
lean_dec(x_254);
lean_dec(x_281);
lean_dec(x_252);
if (lean_is_scalar(x_253)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_253;
}
lean_ctor_set(x_283, 0, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_9);
x_11 = x_284;
x_12 = x_10;
goto block_249;
}
}
}
block_249:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = 0;
x_17 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_18 = l_Lean_Name_toString(x_15, x_16, x_17);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_19, x_18, x_14, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = l_Lake_updateGitPkg___closed__1;
x_29 = lean_string_append(x_28, x_19);
lean_dec(x_19);
x_30 = l_Lake_Dependency_materialize___lambda__2___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_18);
lean_dec(x_18);
x_33 = l_Lake_Dependency_materialize___lambda__2___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_26);
x_38 = lean_array_push(x_26, x_36);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_38);
lean_ctor_set(x_21, 0, x_37);
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = l_Lake_updateGitPkg___closed__1;
x_41 = lean_string_append(x_40, x_19);
lean_dec(x_19);
x_42 = l_Lake_Dependency_materialize___lambda__2___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_18);
lean_dec(x_18);
x_45 = l_Lake_Dependency_materialize___lambda__2___closed__3;
x_46 = lean_string_append(x_44, x_45);
x_47 = 3;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_array_get_size(x_39);
x_50 = lean_array_push(x_39, x_48);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_20, 0, x_51);
return x_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_dec(x_20);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_54 = x_21;
} else {
 lean_dec_ref(x_21);
 x_54 = lean_box(0);
}
x_55 = l_Lake_updateGitPkg___closed__1;
x_56 = lean_string_append(x_55, x_19);
lean_dec(x_19);
x_57 = l_Lake_Dependency_materialize___lambda__2___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_18);
lean_dec(x_18);
x_60 = l_Lake_Dependency_materialize___lambda__2___closed__3;
x_61 = lean_string_append(x_59, x_60);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_53);
x_65 = lean_array_push(x_53, x_63);
if (lean_is_scalar(x_54)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_54;
 lean_ctor_set_tag(x_66, 1);
}
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_52);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_19);
lean_dec(x_18);
x_68 = !lean_is_exclusive(x_20);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_20, 1);
x_70 = lean_ctor_get(x_20, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_21);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_21, 1);
x_73 = lean_ctor_get(x_21, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_22, 0);
lean_inc(x_74);
lean_dec(x_22);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = l_System_FilePath_join(x_4, x_75);
lean_dec(x_75);
x_77 = l_Lake_RegistryPkg_gitSrc_x3f(x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = l_Lake_updateGitPkg___closed__1;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_82 = lean_string_append(x_80, x_81);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_array_get_size(x_72);
x_86 = lean_array_push(x_72, x_84);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_86);
lean_ctor_set(x_21, 0, x_85);
return x_20;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_77, 0);
lean_inc(x_87);
lean_dec(x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_free_object(x_21);
lean_free_object(x_20);
x_88 = lean_ctor_get(x_87, 2);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 4);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
lean_dec(x_74);
x_93 = l_Lake_updateGitPkg___closed__1;
x_94 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_92, x_76, x_89, x_93, x_90, x_91, x_72, x_69);
lean_dec(x_92);
lean_dec(x_2);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 4);
lean_inc(x_96);
lean_dec(x_87);
x_97 = lean_ctor_get(x_74, 1);
lean_inc(x_97);
lean_dec(x_74);
x_98 = !lean_is_exclusive(x_13);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lake_updateGitPkg___closed__1;
x_100 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_97, x_76, x_95, x_99, x_13, x_96, x_72, x_69);
lean_dec(x_97);
lean_dec(x_2);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_13, 0);
lean_inc(x_101);
lean_dec(x_13);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lake_updateGitPkg___closed__1;
x_104 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_97, x_76, x_95, x_103, x_102, x_96, x_72, x_69);
lean_dec(x_97);
lean_dec(x_2);
return x_104;
}
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_87, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_87, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_87, 4);
lean_inc(x_107);
lean_dec(x_87);
x_108 = lean_ctor_get(x_74, 1);
lean_inc(x_108);
lean_dec(x_74);
x_109 = lean_ctor_get(x_88, 0);
lean_inc(x_109);
lean_dec(x_88);
x_110 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_108, x_76, x_105, x_109, x_106, x_107, x_72, x_69);
lean_dec(x_108);
lean_dec(x_2);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_87, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_87, 4);
lean_inc(x_112);
lean_dec(x_87);
x_113 = lean_ctor_get(x_74, 1);
lean_inc(x_113);
lean_dec(x_74);
x_114 = lean_ctor_get(x_88, 0);
lean_inc(x_114);
lean_dec(x_88);
x_115 = !lean_is_exclusive(x_13);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_113, x_76, x_111, x_114, x_13, x_112, x_72, x_69);
lean_dec(x_113);
lean_dec(x_2);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_13, 0);
lean_inc(x_117);
lean_dec(x_13);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_113, x_76, x_111, x_114, x_118, x_112, x_72, x_69);
lean_dec(x_113);
lean_dec(x_2);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_87);
lean_dec(x_76);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_120 = lean_ctor_get(x_74, 1);
lean_inc(x_120);
lean_dec(x_74);
x_121 = l_Lake_updateGitPkg___closed__1;
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_124 = lean_string_append(x_122, x_123);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_array_get_size(x_72);
x_128 = lean_array_push(x_72, x_126);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_128);
lean_ctor_set(x_21, 0, x_127);
return x_20;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_21, 1);
lean_inc(x_129);
lean_dec(x_21);
x_130 = lean_ctor_get(x_22, 0);
lean_inc(x_130);
lean_dec(x_22);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = l_System_FilePath_join(x_4, x_131);
lean_dec(x_131);
x_133 = l_Lake_RegistryPkg_gitSrc_x3f(x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_132);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec(x_130);
x_135 = l_Lake_updateGitPkg___closed__1;
x_136 = lean_string_append(x_135, x_134);
lean_dec(x_134);
x_137 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_138 = lean_string_append(x_136, x_137);
x_139 = 3;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = lean_array_get_size(x_129);
x_142 = lean_array_push(x_129, x_140);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_20, 0, x_143);
return x_20;
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_133, 0);
lean_inc(x_144);
lean_dec(x_133);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_free_object(x_20);
x_145 = lean_ctor_get(x_144, 2);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_144, 4);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_ctor_get(x_130, 1);
lean_inc(x_149);
lean_dec(x_130);
x_150 = l_Lake_updateGitPkg___closed__1;
x_151 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_149, x_132, x_146, x_150, x_147, x_148, x_129, x_69);
lean_dec(x_149);
lean_dec(x_2);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_144, 4);
lean_inc(x_153);
lean_dec(x_144);
x_154 = lean_ctor_get(x_130, 1);
lean_inc(x_154);
lean_dec(x_130);
x_155 = lean_ctor_get(x_13, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_156 = x_13;
} else {
 lean_dec_ref(x_13);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
x_158 = l_Lake_updateGitPkg___closed__1;
x_159 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_154, x_132, x_152, x_158, x_157, x_153, x_129, x_69);
lean_dec(x_154);
lean_dec(x_2);
return x_159;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_144, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_144, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_144, 4);
lean_inc(x_162);
lean_dec(x_144);
x_163 = lean_ctor_get(x_130, 1);
lean_inc(x_163);
lean_dec(x_130);
x_164 = lean_ctor_get(x_145, 0);
lean_inc(x_164);
lean_dec(x_145);
x_165 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_163, x_132, x_160, x_164, x_161, x_162, x_129, x_69);
lean_dec(x_163);
lean_dec(x_2);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_144, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_144, 4);
lean_inc(x_167);
lean_dec(x_144);
x_168 = lean_ctor_get(x_130, 1);
lean_inc(x_168);
lean_dec(x_130);
x_169 = lean_ctor_get(x_145, 0);
lean_inc(x_169);
lean_dec(x_145);
x_170 = lean_ctor_get(x_13, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_171 = x_13;
} else {
 lean_dec_ref(x_13);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_170);
x_173 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_168, x_132, x_166, x_169, x_172, x_167, x_129, x_69);
lean_dec(x_168);
lean_dec(x_2);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_144);
lean_dec(x_132);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 1);
lean_inc(x_174);
lean_dec(x_130);
x_175 = l_Lake_updateGitPkg___closed__1;
x_176 = lean_string_append(x_175, x_174);
lean_dec(x_174);
x_177 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_178 = lean_string_append(x_176, x_177);
x_179 = 3;
x_180 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_179);
x_181 = lean_array_get_size(x_129);
x_182 = lean_array_push(x_129, x_180);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_20, 0, x_183);
return x_20;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_20, 1);
lean_inc(x_184);
lean_dec(x_20);
x_185 = lean_ctor_get(x_21, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_186 = x_21;
} else {
 lean_dec_ref(x_21);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_22, 0);
lean_inc(x_187);
lean_dec(x_22);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = l_System_FilePath_join(x_4, x_188);
lean_dec(x_188);
x_190 = l_Lake_RegistryPkg_gitSrc_x3f(x_187);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_189);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
x_192 = l_Lake_updateGitPkg___closed__1;
x_193 = lean_string_append(x_192, x_191);
lean_dec(x_191);
x_194 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_195 = lean_string_append(x_193, x_194);
x_196 = 3;
x_197 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_196);
x_198 = lean_array_get_size(x_185);
x_199 = lean_array_push(x_185, x_197);
if (lean_is_scalar(x_186)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_186;
 lean_ctor_set_tag(x_200, 1);
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_184);
return x_201;
}
else
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_190, 0);
lean_inc(x_202);
lean_dec(x_190);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; 
lean_dec(x_186);
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
if (lean_obj_tag(x_203) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 4);
lean_inc(x_206);
lean_dec(x_202);
x_207 = lean_ctor_get(x_187, 1);
lean_inc(x_207);
lean_dec(x_187);
x_208 = l_Lake_updateGitPkg___closed__1;
x_209 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_207, x_189, x_204, x_208, x_205, x_206, x_185, x_184);
lean_dec(x_207);
lean_dec(x_2);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_202, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_202, 4);
lean_inc(x_211);
lean_dec(x_202);
x_212 = lean_ctor_get(x_187, 1);
lean_inc(x_212);
lean_dec(x_187);
x_213 = lean_ctor_get(x_13, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_214 = x_13;
} else {
 lean_dec_ref(x_13);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
x_216 = l_Lake_updateGitPkg___closed__1;
x_217 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_212, x_189, x_210, x_216, x_215, x_211, x_185, x_184);
lean_dec(x_212);
lean_dec(x_2);
return x_217;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_218 = lean_ctor_get(x_202, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_202, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_202, 4);
lean_inc(x_220);
lean_dec(x_202);
x_221 = lean_ctor_get(x_187, 1);
lean_inc(x_221);
lean_dec(x_187);
x_222 = lean_ctor_get(x_203, 0);
lean_inc(x_222);
lean_dec(x_203);
x_223 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_221, x_189, x_218, x_222, x_219, x_220, x_185, x_184);
lean_dec(x_221);
lean_dec(x_2);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_224 = lean_ctor_get(x_202, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_202, 4);
lean_inc(x_225);
lean_dec(x_202);
x_226 = lean_ctor_get(x_187, 1);
lean_inc(x_226);
lean_dec(x_187);
x_227 = lean_ctor_get(x_203, 0);
lean_inc(x_227);
lean_dec(x_203);
x_228 = lean_ctor_get(x_13, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_229 = x_13;
} else {
 lean_dec_ref(x_13);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
x_231 = l_Lake_Dependency_materialize_materializeGit(x_2, x_5, x_3, x_6, x_226, x_189, x_224, x_227, x_230, x_225, x_185, x_184);
lean_dec(x_226);
lean_dec(x_2);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_202);
lean_dec(x_189);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_232 = lean_ctor_get(x_187, 1);
lean_inc(x_232);
lean_dec(x_187);
x_233 = l_Lake_updateGitPkg___closed__1;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Lake_Dependency_materialize___lambda__2___closed__4;
x_236 = lean_string_append(x_234, x_235);
x_237 = 3;
x_238 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*1, x_237);
x_239 = lean_array_get_size(x_185);
x_240 = lean_array_push(x_185, x_238);
if (lean_is_scalar(x_186)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_186;
 lean_ctor_set_tag(x_241, 1);
}
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_184);
return x_242;
}
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_243 = !lean_is_exclusive(x_11);
if (x_243 == 0)
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_11);
lean_ctor_set(x_244, 1, x_12);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_11, 0);
x_246 = lean_ctor_get(x_11, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_11);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_12);
return x_248;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_string_utf8_byte_size(x_11);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lake_Dependency_materialize___lambda__2(x_12, x_1, x_3, x_5, x_2, x_4, x_10, x_16, x_7, x_8);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = 1;
x_19 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_20 = l_Lean_Name_toString(x_10, x_18, x_19);
x_21 = l_Lake_updateGitPkg___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lake_Dependency_materialize___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_get_size(x_7);
x_28 = lean_array_push(x_7, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_dec(x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = l_System_FilePath_join(x_6, x_35);
lean_dec(x_35);
lean_inc(x_36);
lean_ctor_set(x_31, 0, x_36);
x_37 = lean_box(0);
x_38 = l_Lake_defaultConfigFile;
x_39 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 4, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_2);
x_40 = l_Lake_updateGitPkg___closed__1;
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
lean_dec(x_31);
x_45 = l_System_FilePath_join(x_6, x_44);
lean_dec(x_44);
lean_inc(x_45);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_box(0);
x_48 = l_Lake_defaultConfigFile;
x_49 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_33);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set(x_49, 4, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*5, x_2);
x_50 = l_Lake_updateGitPkg___closed__1;
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_8);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_31, 2);
lean_inc(x_57);
lean_dec(x_31);
x_58 = 0;
x_59 = l_Lake_Dependency_materialize___lambda__2___closed__1;
x_60 = l_Lean_Name_toString(x_54, x_58, x_59);
lean_inc(x_55);
x_61 = l_Lake_Git_filterUrl_x3f(x_55);
x_62 = l_System_FilePath_join(x_5, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lake_updateGitPkg___closed__1;
x_64 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_60, x_62, x_55, x_63, x_56, x_57, x_7, x_8);
lean_dec(x_60);
lean_dec(x_1);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_60, x_62, x_55, x_65, x_56, x_57, x_7, x_8);
lean_dec(x_60);
lean_dec(x_1);
return x_66;
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lake_Dependency_materialize___lambda__2(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
return x_12;
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
x_88 = l_Lake_updateGitPkg___closed__10;
x_89 = l_Lake_updateGitPkg___closed__12;
x_90 = l_Lake_PackageEntry_materialize___closed__9;
x_91 = l_Lake_updateGitPkg___closed__11;
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
x_137 = l_Lake_updateGitPkg___closed__17;
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
l_Lake_cloneGitPkg___closed__1 = _init_l_Lake_cloneGitPkg___closed__1();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__1);
l_Lake_cloneGitPkg___closed__2 = _init_l_Lake_cloneGitPkg___closed__2();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__2);
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
