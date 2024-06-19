// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: Init Lake.Util.Git Lake.Load.Manifest Lake.Config.Dependency Lake.Config.Package
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
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__7;
static lean_object* l_Lake_updateGitRepo___closed__1;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__18;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__20;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__9;
static lean_object* l_Lake_updateGitPkg___closed__13;
static lean_object* l_Lake_updateGitRepo___closed__8;
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitRepo___closed__9;
static lean_object* l_Lake_cloneGitPkg___closed__4;
static lean_object* l_Lake_updateGitPkg___closed__8;
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__4;
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__1;
static lean_object* l_Lake_updateGitPkg___closed__22;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__21;
static lean_object* l_Lake_updateGitPkg___closed__15;
static lean_object* l_Lake_updateGitRepo___closed__5;
static lean_object* l_Lake_updateGitRepo___closed__3;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
static lean_object* l_Lake_updateGitRepo___closed__7;
static lean_object* l_Lake_updateGitRepo___closed__4;
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__2;
static lean_object* l_Lake_updateGitPkg___closed__10;
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_captureProc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__3;
static lean_object* l_Lake_updateGitPkg___closed__17;
static lean_object* l_Lake_updateGitPkg___closed__16;
static lean_object* l_Lake_updateGitPkg___closed__19;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkEntry___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__3;
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_testProc(lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
static lean_object* l_Lake_updateGitPkg___closed__12;
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_cloneGitPkg___closed__1;
static lean_object* l_Lake_updateGitRepo___closed__2;
static lean_object* l_Lake_updateGitPkg___closed__23;
static lean_object* l_Lake_updateGitPkg___closed__24;
static lean_object* l_Lake_updateGitRepo___closed__6;
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkEntry(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__6;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__1;
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__2;
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__3;
static lean_object* l_Lake_updateGitPkg___closed__14;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_updateGitPkg___closed__5;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
static lean_object* l_Lake_updateGitPkg___closed__25;
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedMaterializedDep___closed__2;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateGitPkg___closed__11;
static lean_object* _init_l_Lake_updateGitPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": repository '", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has local changes", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rev-parse", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__4;
x_2 = l_Lake_updateGitPkg___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--verify", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__6;
x_2 = l_Lake_updateGitPkg___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HEAD", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__8;
x_2 = l_Lake_updateGitPkg___closed__9;
x_3 = lean_array_push(x_1, x_2);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": updating repository '", 23);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' to revision '", 15);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("checkout", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__4;
x_2 = l_Lake_updateGitPkg___closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--detach", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__18;
x_2 = l_Lake_updateGitPkg___closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("diff", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__21;
x_2 = l_Lake_updateGitPkg___closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--exit-code", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitPkg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__23;
x_2 = l_Lake_updateGitPkg___closed__24;
x_3 = lean_array_push(x_1, x_2);
return x_3;
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_2);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_2);
x_55 = l_Lake_updateGitPkg___closed__11;
x_56 = l_Lake_updateGitPkg___closed__13;
x_57 = l_Lake_updateGitPkg___closed__10;
x_58 = l_Lake_updateGitPkg___closed__12;
x_59 = 0;
lean_inc(x_54);
x_60 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_54);
lean_ctor_set(x_60, 4, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*5, x_59);
x_61 = l_Lake_captureProc(x_60, x_53, x_51);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_ctor_get(x_62, 1);
x_67 = lean_string_dec_eq(x_65, x_52);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
lean_free_object(x_62);
x_68 = l_Lake_updateGitPkg___closed__1;
x_69 = lean_string_append(x_68, x_1);
x_70 = l_Lake_updateGitPkg___closed__14;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_string_append(x_71, x_2);
lean_dec(x_2);
x_73 = l_Lake_updateGitPkg___closed__15;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_string_append(x_74, x_52);
x_76 = l_Lake_updateGitPkg___closed__16;
x_77 = lean_string_append(x_75, x_76);
x_78 = 1;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_push(x_66, x_79);
x_81 = l_Lake_updateGitPkg___closed__20;
x_82 = lean_array_push(x_81, x_52);
x_83 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_83, 0, x_55);
lean_ctor_set(x_83, 1, x_56);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_54);
lean_ctor_set(x_83, 4, x_58);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_59);
x_84 = 1;
x_85 = l_Lake_proc(x_83, x_84, x_80, x_63);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_52);
x_86 = l_Lake_updateGitPkg___closed__25;
x_87 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_87, 0, x_55);
lean_ctor_set(x_87, 1, x_56);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_54);
lean_ctor_set(x_87, 4, x_58);
lean_ctor_set_uint8(x_87, sizeof(void*)*5, x_59);
x_88 = l_Lake_testProc(x_87, x_63);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = 1;
x_93 = lean_box(x_92);
lean_ctor_set(x_62, 0, x_93);
x_6 = x_62;
x_7 = x_91;
goto block_47;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
x_95 = lean_box(x_59);
lean_ctor_set(x_62, 0, x_95);
x_6 = x_62;
x_7 = x_94;
goto block_47;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_62, 0);
x_97 = lean_ctor_get(x_62, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_62);
x_98 = lean_string_dec_eq(x_96, x_52);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_99 = l_Lake_updateGitPkg___closed__1;
x_100 = lean_string_append(x_99, x_1);
x_101 = l_Lake_updateGitPkg___closed__14;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_2);
lean_dec(x_2);
x_104 = l_Lake_updateGitPkg___closed__15;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_string_append(x_105, x_52);
x_107 = l_Lake_updateGitPkg___closed__16;
x_108 = lean_string_append(x_106, x_107);
x_109 = 1;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_push(x_97, x_110);
x_112 = l_Lake_updateGitPkg___closed__20;
x_113 = lean_array_push(x_112, x_52);
x_114 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_114, 0, x_55);
lean_ctor_set(x_114, 1, x_56);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_54);
lean_ctor_set(x_114, 4, x_58);
lean_ctor_set_uint8(x_114, sizeof(void*)*5, x_59);
x_115 = 1;
x_116 = l_Lake_proc(x_114, x_115, x_111, x_63);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_52);
x_117 = l_Lake_updateGitPkg___closed__25;
x_118 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_118, 0, x_55);
lean_ctor_set(x_118, 1, x_56);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_54);
lean_ctor_set(x_118, 4, x_58);
lean_ctor_set_uint8(x_118, sizeof(void*)*5, x_59);
x_119 = l_Lake_testProc(x_118, x_63);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = 1;
x_124 = lean_box(x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_97);
x_6 = x_125;
x_7 = x_122;
goto block_47;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_127 = lean_box(x_59);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_97);
x_6 = x_128;
x_7 = x_126;
goto block_47;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_61);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_61, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_62);
if (x_131 == 0)
{
return x_61;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_62, 0);
x_133 = lean_ctor_get(x_62, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_62);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_61, 0, x_134);
return x_61;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_61, 1);
lean_inc(x_135);
lean_dec(x_61);
x_136 = lean_ctor_get(x_62, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_62, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_138 = x_62;
} else {
 lean_dec_ref(x_62);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_49);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_49, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_50);
if (x_143 == 0)
{
return x_49;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_50, 0);
x_145 = lean_ctor_get(x_50, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_50);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_49, 0, x_146);
return x_49;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_49, 1);
lean_inc(x_147);
lean_dec(x_49);
x_148 = lean_ctor_get(x_50, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_50, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_150 = x_50;
} else {
 lean_dec_ref(x_50);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_147);
return x_152;
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
x_1 = lean_mk_string_from_bytes(": cloning ", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" to '", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("clone", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_cloneGitPkg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__4;
x_2 = l_Lake_cloneGitPkg___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_7 = l_Lake_updateGitPkg___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lake_cloneGitPkg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_3);
x_12 = l_Lake_cloneGitPkg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_2);
x_15 = l_Lake_updateGitPkg___closed__16;
x_16 = lean_string_append(x_14, x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_push(x_5, x_18);
x_20 = l_Lake_cloneGitPkg___closed__4;
x_21 = lean_array_push(x_20, x_3);
lean_inc(x_2);
x_22 = lean_array_push(x_21, x_2);
x_23 = lean_box(0);
x_24 = l_Lake_updateGitPkg___closed__11;
x_25 = l_Lake_updateGitPkg___closed__13;
x_26 = l_Lake_updateGitPkg___closed__12;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_27);
x_29 = 1;
x_30 = l_Lake_proc(x_28, x_29, x_19, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_42 = x_31;
} else {
 lean_dec_ref(x_31);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_dec(x_31);
x_48 = !lean_is_exclusive(x_4);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = l_Lake_Git_defaultRemote;
lean_inc(x_2);
x_51 = l_Lake_GitRepo_resolveRemoteRevision(x_49, x_50, x_2, x_47, x_46);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lake_updateGitPkg___closed__20;
x_57 = lean_array_push(x_56, x_54);
lean_ctor_set(x_4, 0, x_2);
x_58 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_58, 0, x_24);
lean_ctor_set(x_58, 1, x_25);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_4);
lean_ctor_set(x_58, 4, x_26);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_27);
x_59 = l_Lake_proc(x_58, x_29, x_55, x_53);
return x_59;
}
else
{
uint8_t x_60; 
lean_free_object(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_51, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_51;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_51, 0, x_65);
return x_51;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_dec(x_51);
x_67 = lean_ctor_get(x_52, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_69 = x_52;
} else {
 lean_dec_ref(x_52);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_4, 0);
lean_inc(x_72);
lean_dec(x_4);
x_73 = l_Lake_Git_defaultRemote;
lean_inc(x_2);
x_74 = l_Lake_GitRepo_resolveRemoteRevision(x_72, x_73, x_2, x_47, x_46);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l_Lake_updateGitPkg___closed__20;
x_80 = lean_array_push(x_79, x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_2);
x_82 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_82, 0, x_24);
lean_ctor_set(x_82, 1, x_25);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_81);
lean_ctor_set(x_82, 4, x_26);
lean_ctor_set_uint8(x_82, sizeof(void*)*5, x_27);
x_83 = l_Lake_proc(x_82, x_29, x_78, x_76);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_2);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_85 = x_74;
} else {
 lean_dec_ref(x_74);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_88 = x_75;
} else {
 lean_dec_ref(x_75);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_30);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_30, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_31);
if (x_93 == 0)
{
return x_30;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_31, 0);
x_95 = lean_ctor_get(x_31, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_31);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_30, 0, x_96);
return x_30;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_30, 1);
lean_inc(x_97);
lean_dec(x_30);
x_98 = lean_ctor_get(x_31, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_31, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_100 = x_31;
} else {
 lean_dec_ref(x_31);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_97);
return x_102;
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
x_1 = lean_mk_string_from_bytes(": URL has changed; deleting '", 29);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' and cloning again", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": URL has changed; you might need to delete '", 45);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' manually", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("remote", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitPkg___closed__4;
x_2 = l_Lake_updateGitRepo___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("get-url", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitRepo___closed__6;
x_2 = l_Lake_updateGitRepo___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateGitRepo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_updateGitRepo___closed__8;
x_2 = l_Lake_Git_defaultRemote;
x_3 = lean_array_push(x_1, x_2);
return x_3;
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
x_96 = l_Lake_updateGitRepo___closed__9;
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
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lake_updateGitPkg___closed__1;
x_5 = l_Lake_instInhabitedMaterializedDep___closed__1;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_updateGitPkg___closed__1;
x_3 = l_Lake_instInhabitedMaterializedDep___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
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
x_3 = lean_ctor_get(x_2, 1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_box(0);
x_6 = l_Lake_defaultConfigFile;
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_2);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_System_FilePath_join(x_6, x_11);
x_13 = lean_box(0);
lean_inc(x_12);
lean_ctor_set(x_9, 0, x_12);
x_14 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_9);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l_System_FilePath_join(x_6, x_18);
x_20 = lean_box(0);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_21);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_110; lean_object* x_111; 
lean_dec(x_6);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_9, 2);
lean_inc(x_28);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 x_29 = x_9;
} else {
 lean_dec_ref(x_9);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = 0;
lean_inc(x_30);
x_32 = l_Lean_Name_toString(x_30, x_31);
lean_inc(x_32);
x_33 = l_System_FilePath_join(x_5, x_32);
lean_inc(x_33);
x_34 = l_System_FilePath_join(x_4, x_33);
x_110 = lean_ctor_get(x_3, 4);
x_111 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_110, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_111) == 0)
{
lean_inc(x_26);
x_35 = x_26;
goto block_109;
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_35 = x_112;
goto block_109;
}
block_109:
{
lean_object* x_36; lean_object* x_37; 
lean_inc(x_27);
lean_inc(x_34);
x_36 = l_Lake_materializeGitRepo(x_32, x_34, x_35, x_27, x_7, x_8);
lean_dec(x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_34);
x_41 = l_Lake_updateGitPkg___closed__11;
x_42 = l_Lake_updateGitPkg___closed__13;
x_43 = l_Lake_updateGitPkg___closed__10;
x_44 = l_Lake_updateGitPkg___closed__12;
x_45 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_31);
x_46 = l_Lake_captureProc(x_45, x_39, x_38);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_26);
x_52 = l_Lake_Git_filterUrl_x3f(x_26);
lean_inc(x_28);
x_53 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_27);
lean_ctor_set(x_53, 3, x_28);
x_54 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_53);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_55; 
if (lean_is_scalar(x_29)) {
 x_55 = lean_alloc_ctor(0, 3, 0);
} else {
 x_55 = x_29;
 lean_ctor_set_tag(x_55, 0);
}
lean_ctor_set(x_55, 0, x_33);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_47, 0, x_55);
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_28, 0);
lean_inc(x_56);
lean_dec(x_28);
x_57 = l_System_FilePath_join(x_33, x_56);
if (lean_is_scalar(x_29)) {
 x_58 = lean_alloc_ctor(0, 3, 0);
} else {
 x_58 = x_29;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set(x_47, 0, x_58);
return x_46;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
lean_inc(x_26);
x_61 = l_Lake_Git_filterUrl_x3f(x_26);
lean_inc(x_28);
x_62 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_27);
lean_ctor_set(x_62, 3, x_28);
x_63 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_62);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_64; lean_object* x_65; 
if (lean_is_scalar(x_29)) {
 x_64 = lean_alloc_ctor(0, 3, 0);
} else {
 x_64 = x_29;
 lean_ctor_set_tag(x_64, 0);
}
lean_ctor_set(x_64, 0, x_33);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_46, 0, x_65);
return x_46;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_28, 0);
lean_inc(x_66);
lean_dec(x_28);
x_67 = l_System_FilePath_join(x_33, x_66);
if (lean_is_scalar(x_29)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_29;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
lean_ctor_set(x_46, 0, x_69);
return x_46;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_dec(x_46);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_73 = x_47;
} else {
 lean_dec_ref(x_47);
 x_73 = lean_box(0);
}
lean_inc(x_26);
x_74 = l_Lake_Git_filterUrl_x3f(x_26);
lean_inc(x_28);
x_75 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_75, 0, x_26);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_27);
lean_ctor_set(x_75, 3, x_28);
x_76 = l_Lake_Dependency_materialize_mkEntry(x_1, x_2, x_75);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
if (lean_is_scalar(x_29)) {
 x_77 = lean_alloc_ctor(0, 3, 0);
} else {
 x_77 = x_29;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_33);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_76);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_70);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_28, 0);
lean_inc(x_80);
lean_dec(x_28);
x_81 = l_System_FilePath_join(x_33, x_80);
if (lean_is_scalar(x_29)) {
 x_82 = lean_alloc_ctor(0, 3, 0);
} else {
 x_82 = x_29;
 lean_ctor_set_tag(x_82, 0);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_76);
if (lean_is_scalar(x_73)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_73;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_72);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_70);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_46);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_46, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_47);
if (x_87 == 0)
{
return x_46;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_47, 0);
x_89 = lean_ctor_get(x_47, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_47);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_46, 0, x_90);
return x_46;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_46, 1);
lean_inc(x_91);
lean_dec(x_46);
x_92 = lean_ctor_get(x_47, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_47, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_94 = x_47;
} else {
 lean_dec_ref(x_47);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_36);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_36, 0);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_37);
if (x_99 == 0)
{
return x_36;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_37, 0);
x_101 = lean_ctor_get(x_37, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_37);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_36, 0, x_102);
return x_36;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_36, 1);
lean_inc(x_103);
lean_dec(x_36);
x_104 = lean_ctor_get(x_37, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_106 = x_37;
} else {
 lean_dec_ref(x_37);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_103);
return x_108;
}
}
}
}
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_System_FilePath_join(x_3, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
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
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_45; 
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
lean_inc(x_16);
x_18 = l_Lean_Name_toString(x_16, x_17);
lean_inc(x_18);
x_19 = l_System_FilePath_join(x_4, x_18);
lean_inc(x_19);
x_20 = l_System_FilePath_join(x_3, x_19);
x_21 = l_System_FilePath_isDir(x_20, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_45 = lean_unbox(x_22);
lean_dec(x_22);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_2, 4);
x_47 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_46, x_16);
lean_dec(x_16);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_inc(x_13);
x_49 = l_Lake_cloneGitPkg(x_18, x_20, x_13, x_48, x_5, x_23);
lean_dec(x_18);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_19, x_1, x_52, x_53, x_51);
lean_dec(x_52);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_49, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_49, 0, x_60);
return x_49;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_dec(x_49);
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_64 = x_50;
} else {
 lean_dec_ref(x_50);
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
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = l_Lake_cloneGitPkg(x_18, x_20, x_67, x_48, x_5, x_23);
lean_dec(x_18);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_19, x_1, x_71, x_72, x_70);
lean_dec(x_71);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_68, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_69);
if (x_76 == 0)
{
return x_68;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_69, 0);
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_69);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_68, 0, x_79);
return x_68;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
lean_dec(x_68);
x_81 = lean_ctor_get(x_69, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_inc(x_20);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_20);
x_87 = l_Lake_updateGitPkg___closed__11;
x_88 = l_Lake_updateGitPkg___closed__13;
x_89 = l_Lake_updateGitPkg___closed__10;
x_90 = l_Lake_updateGitPkg___closed__12;
lean_inc(x_86);
x_91 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set(x_91, 3, x_86);
lean_ctor_set(x_91, 4, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*5, x_17);
x_92 = l_Lake_captureProc_x3f(x_91, x_23);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_14);
x_96 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(x_93, x_95);
lean_dec(x_93);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_86);
x_97 = lean_ctor_get(x_2, 4);
x_98 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_97, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_inc(x_13);
x_99 = l_Lake_updateGitRepo(x_18, x_20, x_13, x_95, x_5, x_94);
lean_dec(x_18);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_19, x_1, x_102, x_103, x_101);
lean_dec(x_102);
return x_104;
}
else
{
uint8_t x_105; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_99);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_99, 0);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_100);
if (x_107 == 0)
{
return x_99;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_100, 0);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_100);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_99, 0, x_110);
return x_99;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_114 = x_100;
} else {
 lean_dec_ref(x_100);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_98, 0);
lean_inc(x_117);
lean_dec(x_98);
x_118 = l_Lake_updateGitRepo(x_18, x_20, x_117, x_95, x_5, x_94);
lean_dec(x_18);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_19, x_1, x_121, x_122, x_120);
lean_dec(x_121);
return x_123;
}
else
{
uint8_t x_124; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_118);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_118, 0);
lean_dec(x_125);
x_126 = !lean_is_exclusive(x_119);
if (x_126 == 0)
{
return x_118;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_119, 0);
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_119);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_118, 0, x_129);
return x_118;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
lean_dec(x_118);
x_131 = lean_ctor_get(x_119, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_119, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_133 = x_119;
} else {
 lean_dec_ref(x_119);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_95);
lean_dec(x_16);
x_136 = l_Lake_updateGitPkg___closed__25;
x_137 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_137, 0, x_87);
lean_ctor_set(x_137, 1, x_88);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_86);
lean_ctor_set(x_137, 4, x_90);
lean_ctor_set_uint8(x_137, sizeof(void*)*5, x_17);
x_138 = l_Lake_testProc(x_137, x_94);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_138);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_138, 1);
x_143 = lean_ctor_get(x_138, 0);
lean_dec(x_143);
x_144 = 1;
x_145 = lean_box(x_144);
lean_ctor_set(x_138, 1, x_5);
lean_ctor_set(x_138, 0, x_145);
x_24 = x_138;
x_25 = x_142;
goto block_44;
}
else
{
lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_138, 1);
lean_inc(x_146);
lean_dec(x_138);
x_147 = 1;
x_148 = lean_box(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_5);
x_24 = x_149;
x_25 = x_146;
goto block_44;
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_138);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_138, 1);
x_152 = lean_ctor_get(x_138, 0);
lean_dec(x_152);
x_153 = lean_box(x_17);
lean_ctor_set(x_138, 1, x_5);
lean_ctor_set(x_138, 0, x_153);
x_24 = x_138;
x_25 = x_151;
goto block_44;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_138, 1);
lean_inc(x_154);
lean_dec(x_138);
x_155 = lean_box(x_17);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_5);
x_24 = x_156;
x_25 = x_154;
goto block_44;
}
}
}
}
block_44:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_18);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_19, x_1, x_29, x_28, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = l_Lake_updateGitPkg___closed__1;
x_33 = lean_string_append(x_32, x_18);
lean_dec(x_18);
x_34 = l_Lake_updateGitPkg___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_20);
lean_dec(x_20);
x_37 = l_Lake_updateGitPkg___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = 2;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_push(x_31, x_40);
x_42 = lean_box(0);
x_43 = l_Lake_PackageEntry_materialize___lambda__1(x_13, x_15, x_19, x_1, x_42, x_41, x_25);
return x_43;
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
l_Lake_updateGitPkg___closed__20 = _init_l_Lake_updateGitPkg___closed__20();
lean_mark_persistent(l_Lake_updateGitPkg___closed__20);
l_Lake_updateGitPkg___closed__21 = _init_l_Lake_updateGitPkg___closed__21();
lean_mark_persistent(l_Lake_updateGitPkg___closed__21);
l_Lake_updateGitPkg___closed__22 = _init_l_Lake_updateGitPkg___closed__22();
lean_mark_persistent(l_Lake_updateGitPkg___closed__22);
l_Lake_updateGitPkg___closed__23 = _init_l_Lake_updateGitPkg___closed__23();
lean_mark_persistent(l_Lake_updateGitPkg___closed__23);
l_Lake_updateGitPkg___closed__24 = _init_l_Lake_updateGitPkg___closed__24();
lean_mark_persistent(l_Lake_updateGitPkg___closed__24);
l_Lake_updateGitPkg___closed__25 = _init_l_Lake_updateGitPkg___closed__25();
lean_mark_persistent(l_Lake_updateGitPkg___closed__25);
l_Lake_cloneGitPkg___closed__1 = _init_l_Lake_cloneGitPkg___closed__1();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__1);
l_Lake_cloneGitPkg___closed__2 = _init_l_Lake_cloneGitPkg___closed__2();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__2);
l_Lake_cloneGitPkg___closed__3 = _init_l_Lake_cloneGitPkg___closed__3();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__3);
l_Lake_cloneGitPkg___closed__4 = _init_l_Lake_cloneGitPkg___closed__4();
lean_mark_persistent(l_Lake_cloneGitPkg___closed__4);
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
l_Lake_instInhabitedMaterializedDep___closed__1 = _init_l_Lake_instInhabitedMaterializedDep___closed__1();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__1);
l_Lake_instInhabitedMaterializedDep___closed__2 = _init_l_Lake_instInhabitedMaterializedDep___closed__2();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__2);
l_Lake_instInhabitedMaterializedDep___closed__3 = _init_l_Lake_instInhabitedMaterializedDep___closed__3();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep___closed__3);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
