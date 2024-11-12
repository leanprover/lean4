// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: Init Lake.Load.Resolve Lake.Build.Module Lake.Build.Package Lake.Build.Library
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
extern lean_object* l_Lake_initPackageFacetConfigs;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspace___closed__1;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lake_initModuleFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_initLibraryFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspaceRoot___closed__3;
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspaceRoot___closed__1;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
static lean_object* l_Lake_loadWorkspaceRoot___closed__2;
lean_object* lean_array_mk(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[root]", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lake_Env_leanSearchPath(x_4);
x_6 = l_Lake_loadWorkspaceRoot___closed__1;
x_7 = lean_st_ref_set(x_6, x_5, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_loadWorkspaceRoot___closed__2;
lean_inc(x_1);
x_10 = l_Lake_loadPackageCore(x_9, x_1, x_2, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = l_Lake_loadWorkspaceRoot___closed__3;
x_24 = l_Lake_initModuleFacetConfigs;
x_25 = l_Lake_initPackageFacetConfigs;
x_26 = l_Lake_initLibraryFacetConfigs;
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_1);
lean_ctor_set(x_11, 0, x_27);
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_10);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_1, 6);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lake_Workspace_addFacetsFromEnv(x_28, x_29, x_27);
lean_dec(x_29);
x_31 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_30, x_14);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_11, 0, x_33);
lean_ctor_set(x_31, 0, x_11);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_11, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_io_error_to_string(x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_17);
x_43 = lean_array_push(x_17, x_41);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_43);
lean_ctor_set(x_11, 0, x_42);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_11);
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_io_error_to_string(x_44);
x_47 = 3;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_array_get_size(x_17);
x_50 = lean_array_push(x_17, x_48);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_50);
lean_ctor_set(x_11, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_dec(x_12);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_box(0);
x_57 = l_Lake_loadWorkspaceRoot___closed__3;
x_58 = l_Lake_initModuleFacetConfigs;
x_59 = l_Lake_initPackageFacetConfigs;
x_60 = l_Lake_initLibraryFacetConfigs;
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_4);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_57);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set(x_61, 5, x_58);
lean_ctor_set(x_61, 6, x_59);
lean_ctor_set(x_61, 7, x_60);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_62; 
lean_dec(x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_10, 0, x_62);
return x_10;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_10);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
lean_dec(x_54);
x_64 = lean_ctor_get(x_1, 6);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l_Lake_Workspace_addFacetsFromEnv(x_63, x_64, x_61);
lean_dec(x_64);
x_66 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_65, x_14);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_52);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
x_75 = lean_io_error_to_string(x_72);
x_76 = 3;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_array_get_size(x_52);
x_79 = lean_array_push(x_52, x_77);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_74)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_74;
 lean_ctor_set_tag(x_81, 0);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_10, 1);
lean_inc(x_82);
lean_dec(x_10);
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_84 = x_11;
} else {
 lean_dec_ref(x_11);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_12, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_12, 1);
lean_inc(x_86);
lean_dec(x_12);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = lean_box(0);
x_89 = l_Lake_loadWorkspaceRoot___closed__3;
x_90 = l_Lake_initModuleFacetConfigs;
x_91 = l_Lake_initPackageFacetConfigs;
x_92 = l_Lake_initLibraryFacetConfigs;
x_93 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_4);
lean_ctor_set(x_93, 2, x_87);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set(x_93, 4, x_88);
lean_ctor_set(x_93, 5, x_90);
lean_ctor_set(x_93, 6, x_91);
lean_ctor_set(x_93, 7, x_92);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
if (lean_is_scalar(x_84)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_84;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_83);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_82);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
lean_dec(x_86);
x_97 = lean_ctor_get(x_1, 6);
lean_inc(x_97);
lean_dec(x_1);
x_98 = l_Lake_Workspace_addFacetsFromEnv(x_96, x_97, x_93);
lean_dec(x_97);
x_99 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_98, x_82);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_84;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_83);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
x_108 = lean_io_error_to_string(x_105);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_get_size(x_83);
x_112 = lean_array_push(x_83, x_110);
if (lean_is_scalar(x_84)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_84;
 lean_ctor_set_tag(x_113, 1);
}
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
if (lean_is_scalar(x_107)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_107;
 lean_ctor_set_tag(x_114, 0);
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_4);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_10);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_10, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_11);
if (x_117 == 0)
{
return x_10;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_11, 0);
x_119 = lean_ctor_get(x_11, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_11);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_10, 0, x_120);
return x_10;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_10, 1);
lean_inc(x_121);
lean_dec(x_10);
x_122 = lean_ctor_get(x_11, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_11, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_124 = x_11;
} else {
 lean_dec_ref(x_11);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_121);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_4);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_10);
if (x_127 == 0)
{
return x_10;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_10, 0);
x_129 = lean_ctor_get(x_10, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_10);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
static lean_object* _init_l_Lake_loadWorkspace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 2);
x_107 = l_Lake_loadWorkspace___closed__1;
x_108 = l_Lake_loadWorkspaceRoot(x_1, x_107, x_3);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_array_get_size(x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_nat_dec_lt(x_114, x_113);
if (x_115 == 0)
{
lean_dec(x_113);
lean_dec(x_112);
x_8 = x_111;
x_9 = x_110;
goto block_106;
}
else
{
uint8_t x_116; 
x_116 = lean_nat_dec_le(x_113, x_113);
if (x_116 == 0)
{
lean_dec(x_113);
lean_dec(x_112);
x_8 = x_111;
x_9 = x_110;
goto block_106;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_119 = lean_box(0);
lean_inc(x_2);
x_120 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_112, x_117, x_118, x_119, x_2, x_110);
lean_dec(x_112);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_8 = x_111;
x_9 = x_121;
goto block_106;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_4);
x_122 = !lean_is_exclusive(x_108);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_108, 1);
x_124 = lean_ctor_get(x_108, 0);
lean_dec(x_124);
x_125 = lean_ctor_get(x_109, 1);
lean_inc(x_125);
lean_dec(x_109);
x_126 = lean_array_get_size(x_125);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_nat_dec_lt(x_127, x_126);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_2);
x_129 = lean_box(0);
lean_ctor_set_tag(x_108, 1);
lean_ctor_set(x_108, 0, x_129);
return x_108;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_126, x_126);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_2);
x_131 = lean_box(0);
lean_ctor_set_tag(x_108, 1);
lean_ctor_set(x_108, 0, x_131);
return x_108;
}
else
{
size_t x_132; size_t x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_free_object(x_108);
x_132 = 0;
x_133 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_134 = lean_box(0);
x_135 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_125, x_132, x_133, x_134, x_2, x_123);
lean_dec(x_125);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set_tag(x_135, 1);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_108, 1);
lean_inc(x_140);
lean_dec(x_108);
x_141 = lean_ctor_get(x_109, 1);
lean_inc(x_141);
lean_dec(x_109);
x_142 = lean_array_get_size(x_141);
x_143 = lean_unsigned_to_nat(0u);
x_144 = lean_nat_dec_lt(x_143, x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_2);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_140);
return x_146;
}
else
{
uint8_t x_147; 
x_147 = lean_nat_dec_le(x_142, x_142);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_2);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_140);
return x_149;
}
else
{
size_t x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = 0;
x_151 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_152 = lean_box(0);
x_153 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_141, x_150, x_151, x_152, x_2, x_140);
lean_dec(x_141);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
 lean_ctor_set_tag(x_156, 1);
}
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
}
block_106:
{
if (x_6 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_System_FilePath_join(x_11, x_12);
lean_dec(x_12);
x_14 = l_Lake_Manifest_load_x3f(x_13, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_NameSet_empty;
x_18 = l_Lake_Workspace_updateAndMaterialize(x_8, x_17, x_4, x_7, x_2, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lake_loadWorkspace___closed__1;
x_22 = l_Lake_Workspace_materializeDeps(x_8, x_20, x_4, x_5, x_21, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_29, x_29);
if (x_32 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_free_object(x_22);
x_33 = 0;
x_34 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_28, x_33, x_34, x_35, x_2, x_25);
lean_dec(x_28);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_27);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_dec(x_22);
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_array_get_size(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_44, x_44);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_43, x_50, x_51, x_52, x_2, x_41);
lean_dec(x_43);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_22, 1);
x_59 = lean_ctor_get(x_22, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_23, 1);
lean_inc(x_60);
lean_dec(x_23);
x_61 = lean_array_get_size(x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_2);
x_64 = lean_box(0);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_64);
return x_22;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_61, x_61);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_2);
x_66 = lean_box(0);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_66);
return x_22;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_free_object(x_22);
x_67 = 0;
x_68 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_69 = lean_box(0);
x_70 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_60, x_67, x_68, x_69, x_2, x_58);
lean_dec(x_60);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_22, 1);
lean_inc(x_75);
lean_dec(x_22);
x_76 = lean_ctor_get(x_23, 1);
lean_inc(x_76);
lean_dec(x_23);
x_77 = lean_array_get_size(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_lt(x_78, x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_2);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = lean_nat_dec_le(x_77, x_77);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_2);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
return x_84;
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_87 = lean_box(0);
x_88 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_76, x_85, x_86, x_87, x_2, x_75);
lean_dec(x_76);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_8);
lean_dec(x_4);
x_92 = lean_ctor_get(x_14, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_14, 1);
lean_inc(x_93);
lean_dec(x_14);
x_94 = lean_io_error_to_string(x_92);
x_95 = 3;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_97 = lean_apply_2(x_2, x_96, x_93);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
x_100 = lean_box(0);
lean_ctor_set_tag(x_97, 1);
lean_ctor_set(x_97, 0, x_100);
return x_97;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_NameSet_empty;
x_105 = l_Lake_Workspace_updateAndMaterialize(x_8, x_104, x_4, x_7, x_2, x_9);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_1, 6);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 2);
x_21 = l_Lake_loadWorkspace___closed__1;
x_22 = l_Lake_loadWorkspaceRoot(x_1, x_21, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
x_7 = x_25;
x_8 = x_24;
goto block_20;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
x_7 = x_25;
x_8 = x_24;
goto block_20;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_33 = lean_box(0);
lean_inc(x_3);
x_34 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_26, x_31, x_32, x_33, x_3, x_24);
lean_dec(x_26);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_7 = x_25;
x_8 = x_35;
goto block_20;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_22, 1);
x_38 = lean_ctor_get(x_22, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_array_get_size(x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_lt(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_3);
x_43 = lean_box(0);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_43);
return x_22;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_40, x_40);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_3);
x_45 = lean_box(0);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_45);
return x_22;
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_free_object(x_22);
x_46 = 0;
x_47 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_48 = lean_box(0);
x_49 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_39, x_46, x_47, x_48, x_3, x_37);
lean_dec(x_39);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_dec(x_22);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_dec(x_23);
x_56 = lean_array_get_size(x_55);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_lt(x_57, x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_3);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_56, x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_3);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_66 = lean_box(0);
x_67 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_55, x_64, x_65, x_66, x_3, x_54);
lean_dec(x_55);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
block_20:
{
lean_object* x_9; 
x_9 = l_Lake_Workspace_updateAndMaterialize(x_7, x_2, x_5, x_6, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateManifest(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Resolve(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Workspace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Resolve(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Library(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_loadWorkspaceRoot___closed__1 = _init_l_Lake_loadWorkspaceRoot___closed__1();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__1);
l_Lake_loadWorkspaceRoot___closed__2 = _init_l_Lake_loadWorkspaceRoot___closed__2();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__2);
l_Lake_loadWorkspaceRoot___closed__3 = _init_l_Lake_loadWorkspaceRoot___closed__3();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__3);
l_Lake_loadWorkspace___closed__1 = _init_l_Lake_loadWorkspace___closed__1();
lean_mark_persistent(l_Lake_loadWorkspace___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
