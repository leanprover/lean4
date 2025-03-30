// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: Lake.Load.Resolve Lake.Build.InitFacets
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
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspace___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspaceRoot___closed__3;
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_initFacetConfigs;
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
lean_object* l_Array_emptyWithCapacity(lean_object*, lean_object*);
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
x_2 = l_Array_emptyWithCapacity(lean_box(0), x_1);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_24 = l_Lake_initFacetConfigs;
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_25, 5, x_24);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_1);
lean_ctor_set(x_11, 0, x_25);
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_10);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_1, 7);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_Workspace_addFacetsFromEnv(x_26, x_27, x_25);
lean_dec(x_27);
x_29 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_28, x_14);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_11, 0, x_31);
lean_ctor_set(x_29, 0, x_11);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_11, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_io_error_to_string(x_36);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_17);
x_41 = lean_array_push(x_17, x_39);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_41);
lean_ctor_set(x_11, 0, x_40);
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 0, x_11);
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_io_error_to_string(x_42);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_get_size(x_17);
x_48 = lean_array_push(x_17, x_46);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_48);
lean_ctor_set(x_11, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_dec(x_11);
x_51 = lean_ctor_get(x_12, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_box(0);
x_55 = l_Lake_loadWorkspaceRoot___closed__3;
x_56 = l_Lake_initFacetConfigs;
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_4);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_55);
lean_ctor_set(x_57, 4, x_54);
lean_ctor_set(x_57, 5, x_56);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_58; 
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_10, 0, x_58);
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_10);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_1, 7);
lean_inc(x_60);
lean_dec(x_1);
x_61 = l_Lake_Workspace_addFacetsFromEnv(x_59, x_60, x_57);
lean_dec(x_60);
x_62 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_61, x_14);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_50);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_io_error_to_string(x_68);
x_72 = 3;
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_array_get_size(x_50);
x_75 = lean_array_push(x_50, x_73);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_70;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_10, 1);
lean_inc(x_78);
lean_dec(x_10);
x_79 = lean_ctor_get(x_11, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_80 = x_11;
} else {
 lean_dec_ref(x_11);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_12, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_dec(x_12);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
x_84 = lean_box(0);
x_85 = l_Lake_loadWorkspaceRoot___closed__3;
x_86 = l_Lake_initFacetConfigs;
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_4);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_85);
lean_ctor_set(x_87, 4, x_84);
lean_ctor_set(x_87, 5, x_86);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_1);
if (lean_is_scalar(x_80)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_80;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_79);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
lean_dec(x_82);
x_91 = lean_ctor_get(x_1, 7);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lake_Workspace_addFacetsFromEnv(x_90, x_91, x_87);
lean_dec(x_91);
x_93 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_92, x_78);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_80;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_79);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
x_102 = lean_io_error_to_string(x_99);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_get_size(x_79);
x_106 = lean_array_push(x_79, x_104);
if (lean_is_scalar(x_80)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_80;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_101)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_101;
 lean_ctor_set_tag(x_108, 0);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_4);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_10);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_10, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_11);
if (x_111 == 0)
{
return x_10;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_11, 0);
x_113 = lean_ctor_get(x_11, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_11);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_10, 0, x_114);
return x_10;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_10, 1);
lean_inc(x_115);
lean_dec(x_10);
x_116 = lean_ctor_get(x_11, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_11, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_118 = x_11;
} else {
 lean_dec_ref(x_11);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_115);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_4);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_10);
if (x_121 == 0)
{
return x_10;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_10, 0);
x_123 = lean_ctor_get(x_10, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_10);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 7);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*10);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 2);
x_38 = l_Lake_loadWorkspace___closed__1;
x_39 = l_Lake_loadWorkspaceRoot(x_1, x_38, x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_array_get_size(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_9 = x_42;
x_10 = x_41;
goto block_37;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_44, x_44);
if (x_47 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_9 = x_42;
x_10 = x_41;
goto block_37;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_50 = lean_box(0);
lean_inc(x_2);
x_51 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_43, x_48, x_49, x_50, x_2, x_41);
lean_dec(x_43);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_9 = x_42;
x_10 = x_52;
goto block_37;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_39, 1);
x_55 = lean_ctor_get(x_39, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_array_get_size(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_lt(x_58, x_57);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_2);
x_60 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_60);
return x_39;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_57, x_57);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_2);
x_62 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_62);
return x_39;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_39);
x_63 = 0;
x_64 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_65 = lean_box(0);
x_66 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_56, x_63, x_64, x_65, x_2, x_54);
lean_dec(x_56);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_39, 1);
lean_inc(x_71);
lean_dec(x_39);
x_72 = lean_ctor_get(x_40, 1);
lean_inc(x_72);
lean_dec(x_40);
x_73 = lean_array_get_size(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_2);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_73, x_73);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_71);
return x_80;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_83 = lean_box(0);
x_84 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_72, x_81, x_82, x_83, x_2, x_71);
lean_dec(x_72);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
block_37:
{
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 5);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_System_FilePath_join(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lake_Manifest_load_x3f(x_14, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_NameSet_empty;
x_19 = l_Lake_Workspace_updateAndMaterialize(x_9, x_18, x_5, x_8, x_2, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lake_Workspace_materializeDeps(x_9, x_21, x_5, x_6, x_4, x_2, x_20);
lean_dec(x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_io_error_to_string(x_23);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_apply_2(x_2, x_27, x_24);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_4);
x_35 = l_Lean_NameSet_empty;
x_36 = l_Lake_Workspace_updateAndMaterialize(x_9, x_35, x_5, x_8, x_2, x_10);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_1, 7);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 2);
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
lean_object* initialize_Lake_Load_Resolve(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Workspace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Resolve(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InitFacets(builtin, lean_io_mk_world());
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
