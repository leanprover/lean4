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
static lean_object* l_Lake_loadWorkspaceRoot___closed__0;
lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__6;
lean_object* l_System_FilePath_normalize(lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__1;
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__5;
lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__2;
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_materializeDeps___elam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1(uint8_t, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__0;
lean_object* l_Lake_validateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*, lean_object*);
extern lean_object* l_Lake_initFacetConfigs;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_loadWorkspace___closed__0;
static lean_object* l_Lake_loadWorkspaceRoot___closed__1;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
static lean_object* l_Lake_loadWorkspaceRoot___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__3;
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4;
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_writeManifest(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[root]", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 9);
lean_inc(x_6);
x_7 = l_Lake_loadWorkspaceRoot___closed__0;
x_8 = l_Lake_Env_leanSearchPath(x_4);
x_9 = lean_st_ref_set(x_7, x_8, x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lake_loadWorkspaceRoot___closed__1;
x_12 = l_Lake_loadPackageCore(x_11, x_1, x_2, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lake_loadWorkspaceRoot___closed__2;
x_24 = lean_box(0);
x_25 = l_Lake_initFacetConfigs;
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_6);
lean_ctor_set(x_13, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_12);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lake_Workspace_addFacetsFromEnv(x_27, x_6, x_26);
lean_dec(x_6);
x_29 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_28, x_16);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_13, 0, x_31);
lean_ctor_set(x_29, 0, x_13);
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
lean_ctor_set(x_13, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_13);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_io_error_to_string(x_36);
x_38 = lean_box(3);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
x_41 = lean_array_get_size(x_19);
x_42 = lean_array_push(x_19, x_39);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_42);
lean_ctor_set(x_13, 0, x_41);
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 0, x_13);
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_io_error_to_string(x_43);
x_46 = lean_box(3);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_array_get_size(x_19);
x_50 = lean_array_push(x_19, x_47);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_50);
lean_ctor_set(x_13, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_dec(x_13);
x_53 = lean_ctor_get(x_14, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = l_Lake_loadWorkspaceRoot___closed__2;
x_56 = lean_box(0);
x_57 = l_Lake_initFacetConfigs;
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_4);
lean_ctor_set(x_58, 2, x_5);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
lean_ctor_set(x_58, 5, x_57);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_59; 
lean_dec(x_6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_12, 0, x_59);
return x_12;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_12);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
lean_dec(x_54);
x_61 = l_Lake_Workspace_addFacetsFromEnv(x_60, x_6, x_58);
lean_dec(x_6);
x_62 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_61, x_16);
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
lean_ctor_set(x_66, 1, x_52);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
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
x_72 = lean_box(3);
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
x_74 = lean_unbox(x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_74);
x_75 = lean_array_get_size(x_52);
x_76 = lean_array_push(x_52, x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_70;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_69);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_dec(x_12);
x_80 = lean_ctor_get(x_13, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_81 = x_13;
} else {
 lean_dec_ref(x_13);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_14, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_14, 1);
lean_inc(x_83);
lean_dec(x_14);
x_84 = l_Lake_loadWorkspaceRoot___closed__2;
x_85 = lean_box(0);
x_86 = l_Lake_initFacetConfigs;
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_4);
lean_ctor_set(x_87, 2, x_5);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set(x_87, 4, x_85);
lean_ctor_set(x_87, 5, x_86);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_6);
if (lean_is_scalar(x_81)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_81;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_80);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_79);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_Lake_Workspace_addFacetsFromEnv(x_90, x_6, x_87);
lean_dec(x_6);
x_92 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_91, x_79);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_81;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_80);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_100 = x_92;
} else {
 lean_dec_ref(x_92);
 x_100 = lean_box(0);
}
x_101 = lean_io_error_to_string(x_98);
x_102 = lean_box(3);
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
x_104 = lean_unbox(x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_104);
x_105 = lean_array_get_size(x_80);
x_106 = lean_array_push(x_80, x_103);
if (lean_is_scalar(x_81)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_81;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_100)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_100;
 lean_ctor_set_tag(x_108, 0);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_99);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_12);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_12, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_13);
if (x_111 == 0)
{
return x_12;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_13, 0);
x_113 = lean_ctor_get(x_13, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_13);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_12, 0, x_114);
return x_12;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_12, 1);
lean_inc(x_115);
lean_dec(x_12);
x_116 = lean_ctor_get(x_13, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_13, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_118 = x_13;
} else {
 lean_dec_ref(x_13);
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
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_10);
x_12 = l_Lake_Workspace_writeManifest(x_10, x_11, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_free_object(x_12);
x_21 = lean_box(0);
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
lean_inc(x_10);
x_24 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(x_16, x_22, x_23, x_21, x_10, x_1, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_10);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_10, 3);
lean_inc(x_34);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_36, x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_41 = lean_box(0);
x_42 = 0;
x_43 = lean_usize_of_nat(x_36);
lean_dec(x_36);
lean_inc(x_10);
x_44 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(x_34, x_42, x_43, x_41, x_10, x_1, x_33);
lean_dec(x_34);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_10);
x_52 = lean_ctor_get(x_12, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_io_error_to_string(x_52);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = lean_apply_2(x_1, x_56, x_53);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_7);
if (x_65 == 0)
{
return x_7;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0(x_1, x_3, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing manifest; use `lake update` to generate one", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__1;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lake", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package-overrides.json", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifest out of date: packages directory changed; use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)", 146, 146);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__5;
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_115; lean_object* x_116; uint8_t x_123; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0), 2, 0);
x_11 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__0;
x_123 = l_Array_isEmpty___redArg(x_9);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_2, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 3);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_System_FilePath_normalize(x_126);
x_128 = l_Lake_mkRelPathString(x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10(x_8, x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__6;
lean_inc(x_1);
x_132 = lean_apply_2(x_1, x_131, x_7);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_115 = x_1;
x_116 = x_133;
goto block_122;
}
else
{
x_115 = x_1;
x_116 = x_7;
goto block_122;
}
}
else
{
x_115 = x_1;
x_116 = x_7;
goto block_122;
}
block_27:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = l_Lake_Workspace_addPackage(x_12, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_box(x_17);
x_21 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_box(x_5);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___elam__4___boxed), 15, 10);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_11);
lean_closure_set(x_23, 3, x_11);
lean_closure_set(x_23, 4, x_14);
lean_closure_set(x_23, 5, x_21);
lean_closure_set(x_23, 6, x_21);
lean_closure_set(x_23, 7, x_16);
lean_closure_set(x_23, 8, x_11);
lean_closure_set(x_23, 9, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__3), 7, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(x_24, x_18, x_19, x_25, x_15, x_13);
return x_26;
}
block_47:
{
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = l_Array_isEmpty___redArg(x_29);
lean_dec(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_2);
x_35 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__2;
x_36 = lean_apply_2(x_31, x_35, x_30);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(0);
x_44 = lean_unbox(x_43);
x_12 = x_28;
x_13 = x_30;
x_14 = x_33;
x_15 = x_31;
x_16 = x_32;
x_17 = x_44;
goto block_27;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_29);
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
x_12 = x_28;
x_13 = x_30;
x_14 = x_33;
x_15 = x_31;
x_16 = x_32;
x_17 = x_46;
goto block_27;
}
}
block_61:
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_array_get_size(x_6);
x_56 = lean_nat_dec_lt(x_52, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_10);
x_28 = x_48;
x_29 = x_49;
x_30 = x_50;
x_31 = x_51;
x_32 = x_53;
x_33 = x_54;
goto block_47;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec(x_10);
x_28 = x_48;
x_29 = x_49;
x_30 = x_50;
x_31 = x_51;
x_32 = x_53;
x_33 = x_54;
goto block_47;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_60 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_6, x_58, x_59, x_54);
x_28 = x_48;
x_29 = x_49;
x_30 = x_50;
x_31 = x_51;
x_32 = x_53;
x_33 = x_60;
goto block_47;
}
}
}
block_102:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 9);
lean_inc(x_69);
lean_inc(x_64);
lean_inc(x_66);
x_70 = l_Lake_validateManifest(x_66, x_69, x_64, x_62);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__3;
x_73 = l_Lake_joinRelative(x_68, x_72);
x_74 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4;
x_75 = l_Lake_joinRelative(x_73, x_74);
x_76 = l_Lake_Manifest_tryLoadEntries(x_75, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_lt(x_63, x_79);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_48 = x_67;
x_49 = x_69;
x_50 = x_78;
x_51 = x_64;
x_52 = x_63;
x_53 = x_65;
x_54 = x_66;
goto block_61;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_79, x_79);
if (x_81 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_48 = x_67;
x_49 = x_69;
x_50 = x_78;
x_51 = x_64;
x_52 = x_63;
x_53 = x_65;
x_54 = x_66;
goto block_61;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_79);
lean_dec(x_79);
lean_inc(x_10);
x_84 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_77, x_82, x_83, x_66);
lean_dec(x_77);
x_48 = x_67;
x_49 = x_69;
x_50 = x_78;
x_51 = x_64;
x_52 = x_63;
x_53 = x_65;
x_54 = x_84;
goto block_61;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_85 = lean_ctor_get(x_76, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_io_error_to_string(x_85);
x_88 = lean_box(3);
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = lean_apply_2(x_64, x_89, x_86);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_70);
if (x_98 == 0)
{
return x_70;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_70, 0);
x_100 = lean_ctor_get(x_70, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_70);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_114:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_box(0);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_array_get_size(x_9);
x_109 = lean_nat_dec_lt(x_107, x_108);
if (x_109 == 0)
{
lean_dec(x_108);
lean_dec(x_9);
x_62 = x_103;
x_63 = x_107;
x_64 = x_104;
x_65 = x_105;
x_66 = x_106;
goto block_102;
}
else
{
uint8_t x_110; 
x_110 = lean_nat_dec_le(x_108, x_108);
if (x_110 == 0)
{
lean_dec(x_108);
lean_dec(x_9);
x_62 = x_103;
x_63 = x_107;
x_64 = x_104;
x_65 = x_105;
x_66 = x_106;
goto block_102;
}
else
{
size_t x_111; size_t x_112; lean_object* x_113; 
x_111 = 0;
x_112 = lean_usize_of_nat(x_108);
lean_dec(x_108);
lean_inc(x_10);
x_113 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_9, x_111, x_112, x_106);
lean_dec(x_9);
x_62 = x_103;
x_63 = x_107;
x_64 = x_104;
x_65 = x_105;
x_66 = x_113;
goto block_102;
}
}
}
block_122:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 3);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_120 = l_System_FilePath_normalize(x_119);
x_103 = x_116;
x_104 = x_115;
x_105 = x_120;
goto block_114;
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_8, 0);
lean_inc(x_121);
lean_dec(x_8);
x_103 = x_116;
x_104 = x_115;
x_105 = x_121;
goto block_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
static lean_object* _init_l_Lake_loadWorkspace___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 9);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*12);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*12 + 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*12 + 2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lake_loadWorkspace___closed__0;
x_15 = l_Lake_loadWorkspaceRoot(x_1, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_49; uint8_t x_50; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_49 = lean_array_get_size(x_19);
x_50 = lean_nat_dec_lt(x_13, x_49);
if (x_50 == 0)
{
lean_dec(x_49);
lean_dec(x_19);
x_20 = x_17;
goto block_48;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_49, x_49);
if (x_51 == 0)
{
lean_dec(x_49);
lean_dec(x_19);
x_20 = x_17;
goto block_48;
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_box(0);
x_53 = 0;
x_54 = lean_usize_of_nat(x_49);
lean_dec(x_49);
lean_inc(x_2);
x_55 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_19, x_53, x_54, x_52, x_2, x_17);
lean_dec(x_19);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_20 = x_56;
goto block_48;
}
}
block_48:
{
if (x_11 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 6);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lake_joinRelative(x_22, x_23);
lean_dec(x_23);
x_25 = l_Lake_Manifest_load_x3f(x_24, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_2, x_18, x_28, x_9, x_12, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(x_2, x_18, x_31, x_9, x_10, x_8, x_30);
lean_dec(x_8);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_io_error_to_string(x_33);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_apply_2(x_2, x_37, x_34);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
x_46 = lean_box(0);
x_47 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_2, x_18, x_46, x_9, x_12, x_20);
return x_47;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_15, 1);
x_59 = lean_ctor_get(x_15, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_lt(x_13, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_2);
x_63 = lean_box(0);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_63);
return x_15;
}
else
{
uint8_t x_64; 
lean_free_object(x_15);
x_64 = lean_nat_dec_le(x_61, x_61);
if (x_64 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_2);
x_4 = x_58;
goto block_7;
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_box(0);
x_66 = 0;
x_67 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_68 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_60, x_66, x_67, x_65, x_2, x_58);
lean_dec(x_60);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_4 = x_69;
goto block_7;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
lean_dec(x_15);
x_71 = lean_ctor_get(x_16, 1);
lean_inc(x_71);
lean_dec(x_16);
x_72 = lean_array_get_size(x_71);
x_73 = lean_nat_dec_lt(x_13, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_72, x_72);
if (x_76 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_2);
x_4 = x_70;
goto block_7;
}
else
{
lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_box(0);
x_78 = 0;
x_79 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_80 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_71, x_78, x_79, x_77, x_2, x_70);
lean_dec(x_71);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_4 = x_81;
goto block_7;
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 9);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*12 + 2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lake_loadWorkspace___closed__0;
x_13 = l_Lake_loadWorkspaceRoot(x_1, x_12, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_31; uint8_t x_32; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_31 = lean_array_get_size(x_17);
x_32 = lean_nat_dec_lt(x_11, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_17);
x_18 = x_15;
goto block_30;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_17);
x_18 = x_15;
goto block_30;
}
else
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_box(0);
x_35 = 0;
x_36 = lean_usize_of_nat(x_31);
lean_dec(x_31);
lean_inc(x_3);
x_37 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_17, x_35, x_36, x_34, x_3, x_15);
lean_dec(x_17);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_18 = x_38;
goto block_30;
}
}
block_30:
{
lean_object* x_19; 
x_19 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_3, x_16, x_2, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_13, 1);
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_11, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_3);
x_45 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_45);
return x_13;
}
else
{
uint8_t x_46; 
lean_free_object(x_13);
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_3);
x_5 = x_40;
goto block_8;
}
else
{
lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_box(0);
x_48 = 0;
x_49 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_50 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_42, x_48, x_49, x_47, x_3, x_40);
lean_dec(x_42);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_5 = x_51;
goto block_8;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_dec(x_13);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_dec(x_14);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_lt(x_11, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_3);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_54, x_54);
if (x_58 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_3);
x_5 = x_52;
goto block_8;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_62 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_53, x_60, x_61, x_59, x_3, x_52);
lean_dec(x_53);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_5 = x_63;
goto block_8;
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
l_Lake_loadWorkspaceRoot___closed__0 = _init_l_Lake_loadWorkspaceRoot___closed__0();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__0);
l_Lake_loadWorkspaceRoot___closed__1 = _init_l_Lake_loadWorkspaceRoot___closed__1();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__1);
l_Lake_loadWorkspaceRoot___closed__2 = _init_l_Lake_loadWorkspaceRoot___closed__2();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__2);
l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__0 = _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__0();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__0);
l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__1 = _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__1();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__1);
l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__2 = _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__2();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__2);
l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__3 = _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__3();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__3);
l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4 = _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4);
l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__5 = _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__5();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__5);
l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__6 = _init_l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__6();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__6);
l_Lake_loadWorkspace___closed__0 = _init_l_Lake_loadWorkspace___closed__0();
lean_mark_persistent(l_Lake_loadWorkspace___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
