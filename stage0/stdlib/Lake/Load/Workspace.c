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
lean_object* l_Lake_Workspace_materializeDeps___elam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
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
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lake_Workspace_materializeDeps_spec__10(lean_object*, lean_object*);
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
static lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4;
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_writeManifest(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_loadInputsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 9);
lean_inc(x_6);
x_7 = l_Lake_loadWorkspaceRoot___closed__0;
x_8 = l_Lake_Env_leanSearchPath(x_4);
x_9 = lean_st_ref_set(x_7, x_8, x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lake_loadWorkspaceRoot___closed__1;
x_12 = l_Lake_loadPackageCore(x_11, x_1, x_2, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
lean_inc_ref(x_4);
x_19 = l_Lake_Package_loadInputsFrom(x_4, x_17, x_16, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
x_27 = l_Lake_loadWorkspaceRoot___closed__2;
x_28 = lean_box(0);
x_29 = l_Lake_initFacetConfigs;
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_5);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_28);
lean_ctor_set(x_30, 5, x_29);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_6);
lean_ctor_set(x_20, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_19);
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l_Lake_Workspace_addFacetsFromEnv(x_31, x_6, x_30);
lean_dec(x_6);
x_33 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_32, x_22);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_20, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_io_error_to_string(x_40);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_get_size(x_26);
x_45 = lean_array_push(x_26, x_43);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_45);
lean_ctor_set(x_20, 0, x_44);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_io_error_to_string(x_46);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_26);
x_52 = lean_array_push(x_26, x_50);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_52);
lean_ctor_set(x_20, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_20);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_20, 0);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_20);
x_56 = l_Lake_loadWorkspaceRoot___closed__2;
x_57 = lean_box(0);
x_58 = l_Lake_initFacetConfigs;
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_5);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
lean_ctor_set(x_59, 5, x_58);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_60; 
lean_dec(x_6);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_19, 0, x_60);
return x_19;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_19);
x_61 = lean_ctor_get(x_18, 0);
lean_inc(x_61);
lean_dec(x_18);
x_62 = l_Lake_Workspace_addFacetsFromEnv(x_61, x_6, x_59);
lean_dec(x_6);
x_63 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_62, x_22);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_55);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
x_72 = lean_io_error_to_string(x_69);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_55);
x_76 = lean_array_push(x_55, x_74);
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
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_19, 1);
lean_inc(x_79);
lean_dec(x_19);
x_80 = lean_ctor_get(x_20, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_20, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_82 = x_20;
} else {
 lean_dec_ref(x_20);
 x_82 = lean_box(0);
}
x_83 = l_Lake_loadWorkspaceRoot___closed__2;
x_84 = lean_box(0);
x_85 = l_Lake_initFacetConfigs;
x_86 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_4);
lean_ctor_set(x_86, 2, x_5);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_84);
lean_ctor_set(x_86, 5, x_85);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_6);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_79);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_18, 0);
lean_inc(x_89);
lean_dec(x_18);
x_90 = l_Lake_Workspace_addFacetsFromEnv(x_89, x_6, x_86);
lean_dec(x_6);
x_91 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_90, x_79);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_82;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_81);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
x_100 = lean_io_error_to_string(x_97);
x_101 = 3;
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_101);
x_103 = lean_array_get_size(x_81);
x_104 = lean_array_push(x_81, x_102);
if (lean_is_scalar(x_82)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_82;
 lean_ctor_set_tag(x_105, 1);
}
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_99)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_99;
 lean_ctor_set_tag(x_106, 0);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_98);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_107 = !lean_is_exclusive(x_19);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_19, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_20);
if (x_109 == 0)
{
return x_19;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_20, 0);
x_111 = lean_ctor_get(x_20, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_20);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_19, 0, x_112);
return x_19;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_19, 1);
lean_inc(x_113);
lean_dec(x_19);
x_114 = lean_ctor_get(x_20, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_20, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_116 = x_20;
} else {
 lean_dec_ref(x_20);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_119 = !lean_is_exclusive(x_12);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_12, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_13);
if (x_121 == 0)
{
return x_12;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_13, 0);
x_123 = lean_ctor_get(x_13, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_13);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_12, 0, x_124);
return x_12;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_12, 1);
lean_inc(x_125);
lean_dec(x_12);
x_126 = lean_ctor_get(x_13, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_13, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_128 = x_13;
} else {
 lean_dec_ref(x_13);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
return x_130;
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
lean_dec_ref(x_7);
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
lean_inc_ref(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec_ref(x_16);
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
lean_dec_ref(x_16);
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
lean_dec_ref(x_16);
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
lean_inc_ref(x_34);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec_ref(x_34);
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
lean_dec_ref(x_34);
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
lean_dec_ref(x_34);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_10);
x_52 = lean_ctor_get(x_12, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec_ref(x_12);
x_54 = lean_io_error_to_string(x_52);
x_55 = 3;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_apply_2(x_1, x_56, x_53);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_7);
if (x_64 == 0)
{
return x_7;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_7, 0);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_7);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__1;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__5;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_112; lean_object* x_113; uint8_t x_120; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_9);
lean_dec_ref(x_3);
x_10 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0), 2, 0);
x_11 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__0;
x_120 = l_Array_isEmpty___redArg(x_9);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_121 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_121, 3);
lean_inc_ref(x_122);
lean_dec_ref(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc_ref(x_123);
lean_dec_ref(x_122);
x_124 = l_System_FilePath_normalize(x_123);
x_125 = l_Lake_mkRelPathString(x_124);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lake_Workspace_materializeDeps_spec__10(x_8, x_126);
lean_dec_ref(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__6;
lean_inc(x_1);
x_129 = lean_apply_2(x_1, x_128, x_7);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec_ref(x_129);
x_112 = x_1;
x_113 = x_130;
goto block_119;
}
else
{
x_112 = x_1;
x_113 = x_7;
goto block_119;
}
}
else
{
x_112 = x_1;
x_113 = x_7;
goto block_119;
}
block_27:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = l_Lake_Workspace_addPackage(x_12, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_box(x_17);
x_21 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_box(x_5);
lean_inc_ref(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___elam__2___boxed), 13, 8);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_16);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_11);
lean_closure_set(x_23, 7, x_11);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__3), 7, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(x_24, x_18, x_19, x_25, x_13, x_15);
return x_26;
}
block_45:
{
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = l_Array_isEmpty___redArg(x_29);
lean_dec_ref(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec_ref(x_32);
lean_dec_ref(x_28);
lean_dec(x_4);
lean_dec_ref(x_2);
x_35 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__2;
x_36 = lean_apply_2(x_30, x_35, x_31);
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
uint8_t x_43; 
x_43 = 0;
x_12 = x_28;
x_13 = x_30;
x_14 = x_33;
x_15 = x_31;
x_16 = x_32;
x_17 = x_43;
goto block_27;
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_29);
x_44 = 0;
x_12 = x_28;
x_13 = x_30;
x_14 = x_33;
x_15 = x_31;
x_16 = x_32;
x_17 = x_44;
goto block_27;
}
}
block_59:
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_array_get_size(x_6);
x_54 = lean_nat_dec_lt(x_47, x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec_ref(x_10);
x_28 = x_46;
x_29 = x_48;
x_30 = x_49;
x_31 = x_50;
x_32 = x_51;
x_33 = x_52;
goto block_45;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_53, x_53);
if (x_55 == 0)
{
lean_dec(x_53);
lean_dec_ref(x_10);
x_28 = x_46;
x_29 = x_48;
x_30 = x_49;
x_31 = x_50;
x_32 = x_51;
x_33 = x_52;
goto block_45;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_58 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_6, x_56, x_57, x_52);
x_28 = x_46;
x_29 = x_48;
x_30 = x_49;
x_31 = x_50;
x_32 = x_51;
x_33 = x_58;
goto block_45;
}
}
}
block_99:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_65, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 9);
lean_inc_ref(x_67);
lean_inc(x_62);
lean_inc(x_64);
x_68 = l_Lake_validateManifest(x_64, x_67, x_62, x_61);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__3;
x_71 = l_Lake_joinRelative(x_66, x_70);
x_72 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___closed__4;
x_73 = l_Lake_joinRelative(x_71, x_72);
x_74 = l_Lake_Manifest_tryLoadEntries(x_73, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_array_get_size(x_75);
x_78 = lean_nat_dec_lt(x_60, x_77);
if (x_78 == 0)
{
lean_dec(x_77);
lean_dec(x_75);
x_46 = x_65;
x_47 = x_60;
x_48 = x_67;
x_49 = x_62;
x_50 = x_76;
x_51 = x_63;
x_52 = x_64;
goto block_59;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_77, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
lean_dec(x_75);
x_46 = x_65;
x_47 = x_60;
x_48 = x_67;
x_49 = x_62;
x_50 = x_76;
x_51 = x_63;
x_52 = x_64;
goto block_59;
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_77);
lean_dec(x_77);
lean_inc_ref(x_10);
x_82 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_75, x_80, x_81, x_64);
lean_dec(x_75);
x_46 = x_65;
x_47 = x_60;
x_48 = x_67;
x_49 = x_62;
x_50 = x_76;
x_51 = x_63;
x_52 = x_82;
goto block_59;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec_ref(x_67);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
x_83 = lean_ctor_get(x_74, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_dec_ref(x_74);
x_85 = lean_io_error_to_string(x_83);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_apply_2(x_62, x_87, x_84);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
x_91 = lean_box(0);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
x_95 = !lean_is_exclusive(x_68);
if (x_95 == 0)
{
return x_68;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_68, 0);
x_97 = lean_ctor_get(x_68, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_68);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
block_111:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_box(0);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_array_get_size(x_9);
x_106 = lean_nat_dec_lt(x_104, x_105);
if (x_106 == 0)
{
lean_dec(x_105);
lean_dec_ref(x_9);
x_60 = x_104;
x_61 = x_100;
x_62 = x_101;
x_63 = x_102;
x_64 = x_103;
goto block_99;
}
else
{
uint8_t x_107; 
x_107 = lean_nat_dec_le(x_105, x_105);
if (x_107 == 0)
{
lean_dec(x_105);
lean_dec_ref(x_9);
x_60 = x_104;
x_61 = x_100;
x_62 = x_101;
x_63 = x_102;
x_64 = x_103;
goto block_99;
}
else
{
size_t x_108; size_t x_109; lean_object* x_110; 
x_108 = 0;
x_109 = lean_usize_of_nat(x_105);
lean_dec(x_105);
lean_inc_ref(x_10);
x_110 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_9, x_108, x_109, x_103);
lean_dec_ref(x_9);
x_60 = x_104;
x_61 = x_100;
x_62 = x_101;
x_63 = x_102;
x_64 = x_110;
goto block_99;
}
}
}
block_119:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_114, 3);
lean_inc_ref(x_115);
lean_dec_ref(x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc_ref(x_116);
lean_dec_ref(x_115);
x_117 = l_System_FilePath_normalize(x_116);
x_100 = x_113;
x_101 = x_112;
x_102 = x_117;
goto block_111;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_8, 0);
lean_inc(x_118);
lean_dec(x_8);
x_100 = x_113;
x_101 = x_112;
x_102 = x_118;
goto block_111;
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
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(x_5, x_8, x_6);
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
lean_inc_ref(x_8);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_48; uint8_t x_49; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_48 = lean_array_get_size(x_19);
x_49 = lean_nat_dec_lt(x_13, x_48);
if (x_49 == 0)
{
lean_dec(x_48);
lean_dec(x_19);
x_20 = x_17;
goto block_47;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_48, x_48);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_19);
x_20 = x_17;
goto block_47;
}
else
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_box(0);
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
lean_dec(x_48);
lean_inc(x_2);
x_54 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_19, x_52, x_53, x_51, x_2, x_17);
lean_dec(x_19);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_20 = x_55;
goto block_47;
}
}
block_47:
{
if (x_11 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 6);
lean_inc_ref(x_23);
lean_dec_ref(x_21);
x_24 = l_Lake_joinRelative(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l_Lake_Manifest_load_x3f(x_24, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_8);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_box(0);
x_29 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_2, x_18, x_28, x_9, x_12, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec_ref(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(x_2, x_18, x_31, x_9, x_10, x_8, x_30);
lean_dec_ref(x_8);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec_ref(x_25);
x_35 = lean_io_error_to_string(x_33);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_apply_2(x_2, x_37, x_34);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_8);
x_45 = lean_box(0);
x_46 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_2, x_18, x_45, x_9, x_12, x_20);
return x_46;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_15, 1);
x_58 = lean_ctor_get(x_15, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_dec(x_16);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_lt(x_13, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_62 = lean_box(0);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_62);
return x_15;
}
else
{
uint8_t x_63; 
lean_free_object(x_15);
x_63 = lean_nat_dec_le(x_60, x_60);
if (x_63 == 0)
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_4 = x_57;
goto block_7;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_67 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_59, x_65, x_66, x_64, x_2, x_57);
lean_dec(x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_4 = x_68;
goto block_7;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
lean_dec(x_15);
x_70 = lean_ctor_get(x_16, 1);
lean_inc(x_70);
lean_dec(x_16);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_13, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_2);
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
lean_dec(x_2);
x_4 = x_69;
goto block_7;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_79 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_70, x_77, x_78, x_76, x_2, x_69);
lean_dec(x_70);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_4 = x_80;
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
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__1(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2(x_1, x_2, x_3, x_4);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_13);
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
lean_dec_ref(x_37);
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
lean_dec_ref(x_50);
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
lean_dec_ref(x_62);
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
