// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: public import Lake.Load.Config public import Lake.Config.Workspace import Lake.Load.Resolve import Lake.Load.Package import Lake.Load.Lean.Eval import Lake.Build.InitFacets
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2;
extern lean_object* l_Lake_initFacetConfigs;
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1;
static lean_object* l_Lake_loadWorkspace___closed__0;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_mk_io_user_error(x_4);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_mk_io_user_error(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[root]", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cache", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 11);
x_8 = lean_ctor_get(x_1, 3);
lean_dec(x_8);
x_9 = l_Lean_searchPathRef;
x_10 = l_Lake_Env_leanSearchPath(x_5);
x_11 = lean_st_ref_set(x_9, x_10);
x_12 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
x_13 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_ctor_set(x_1, 3, x_13);
x_14 = l_Lake_loadPackageCore(x_12, x_1, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2;
x_21 = lean_st_mk_ref(x_20);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_18, 6);
x_24 = lean_ctor_get(x_18, 4);
x_25 = lean_ctor_get(x_18, 23);
lean_dec(x_25);
x_26 = lean_ctor_get_uint8(x_23, sizeof(void*)*26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_21);
lean_inc_ref(x_24);
lean_ctor_set(x_18, 23, x_27);
if (x_26 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_5, 7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Lake_defaultLakeDir;
x_49 = l_Lake_joinRelative(x_24, x_48);
x_50 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
x_51 = l_Lake_joinRelative(x_49, x_50);
x_28 = x_51;
goto block_46;
}
else
{
lean_object* x_52; 
lean_dec_ref(x_24);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
x_28 = x_52;
goto block_46;
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_5, 8);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = l_Lake_defaultLakeDir;
x_55 = l_Lake_joinRelative(x_24, x_54);
x_56 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
x_57 = l_Lake_joinRelative(x_55, x_56);
x_28 = x_57;
goto block_46;
}
else
{
lean_object* x_58; 
lean_dec_ref(x_24);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_28 = x_58;
goto block_46;
}
}
block_46:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3;
x_30 = lean_box(1);
x_31 = l_Lake_initFacetConfigs;
x_32 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_5);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_6);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
lean_ctor_set(x_32, 6, x_31);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
lean_dec_ref(x_19);
x_34 = l_Lake_Workspace_addFacetsFromEnv(x_33, x_7, x_32);
lean_dec_ref(x_7);
x_35 = l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
if (lean_is_scalar(x_17)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_17;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec_ref(x_35);
x_39 = lean_io_error_to_string(x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_16);
x_43 = lean_array_push(x_16, x_41);
if (lean_is_scalar(x_17)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_17;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_19);
lean_dec_ref(x_7);
if (lean_is_scalar(x_17)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_17;
}
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_16);
return x_45;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_59 = lean_ctor_get(x_18, 6);
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
x_62 = lean_ctor_get(x_18, 2);
x_63 = lean_ctor_get(x_18, 3);
x_64 = lean_ctor_get(x_18, 4);
x_65 = lean_ctor_get(x_18, 5);
x_66 = lean_ctor_get(x_18, 7);
x_67 = lean_ctor_get(x_18, 8);
x_68 = lean_ctor_get(x_18, 9);
x_69 = lean_ctor_get(x_18, 10);
x_70 = lean_ctor_get(x_18, 11);
x_71 = lean_ctor_get(x_18, 12);
x_72 = lean_ctor_get(x_18, 13);
x_73 = lean_ctor_get(x_18, 14);
x_74 = lean_ctor_get(x_18, 15);
x_75 = lean_ctor_get(x_18, 16);
x_76 = lean_ctor_get(x_18, 17);
x_77 = lean_ctor_get(x_18, 18);
x_78 = lean_ctor_get(x_18, 19);
x_79 = lean_ctor_get(x_18, 20);
x_80 = lean_ctor_get(x_18, 21);
x_81 = lean_ctor_get(x_18, 22);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_59);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
x_82 = lean_ctor_get_uint8(x_59, sizeof(void*)*26);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_21);
lean_inc_ref(x_64);
x_84 = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(x_84, 0, x_60);
lean_ctor_set(x_84, 1, x_61);
lean_ctor_set(x_84, 2, x_62);
lean_ctor_set(x_84, 3, x_63);
lean_ctor_set(x_84, 4, x_64);
lean_ctor_set(x_84, 5, x_65);
lean_ctor_set(x_84, 6, x_59);
lean_ctor_set(x_84, 7, x_66);
lean_ctor_set(x_84, 8, x_67);
lean_ctor_set(x_84, 9, x_68);
lean_ctor_set(x_84, 10, x_69);
lean_ctor_set(x_84, 11, x_70);
lean_ctor_set(x_84, 12, x_71);
lean_ctor_set(x_84, 13, x_72);
lean_ctor_set(x_84, 14, x_73);
lean_ctor_set(x_84, 15, x_74);
lean_ctor_set(x_84, 16, x_75);
lean_ctor_set(x_84, 17, x_76);
lean_ctor_set(x_84, 18, x_77);
lean_ctor_set(x_84, 19, x_78);
lean_ctor_set(x_84, 20, x_79);
lean_ctor_set(x_84, 21, x_80);
lean_ctor_set(x_84, 22, x_81);
lean_ctor_set(x_84, 23, x_83);
if (x_82 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_5, 7);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = l_Lake_defaultLakeDir;
x_106 = l_Lake_joinRelative(x_64, x_105);
x_107 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
x_108 = l_Lake_joinRelative(x_106, x_107);
x_85 = x_108;
goto block_103;
}
else
{
lean_object* x_109; 
lean_dec_ref(x_64);
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
x_85 = x_109;
goto block_103;
}
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_5, 8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = l_Lake_defaultLakeDir;
x_112 = l_Lake_joinRelative(x_64, x_111);
x_113 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
x_114 = l_Lake_joinRelative(x_112, x_113);
x_85 = x_114;
goto block_103;
}
else
{
lean_object* x_115; 
lean_dec_ref(x_64);
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
x_85 = x_115;
goto block_103;
}
}
block_103:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3;
x_87 = lean_box(1);
x_88 = l_Lake_initFacetConfigs;
x_89 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_5);
lean_ctor_set(x_89, 2, x_85);
lean_ctor_set(x_89, 3, x_6);
lean_ctor_set(x_89, 4, x_86);
lean_ctor_set(x_89, 5, x_87);
lean_ctor_set(x_89, 6, x_88);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_19, 0);
lean_inc(x_90);
lean_dec_ref(x_19);
x_91 = l_Lake_Workspace_addFacetsFromEnv(x_90, x_7, x_89);
lean_dec_ref(x_7);
x_92 = l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
if (lean_is_scalar(x_17)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_17;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_16);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec_ref(x_92);
x_96 = lean_io_error_to_string(x_95);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_array_get_size(x_16);
x_100 = lean_array_push(x_16, x_98);
if (lean_is_scalar(x_17)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_17;
 lean_ctor_set_tag(x_101, 1);
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; 
lean_dec(x_19);
lean_dec_ref(x_7);
if (lean_is_scalar(x_17)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_17;
}
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_16);
return x_102;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_116 = !lean_is_exclusive(x_14);
if (x_116 == 0)
{
return x_14;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_14, 0);
x_118 = lean_ctor_get(x_14, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_14);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_120 = lean_ctor_get(x_1, 0);
x_121 = lean_ctor_get(x_1, 1);
x_122 = lean_ctor_get(x_1, 2);
x_123 = lean_ctor_get(x_1, 4);
x_124 = lean_ctor_get(x_1, 5);
x_125 = lean_ctor_get(x_1, 6);
x_126 = lean_ctor_get(x_1, 7);
x_127 = lean_ctor_get(x_1, 8);
x_128 = lean_ctor_get(x_1, 9);
x_129 = lean_ctor_get(x_1, 10);
x_130 = lean_ctor_get(x_1, 11);
x_131 = lean_ctor_get_uint8(x_1, sizeof(void*)*14);
x_132 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 1);
x_133 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 2);
x_134 = lean_ctor_get(x_1, 12);
x_135 = lean_ctor_get(x_1, 13);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_1);
x_136 = l_Lean_searchPathRef;
x_137 = l_Lake_Env_leanSearchPath(x_120);
x_138 = lean_st_ref_set(x_136, x_137);
x_139 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
x_140 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_130);
lean_inc(x_121);
lean_inc_ref(x_120);
x_141 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_121);
lean_ctor_set(x_141, 2, x_122);
lean_ctor_set(x_141, 3, x_140);
lean_ctor_set(x_141, 4, x_123);
lean_ctor_set(x_141, 5, x_124);
lean_ctor_set(x_141, 6, x_125);
lean_ctor_set(x_141, 7, x_126);
lean_ctor_set(x_141, 8, x_127);
lean_ctor_set(x_141, 9, x_128);
lean_ctor_set(x_141, 10, x_129);
lean_ctor_set(x_141, 11, x_130);
lean_ctor_set(x_141, 12, x_134);
lean_ctor_set(x_141, 13, x_135);
lean_ctor_set_uint8(x_141, sizeof(void*)*14, x_131);
lean_ctor_set_uint8(x_141, sizeof(void*)*14 + 1, x_132);
lean_ctor_set_uint8(x_141, sizeof(void*)*14 + 2, x_133);
x_142 = l_Lake_loadPackageCore(x_139, x_141, x_2);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2;
x_149 = lean_st_mk_ref(x_148);
x_150 = lean_ctor_get(x_146, 6);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_146, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_146, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_146, 4);
lean_inc_ref(x_155);
x_156 = lean_ctor_get(x_146, 5);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_146, 7);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_146, 8);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_146, 9);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_146, 10);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_146, 11);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_146, 12);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_146, 13);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_146, 14);
lean_inc(x_164);
x_165 = lean_ctor_get(x_146, 15);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_146, 16);
lean_inc(x_166);
x_167 = lean_ctor_get(x_146, 17);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_146, 18);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_146, 19);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_146, 20);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_146, 21);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_146, 22);
lean_inc(x_172);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 lean_ctor_release(x_146, 6);
 lean_ctor_release(x_146, 7);
 lean_ctor_release(x_146, 8);
 lean_ctor_release(x_146, 9);
 lean_ctor_release(x_146, 10);
 lean_ctor_release(x_146, 11);
 lean_ctor_release(x_146, 12);
 lean_ctor_release(x_146, 13);
 lean_ctor_release(x_146, 14);
 lean_ctor_release(x_146, 15);
 lean_ctor_release(x_146, 16);
 lean_ctor_release(x_146, 17);
 lean_ctor_release(x_146, 18);
 lean_ctor_release(x_146, 19);
 lean_ctor_release(x_146, 20);
 lean_ctor_release(x_146, 21);
 lean_ctor_release(x_146, 22);
 lean_ctor_release(x_146, 23);
 x_173 = x_146;
} else {
 lean_dec_ref(x_146);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get_uint8(x_150, sizeof(void*)*26);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_149);
lean_inc_ref(x_155);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 24, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_151);
lean_ctor_set(x_176, 1, x_152);
lean_ctor_set(x_176, 2, x_153);
lean_ctor_set(x_176, 3, x_154);
lean_ctor_set(x_176, 4, x_155);
lean_ctor_set(x_176, 5, x_156);
lean_ctor_set(x_176, 6, x_150);
lean_ctor_set(x_176, 7, x_157);
lean_ctor_set(x_176, 8, x_158);
lean_ctor_set(x_176, 9, x_159);
lean_ctor_set(x_176, 10, x_160);
lean_ctor_set(x_176, 11, x_161);
lean_ctor_set(x_176, 12, x_162);
lean_ctor_set(x_176, 13, x_163);
lean_ctor_set(x_176, 14, x_164);
lean_ctor_set(x_176, 15, x_165);
lean_ctor_set(x_176, 16, x_166);
lean_ctor_set(x_176, 17, x_167);
lean_ctor_set(x_176, 18, x_168);
lean_ctor_set(x_176, 19, x_169);
lean_ctor_set(x_176, 20, x_170);
lean_ctor_set(x_176, 21, x_171);
lean_ctor_set(x_176, 22, x_172);
lean_ctor_set(x_176, 23, x_175);
if (x_174 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_120, 7);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = l_Lake_defaultLakeDir;
x_198 = l_Lake_joinRelative(x_155, x_197);
x_199 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
x_200 = l_Lake_joinRelative(x_198, x_199);
x_177 = x_200;
goto block_195;
}
else
{
lean_object* x_201; 
lean_dec_ref(x_155);
x_201 = lean_ctor_get(x_196, 0);
lean_inc(x_201);
x_177 = x_201;
goto block_195;
}
}
else
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_120, 8);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = l_Lake_defaultLakeDir;
x_204 = l_Lake_joinRelative(x_155, x_203);
x_205 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
x_206 = l_Lake_joinRelative(x_204, x_205);
x_177 = x_206;
goto block_195;
}
else
{
lean_object* x_207; 
lean_dec_ref(x_155);
x_207 = lean_ctor_get(x_202, 0);
lean_inc(x_207);
x_177 = x_207;
goto block_195;
}
}
block_195:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3;
x_179 = lean_box(1);
x_180 = l_Lake_initFacetConfigs;
x_181 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_120);
lean_ctor_set(x_181, 2, x_177);
lean_ctor_set(x_181, 3, x_121);
lean_ctor_set(x_181, 4, x_178);
lean_ctor_set(x_181, 5, x_179);
lean_ctor_set(x_181, 6, x_180);
if (lean_obj_tag(x_147) == 1)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_147, 0);
lean_inc(x_182);
lean_dec_ref(x_147);
x_183 = l_Lake_Workspace_addFacetsFromEnv(x_182, x_130, x_181);
lean_dec_ref(x_130);
x_184 = l_IO_ofExcept___at___00__private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
if (lean_is_scalar(x_145)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_145;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_144);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
lean_dec_ref(x_184);
x_188 = lean_io_error_to_string(x_187);
x_189 = 3;
x_190 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set_uint8(x_190, sizeof(void*)*1, x_189);
x_191 = lean_array_get_size(x_144);
x_192 = lean_array_push(x_144, x_190);
if (lean_is_scalar(x_145)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_145;
 lean_ctor_set_tag(x_193, 1);
}
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_147);
lean_dec_ref(x_130);
if (lean_is_scalar(x_145)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_145;
}
lean_ctor_set(x_194, 0, x_181);
lean_ctor_set(x_194, 1, x_144);
return x_194;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec_ref(x_130);
lean_dec(x_121);
lean_dec_ref(x_120);
x_208 = lean_ctor_get(x_142, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_142, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_210 = x_142;
} else {
 lean_dec_ref(x_142);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspace___elam__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
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
lean_dec_ref(x_5);
return x_9;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*14);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lake_loadWorkspace___closed__0;
x_15 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; uint8_t x_47; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_46 = lean_array_get_size(x_17);
x_47 = lean_nat_dec_lt(x_13, x_46);
if (x_47 == 0)
{
lean_dec(x_17);
x_18 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(0);
x_49 = lean_nat_dec_le(x_46, x_46);
if (x_49 == 0)
{
if (x_47 == 0)
{
lean_dec(x_17);
x_18 = lean_box(0);
goto block_45;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_46);
lean_inc_ref(x_2);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_17, x_50, x_51, x_48, x_2);
lean_dec(x_17);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_18 = lean_box(0);
goto block_45;
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_46);
lean_inc_ref(x_2);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_17, x_56, x_57, x_48, x_2);
lean_dec(x_17);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_18 = lean_box(0);
goto block_45;
}
else
{
uint8_t x_59; 
lean_dec(x_16);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
block_45:
{
if (x_11 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_19, 4);
x_21 = lean_ctor_get(x_19, 9);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
x_22 = l_Lake_joinRelative(x_20, x_21);
x_23 = l_Lake_Manifest_load_x3f(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lake_Workspace_materializeDeps(x_16, x_25, x_9, x_10, x_8, x_2);
lean_dec_ref(x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec_ref(x_8);
x_27 = l_Lean_NameSet_empty;
x_28 = l_Lake_Workspace_updateAndMaterialize(x_16, x_27, x_9, x_12, x_2);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_io_error_to_string(x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_apply_2(x_2, x_33, lean_box(0));
x_35 = lean_box(0);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_io_error_to_string(x_36);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_apply_2(x_2, x_39, lean_box(0));
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_8);
x_43 = l_Lean_NameSet_empty;
x_44 = l_Lake_Workspace_updateAndMaterialize(x_16, x_43, x_9, x_12, x_2);
return x_44;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_dec_ref(x_15);
x_63 = lean_array_get_size(x_62);
x_64 = lean_nat_dec_lt(x_13, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec_ref(x_2);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_box(0);
x_68 = lean_nat_dec_le(x_63, x_63);
if (x_68 == 0)
{
if (x_64 == 0)
{
lean_dec(x_62);
lean_dec_ref(x_2);
x_4 = lean_box(0);
goto block_7;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_63);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_62, x_69, x_70, x_67, x_2);
lean_dec(x_62);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_4 = lean_box(0);
goto block_7;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_63);
x_77 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_62, x_75, x_76, x_67, x_2);
lean_dec(x_62);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_4 = lean_box(0);
goto block_7;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspace(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lake_loadWorkspace___closed__0;
x_13 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_27 = lean_array_get_size(x_15);
x_28 = lean_nat_dec_lt(x_11, x_27);
if (x_28 == 0)
{
lean_dec(x_15);
x_16 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
if (x_28 == 0)
{
lean_dec(x_15);
x_16 = lean_box(0);
goto block_26;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_inc_ref(x_3);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_15, x_31, x_32, x_29, x_3);
lean_dec(x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_16 = lean_box(0);
goto block_26;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
return x_33;
}
}
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_27);
lean_inc_ref(x_3);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_15, x_34, x_35, x_29, x_3);
lean_dec(x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_dec_ref(x_36);
x_16 = lean_box(0);
goto block_26;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
return x_36;
}
}
}
block_26:
{
lean_object* x_17; 
x_17 = l_Lake_Workspace_updateAndMaterialize(x_14, x_2, x_9, x_10, x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec_ref(x_9);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec_ref(x_13);
x_38 = lean_array_get_size(x_37);
x_39 = lean_nat_dec_lt(x_11, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec_ref(x_3);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_box(0);
x_43 = lean_nat_dec_le(x_38, x_38);
if (x_43 == 0)
{
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_3);
x_5 = lean_box(0);
goto block_8;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_38);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_37, x_44, x_45, x_42, x_3);
lean_dec(x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_5 = lean_box(0);
goto block_8;
}
else
{
return x_46;
}
}
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_38);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_37, x_47, x_48, x_42, x_3);
lean_dec(x_37);
if (lean_obj_tag(x_49) == 0)
{
lean_dec_ref(x_49);
x_5 = lean_box(0);
goto block_8;
}
else
{
return x_49;
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateManifest(x_1, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Load_Resolve(uint8_t builtin);
lean_object* initialize_Lake_Load_Package(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Resolve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4);
l_Lake_loadWorkspace___closed__0 = _init_l_Lake_loadWorkspace___closed__0();
lean_mark_persistent(l_Lake_loadWorkspace___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
