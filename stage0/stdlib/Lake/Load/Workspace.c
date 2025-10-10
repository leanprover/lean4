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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspace___closed__1;
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2;
extern lean_object* l_Lake_initFacetConfigs;
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1;
static lean_object* l_Lake_loadWorkspace___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__5;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_mk_io_user_error(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[root]", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initFacetConfigs;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLakeDir;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cache", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 10);
lean_inc(x_6);
x_7 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
x_8 = l_Lake_Env_leanSearchPath(x_4);
x_9 = lean_st_ref_set(x_7, x_8, x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1;
x_12 = l_Lake_loadPackageCore(x_11, x_1, x_2, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6;
x_21 = lean_st_mk_ref(x_20, x_15);
x_22 = lean_ctor_get(x_18, 4);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_18, 2);
x_28 = lean_ctor_get(x_18, 21);
lean_dec(x_28);
x_29 = lean_ctor_get(x_18, 4);
lean_dec(x_29);
x_30 = lean_ctor_get_uint8(x_22, sizeof(void*)*26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_23);
lean_inc_ref(x_27);
lean_ctor_set(x_18, 21, x_31);
if (x_30 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_4, 6);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_58 = l_Lake_joinRelative(x_27, x_57);
x_59 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_60 = l_Lake_joinRelative(x_58, x_59);
x_32 = x_60;
goto block_55;
}
else
{
lean_object* x_61; 
lean_dec_ref(x_27);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_32 = x_61;
goto block_55;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_4, 7);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_64 = l_Lake_joinRelative(x_27, x_63);
x_65 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_66 = l_Lake_joinRelative(x_64, x_65);
x_32 = x_66;
goto block_55;
}
else
{
lean_object* x_67; 
lean_dec_ref(x_27);
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_32 = x_67;
goto block_55;
}
}
block_55:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_34 = lean_box(1);
x_35 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_36 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_5);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_34);
lean_ctor_set(x_36, 6, x_35);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
if (lean_is_scalar(x_17)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_17;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
if (lean_is_scalar(x_25)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_25;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
lean_inc(x_39);
lean_dec_ref(x_19);
x_40 = l_Lake_Workspace_addFacetsFromEnv(x_39, x_6, x_36);
lean_dec(x_6);
x_41 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_40, x_24);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
if (lean_is_scalar(x_17)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_17;
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_16);
if (lean_is_scalar(x_25)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_25;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec_ref(x_41);
x_48 = lean_io_error_to_string(x_46);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_16);
x_52 = lean_array_push(x_16, x_50);
if (lean_is_scalar(x_17)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_17;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_25)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_25;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
x_70 = lean_ctor_get(x_18, 2);
x_71 = lean_ctor_get(x_18, 3);
x_72 = lean_ctor_get(x_18, 5);
x_73 = lean_ctor_get(x_18, 6);
x_74 = lean_ctor_get(x_18, 7);
x_75 = lean_ctor_get(x_18, 8);
x_76 = lean_ctor_get(x_18, 9);
x_77 = lean_ctor_get(x_18, 10);
x_78 = lean_ctor_get(x_18, 11);
x_79 = lean_ctor_get(x_18, 12);
x_80 = lean_ctor_get(x_18, 13);
x_81 = lean_ctor_get(x_18, 14);
x_82 = lean_ctor_get(x_18, 15);
x_83 = lean_ctor_get(x_18, 16);
x_84 = lean_ctor_get(x_18, 17);
x_85 = lean_ctor_get(x_18, 18);
x_86 = lean_ctor_get(x_18, 19);
x_87 = lean_ctor_get(x_18, 20);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
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
lean_dec(x_18);
x_88 = lean_ctor_get_uint8(x_22, sizeof(void*)*26);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_23);
lean_inc_ref(x_70);
x_90 = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(x_90, 0, x_68);
lean_ctor_set(x_90, 1, x_69);
lean_ctor_set(x_90, 2, x_70);
lean_ctor_set(x_90, 3, x_71);
lean_ctor_set(x_90, 4, x_22);
lean_ctor_set(x_90, 5, x_72);
lean_ctor_set(x_90, 6, x_73);
lean_ctor_set(x_90, 7, x_74);
lean_ctor_set(x_90, 8, x_75);
lean_ctor_set(x_90, 9, x_76);
lean_ctor_set(x_90, 10, x_77);
lean_ctor_set(x_90, 11, x_78);
lean_ctor_set(x_90, 12, x_79);
lean_ctor_set(x_90, 13, x_80);
lean_ctor_set(x_90, 14, x_81);
lean_ctor_set(x_90, 15, x_82);
lean_ctor_set(x_90, 16, x_83);
lean_ctor_set(x_90, 17, x_84);
lean_ctor_set(x_90, 18, x_85);
lean_ctor_set(x_90, 19, x_86);
lean_ctor_set(x_90, 20, x_87);
lean_ctor_set(x_90, 21, x_89);
if (x_88 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_4, 6);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_117 = l_Lake_joinRelative(x_70, x_116);
x_118 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_119 = l_Lake_joinRelative(x_117, x_118);
x_91 = x_119;
goto block_114;
}
else
{
lean_object* x_120; 
lean_dec_ref(x_70);
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
x_91 = x_120;
goto block_114;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_4, 7);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_123 = l_Lake_joinRelative(x_70, x_122);
x_124 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_125 = l_Lake_joinRelative(x_123, x_124);
x_91 = x_125;
goto block_114;
}
else
{
lean_object* x_126; 
lean_dec_ref(x_70);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
x_91 = x_126;
goto block_114;
}
}
block_114:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_93 = lean_box(1);
x_94 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_95 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_4);
lean_ctor_set(x_95, 2, x_91);
lean_ctor_set(x_95, 3, x_5);
lean_ctor_set(x_95, 4, x_92);
lean_ctor_set(x_95, 5, x_93);
lean_ctor_set(x_95, 6, x_94);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_6);
if (lean_is_scalar(x_17)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_17;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_16);
if (lean_is_scalar(x_25)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_25;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_24);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_19, 0);
lean_inc(x_98);
lean_dec_ref(x_19);
x_99 = l_Lake_Workspace_addFacetsFromEnv(x_98, x_6, x_95);
lean_dec(x_6);
x_100 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_99, x_24);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
if (lean_is_scalar(x_17)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_17;
}
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_16);
if (lean_is_scalar(x_25)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_25;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_dec_ref(x_100);
x_107 = lean_io_error_to_string(x_105);
x_108 = 3;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_110 = lean_array_get_size(x_16);
x_111 = lean_array_push(x_16, x_109);
if (lean_is_scalar(x_17)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_17;
 lean_ctor_set_tag(x_112, 1);
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_25)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_25;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
return x_113;
}
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_127 = !lean_is_exclusive(x_12);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_12, 0);
lean_dec(x_128);
x_129 = !lean_is_exclusive(x_13);
if (x_129 == 0)
{
return x_12;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_13, 0);
x_131 = lean_ctor_get(x_13, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_13);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_12, 0, x_132);
return x_12;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_12, 1);
lean_inc(x_133);
lean_dec(x_12);
x_134 = lean_ctor_get(x_13, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_13, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_136 = x_13;
} else {
 lean_dec_ref(x_13);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
return x_138;
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(x_5, x_8, x_6);
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
static lean_object* _init_l_Lake_loadWorkspace___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadWorkspace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 10);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*13);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*13 + 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*13 + 2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lake_loadWorkspace___closed__0;
x_15 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(x_1, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_54; uint8_t x_55; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_54 = lean_array_get_size(x_19);
x_55 = lean_nat_dec_lt(x_13, x_54);
if (x_55 == 0)
{
lean_dec(x_54);
lean_dec(x_19);
x_20 = x_17;
goto block_53;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_54, x_54);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec(x_19);
x_20 = x_17;
goto block_53;
}
else
{
lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_box(0);
x_58 = 0;
x_59 = lean_usize_of_nat(x_54);
lean_dec(x_54);
lean_inc_ref(x_2);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_19, x_58, x_59, x_57, x_2, x_17);
lean_dec(x_19);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
x_20 = x_61;
goto block_53;
}
}
block_53:
{
if (x_11 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_21, 2);
x_23 = lean_ctor_get(x_21, 7);
lean_inc_ref(x_22);
x_24 = l_Lake_joinRelative(x_22, x_23);
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
x_28 = l_Lake_loadWorkspace___closed__1;
x_29 = l_Lake_Workspace_updateAndMaterialize(x_18, x_28, x_9, x_12, x_2, x_27);
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
lean_dec_ref(x_26);
x_32 = l_Lake_Workspace_materializeDeps(x_18, x_31, x_9, x_10, x_8, x_2, x_30);
lean_dec_ref(x_8);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
x_36 = lean_io_error_to_string(x_34);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_apply_2(x_2, x_38, x_35);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_box(0);
lean_ctor_set(x_25, 1, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_io_error_to_string(x_42);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_apply_2(x_2, x_46, x_43);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_8);
x_51 = l_Lake_loadWorkspace___closed__1;
x_52 = l_Lake_Workspace_updateAndMaterialize(x_18, x_51, x_9, x_12, x_2, x_20);
return x_52;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_dec_ref(x_15);
x_63 = !lean_is_exclusive(x_16);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_16, 1);
x_65 = lean_ctor_get(x_16, 0);
lean_dec(x_65);
x_66 = lean_array_get_size(x_64);
x_67 = lean_nat_dec_lt(x_13, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec_ref(x_2);
x_68 = lean_box(0);
lean_ctor_set(x_16, 1, x_62);
lean_ctor_set(x_16, 0, x_68);
return x_16;
}
else
{
uint8_t x_69; 
lean_free_object(x_16);
x_69 = lean_nat_dec_le(x_66, x_66);
if (x_69 == 0)
{
lean_dec(x_66);
lean_dec(x_64);
lean_dec_ref(x_2);
x_4 = x_62;
goto block_7;
}
else
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = 0;
x_72 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_73 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_64, x_71, x_72, x_70, x_2, x_62);
lean_dec(x_64);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_4 = x_74;
goto block_7;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_16, 1);
lean_inc(x_75);
lean_dec(x_16);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_13, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_2);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_62);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_76, x_76);
if (x_80 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_2);
x_4 = x_62;
goto block_7;
}
else
{
lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_75, x_82, x_83, x_81, x_2, x_62);
lean_dec(x_75);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec_ref(x_84);
x_4 = x_85;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 10);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*13 + 2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lake_loadWorkspace___closed__0;
x_13 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(x_1, x_12, x_4);
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
lean_dec_ref(x_14);
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
lean_inc_ref(x_3);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_17, x_35, x_36, x_34, x_3, x_15);
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
x_19 = l_Lake_Workspace_updateAndMaterialize(x_16, x_2, x_9, x_10, x_3, x_18);
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
lean_object* x_39; uint8_t x_40; 
lean_dec(x_9);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_dec_ref(x_13);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_14, 1);
x_42 = lean_ctor_get(x_14, 0);
lean_dec(x_42);
x_43 = lean_array_get_size(x_41);
x_44 = lean_nat_dec_lt(x_11, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec_ref(x_3);
x_45 = lean_box(0);
lean_ctor_set(x_14, 1, x_39);
lean_ctor_set(x_14, 0, x_45);
return x_14;
}
else
{
uint8_t x_46; 
lean_free_object(x_14);
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
lean_dec(x_43);
lean_dec(x_41);
lean_dec_ref(x_3);
x_5 = x_39;
goto block_8;
}
else
{
lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_box(0);
x_48 = 0;
x_49 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_41, x_48, x_49, x_47, x_3, x_39);
lean_dec(x_41);
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
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_dec(x_14);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_11, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_3);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_39);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_53, x_53);
if (x_57 == 0)
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_3);
x_5 = x_39;
goto block_8;
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_box(0);
x_59 = 0;
x_60 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_52, x_59, x_60, x_58, x_3, x_39);
lean_dec(x_52);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_5 = x_62;
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
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateManifest(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Resolve(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Workspace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Resolve(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InitFacets(builtin, lean_io_mk_world());
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
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__5 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__5();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__5);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9);
l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10 = _init_l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10();
lean_mark_persistent(l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10);
l_Lake_loadWorkspace___closed__0 = _init_l_Lake_loadWorkspace___closed__0();
lean_mark_persistent(l_Lake_loadWorkspace___closed__0);
l_Lake_loadWorkspace___closed__1 = _init_l_Lake_loadWorkspace___closed__1();
lean_mark_persistent(l_Lake_loadWorkspace___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
