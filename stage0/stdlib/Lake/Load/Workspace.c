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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
static lean_object* l_Lake_loadWorkspace___closed__1;
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__2;
extern lean_object* l_Lake_initFacetConfigs;
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1;
static lean_object* l_Lake_loadWorkspace___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__4;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__5;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_2);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 10);
lean_inc(x_6);
x_7 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
x_8 = l_Lake_Env_leanSearchPath(x_4);
x_9 = lean_st_ref_set(x_7, x_8);
x_10 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__1;
x_11 = l_Lake_loadPackageCore(x_10, x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6;
x_18 = lean_st_mk_ref(x_17);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_15, 4);
x_21 = lean_ctor_get(x_15, 2);
x_22 = lean_ctor_get(x_15, 21);
lean_dec(x_22);
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*26);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
lean_inc_ref(x_21);
lean_ctor_set(x_15, 21, x_24);
if (x_23 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_4, 6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_46 = l_Lake_joinRelative(x_21, x_45);
x_47 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_48 = l_Lake_joinRelative(x_46, x_47);
x_25 = x_48;
goto block_43;
}
else
{
lean_object* x_49; 
lean_dec_ref(x_21);
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
x_25 = x_49;
goto block_43;
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_4, 7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_52 = l_Lake_joinRelative(x_21, x_51);
x_53 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_54 = l_Lake_joinRelative(x_52, x_53);
x_25 = x_54;
goto block_43;
}
else
{
lean_object* x_55; 
lean_dec_ref(x_21);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_25 = x_55;
goto block_43;
}
}
block_43:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_27 = lean_box(1);
x_28 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_5);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; 
lean_dec(x_6);
if (lean_is_scalar(x_14)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_14;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec_ref(x_16);
x_32 = l_Lake_Workspace_addFacetsFromEnv(x_31, x_6, x_29);
lean_dec(x_6);
x_33 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_is_scalar(x_14)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_14;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_13);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_io_error_to_string(x_36);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_13);
x_41 = lean_array_push(x_13, x_39);
if (lean_is_scalar(x_14)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_14;
 lean_ctor_set_tag(x_42, 1);
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_56 = lean_ctor_get(x_15, 4);
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_ctor_get(x_15, 1);
x_59 = lean_ctor_get(x_15, 2);
x_60 = lean_ctor_get(x_15, 3);
x_61 = lean_ctor_get(x_15, 5);
x_62 = lean_ctor_get(x_15, 6);
x_63 = lean_ctor_get(x_15, 7);
x_64 = lean_ctor_get(x_15, 8);
x_65 = lean_ctor_get(x_15, 9);
x_66 = lean_ctor_get(x_15, 10);
x_67 = lean_ctor_get(x_15, 11);
x_68 = lean_ctor_get(x_15, 12);
x_69 = lean_ctor_get(x_15, 13);
x_70 = lean_ctor_get(x_15, 14);
x_71 = lean_ctor_get(x_15, 15);
x_72 = lean_ctor_get(x_15, 16);
x_73 = lean_ctor_get(x_15, 17);
x_74 = lean_ctor_get(x_15, 18);
x_75 = lean_ctor_get(x_15, 19);
x_76 = lean_ctor_get(x_15, 20);
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
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_56);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_15);
x_77 = lean_ctor_get_uint8(x_56, sizeof(void*)*26);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_18);
lean_inc_ref(x_59);
x_79 = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(x_79, 0, x_57);
lean_ctor_set(x_79, 1, x_58);
lean_ctor_set(x_79, 2, x_59);
lean_ctor_set(x_79, 3, x_60);
lean_ctor_set(x_79, 4, x_56);
lean_ctor_set(x_79, 5, x_61);
lean_ctor_set(x_79, 6, x_62);
lean_ctor_set(x_79, 7, x_63);
lean_ctor_set(x_79, 8, x_64);
lean_ctor_set(x_79, 9, x_65);
lean_ctor_set(x_79, 10, x_66);
lean_ctor_set(x_79, 11, x_67);
lean_ctor_set(x_79, 12, x_68);
lean_ctor_set(x_79, 13, x_69);
lean_ctor_set(x_79, 14, x_70);
lean_ctor_set(x_79, 15, x_71);
lean_ctor_set(x_79, 16, x_72);
lean_ctor_set(x_79, 17, x_73);
lean_ctor_set(x_79, 18, x_74);
lean_ctor_set(x_79, 19, x_75);
lean_ctor_set(x_79, 20, x_76);
lean_ctor_set(x_79, 21, x_78);
if (x_77 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_4, 6);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_101 = l_Lake_joinRelative(x_59, x_100);
x_102 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_103 = l_Lake_joinRelative(x_101, x_102);
x_80 = x_103;
goto block_98;
}
else
{
lean_object* x_104; 
lean_dec_ref(x_59);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_80 = x_104;
goto block_98;
}
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_4, 7);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__9;
x_107 = l_Lake_joinRelative(x_59, x_106);
x_108 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__10;
x_109 = l_Lake_joinRelative(x_107, x_108);
x_80 = x_109;
goto block_98;
}
else
{
lean_object* x_110; 
lean_dec_ref(x_59);
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_80 = x_110;
goto block_98;
}
}
block_98:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_82 = lean_box(1);
x_83 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_84 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_4);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_5);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_84, 5, x_82);
lean_ctor_set(x_84, 6, x_83);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_85; 
lean_dec(x_6);
if (lean_is_scalar(x_14)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_14;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_13);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_16, 0);
lean_inc(x_86);
lean_dec_ref(x_16);
x_87 = l_Lake_Workspace_addFacetsFromEnv(x_86, x_6, x_84);
lean_dec(x_6);
x_88 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
if (lean_is_scalar(x_14)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_14;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_13);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec_ref(x_88);
x_92 = lean_io_error_to_string(x_91);
x_93 = 3;
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
x_95 = lean_array_get_size(x_13);
x_96 = lean_array_push(x_13, x_94);
if (lean_is_scalar(x_14)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_14;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_111 = !lean_is_exclusive(x_11);
if (x_111 == 0)
{
return x_11;
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
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0(x_1, x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(x_5, x_8);
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
lean_object* x_14; 
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 10);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*13);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*13 + 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*13 + 2);
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
lean_dec(x_46);
lean_dec(x_17);
x_18 = lean_box(0);
goto block_45;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_17);
x_18 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_49 = lean_box(0);
x_50 = 0;
x_51 = lean_usize_of_nat(x_46);
lean_dec(x_46);
lean_inc_ref(x_2);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_17, x_50, x_51, x_49, x_2);
lean_dec(x_17);
lean_dec_ref(x_52);
x_18 = lean_box(0);
goto block_45;
}
}
block_45:
{
if (x_11 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_19, 2);
x_21 = lean_ctor_get(x_19, 7);
lean_inc_ref(x_20);
x_22 = l_Lake_joinRelative(x_20, x_21);
x_23 = l_Lake_Manifest_load_x3f(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_8);
x_25 = l_Lake_loadWorkspace___closed__1;
x_26 = l_Lake_Workspace_updateAndMaterialize(x_16, x_25, x_9, x_12, x_2);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = l_Lake_Workspace_materializeDeps(x_16, x_27, x_9, x_10, x_8, x_2);
lean_dec_ref(x_8);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_9);
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
x_43 = l_Lake_loadWorkspace___closed__1;
x_44 = l_Lake_Workspace_updateAndMaterialize(x_16, x_43, x_9, x_12, x_2);
return x_44;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
lean_dec_ref(x_15);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_lt(x_13, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
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
lean_dec_ref(x_2);
x_4 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_53, x_60, x_61, x_59, x_2);
lean_dec(x_53);
lean_dec_ref(x_62);
x_4 = lean_box(0);
goto block_7;
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspace___elam__0___redArg(x_1, x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0_spec__0(x_1, x_2, x_3);
return x_5;
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
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
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 10);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*13 + 2);
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
lean_dec(x_27);
lean_dec(x_15);
x_16 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_15);
x_16 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_30 = lean_box(0);
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc_ref(x_3);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_15, x_31, x_32, x_30, x_3);
lean_dec(x_15);
lean_dec_ref(x_33);
x_16 = lean_box(0);
goto block_26;
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
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_9);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec_ref(x_13);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_11, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_3);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_35, x_35);
if (x_39 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_3);
x_5 = lean_box(0);
goto block_8;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_34, x_41, x_42, x_40, x_3);
lean_dec(x_34);
lean_dec_ref(x_43);
x_5 = lean_box(0);
goto block_8;
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
