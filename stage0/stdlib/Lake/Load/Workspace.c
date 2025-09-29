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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__0;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspace___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6;
x_22 = lean_st_mk_ref(x_21, x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_19, 21);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_19, 21, x_28);
x_29 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_30 = lean_box(1);
x_31 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_4);
lean_ctor_set(x_32, 2, x_5);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set(x_32, 5, x_31);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_6);
lean_ctor_set(x_13, 0, x_32);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_22);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec_ref(x_20);
x_34 = l_Lake_Workspace_addFacetsFromEnv(x_33, x_6, x_32);
lean_dec(x_6);
x_35 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_34, x_26);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_13, 0, x_37);
lean_ctor_set(x_35, 0, x_13);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_13, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_io_error_to_string(x_42);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_17);
x_47 = lean_array_push(x_17, x_45);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_47);
lean_ctor_set(x_13, 0, x_46);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_13);
return x_35;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_io_error_to_string(x_48);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_get_size(x_17);
x_54 = lean_array_push(x_17, x_52);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_54);
lean_ctor_set(x_13, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_13);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = lean_ctor_get(x_22, 1);
x_58 = lean_ctor_get(x_19, 0);
x_59 = lean_ctor_get(x_19, 1);
x_60 = lean_ctor_get(x_19, 2);
x_61 = lean_ctor_get(x_19, 3);
x_62 = lean_ctor_get(x_19, 4);
x_63 = lean_ctor_get(x_19, 5);
x_64 = lean_ctor_get(x_19, 6);
x_65 = lean_ctor_get(x_19, 7);
x_66 = lean_ctor_get(x_19, 8);
x_67 = lean_ctor_get(x_19, 9);
x_68 = lean_ctor_get(x_19, 10);
x_69 = lean_ctor_get(x_19, 11);
x_70 = lean_ctor_get(x_19, 12);
x_71 = lean_ctor_get(x_19, 13);
x_72 = lean_ctor_get(x_19, 14);
x_73 = lean_ctor_get(x_19, 15);
x_74 = lean_ctor_get(x_19, 16);
x_75 = lean_ctor_get(x_19, 17);
x_76 = lean_ctor_get(x_19, 18);
x_77 = lean_ctor_get(x_19, 19);
x_78 = lean_ctor_get(x_19, 20);
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
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_19);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_56);
x_80 = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(x_80, 0, x_58);
lean_ctor_set(x_80, 1, x_59);
lean_ctor_set(x_80, 2, x_60);
lean_ctor_set(x_80, 3, x_61);
lean_ctor_set(x_80, 4, x_62);
lean_ctor_set(x_80, 5, x_63);
lean_ctor_set(x_80, 6, x_64);
lean_ctor_set(x_80, 7, x_65);
lean_ctor_set(x_80, 8, x_66);
lean_ctor_set(x_80, 9, x_67);
lean_ctor_set(x_80, 10, x_68);
lean_ctor_set(x_80, 11, x_69);
lean_ctor_set(x_80, 12, x_70);
lean_ctor_set(x_80, 13, x_71);
lean_ctor_set(x_80, 14, x_72);
lean_ctor_set(x_80, 15, x_73);
lean_ctor_set(x_80, 16, x_74);
lean_ctor_set(x_80, 17, x_75);
lean_ctor_set(x_80, 18, x_76);
lean_ctor_set(x_80, 19, x_77);
lean_ctor_set(x_80, 20, x_78);
lean_ctor_set(x_80, 21, x_79);
x_81 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_82 = lean_box(1);
x_83 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_4);
lean_ctor_set(x_84, 2, x_5);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
lean_ctor_set(x_84, 5, x_83);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_6);
lean_ctor_set(x_13, 0, x_84);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_22);
x_85 = lean_ctor_get(x_20, 0);
lean_inc(x_85);
lean_dec_ref(x_20);
x_86 = l_Lake_Workspace_addFacetsFromEnv(x_85, x_6, x_84);
lean_dec(x_6);
x_87 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_86, x_57);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
lean_ctor_set(x_13, 0, x_88);
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_13);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
x_95 = lean_io_error_to_string(x_92);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_17);
x_99 = lean_array_push(x_17, x_97);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_99);
lean_ctor_set(x_13, 0, x_98);
if (lean_is_scalar(x_94)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_94;
 lean_ctor_set_tag(x_100, 0);
}
lean_ctor_set(x_100, 0, x_13);
lean_ctor_set(x_100, 1, x_93);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_101 = lean_ctor_get(x_22, 0);
x_102 = lean_ctor_get(x_22, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_22);
x_103 = lean_ctor_get(x_19, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_19, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_19, 2);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_19, 5);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_19, 6);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_19, 7);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_19, 8);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_19, 9);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_19, 10);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_19, 11);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_19, 12);
lean_inc(x_115);
x_116 = lean_ctor_get(x_19, 13);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_19, 14);
lean_inc(x_117);
x_118 = lean_ctor_get(x_19, 15);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_19, 16);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_19, 17);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_19, 18);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_19, 19);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_19, 20);
lean_inc(x_123);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 lean_ctor_release(x_19, 14);
 lean_ctor_release(x_19, 15);
 lean_ctor_release(x_19, 16);
 lean_ctor_release(x_19, 17);
 lean_ctor_release(x_19, 18);
 lean_ctor_release(x_19, 19);
 lean_ctor_release(x_19, 20);
 lean_ctor_release(x_19, 21);
 x_124 = x_19;
} else {
 lean_dec_ref(x_19);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_101);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 22, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_103);
lean_ctor_set(x_126, 1, x_104);
lean_ctor_set(x_126, 2, x_105);
lean_ctor_set(x_126, 3, x_106);
lean_ctor_set(x_126, 4, x_107);
lean_ctor_set(x_126, 5, x_108);
lean_ctor_set(x_126, 6, x_109);
lean_ctor_set(x_126, 7, x_110);
lean_ctor_set(x_126, 8, x_111);
lean_ctor_set(x_126, 9, x_112);
lean_ctor_set(x_126, 10, x_113);
lean_ctor_set(x_126, 11, x_114);
lean_ctor_set(x_126, 12, x_115);
lean_ctor_set(x_126, 13, x_116);
lean_ctor_set(x_126, 14, x_117);
lean_ctor_set(x_126, 15, x_118);
lean_ctor_set(x_126, 16, x_119);
lean_ctor_set(x_126, 17, x_120);
lean_ctor_set(x_126, 18, x_121);
lean_ctor_set(x_126, 19, x_122);
lean_ctor_set(x_126, 20, x_123);
lean_ctor_set(x_126, 21, x_125);
x_127 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_128 = lean_box(1);
x_129 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_4);
lean_ctor_set(x_130, 2, x_5);
lean_ctor_set(x_130, 3, x_127);
lean_ctor_set(x_130, 4, x_128);
lean_ctor_set(x_130, 5, x_129);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_131; 
lean_dec(x_6);
lean_ctor_set(x_13, 0, x_130);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_13);
lean_ctor_set(x_131, 1, x_102);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_20, 0);
lean_inc(x_132);
lean_dec_ref(x_20);
x_133 = l_Lake_Workspace_addFacetsFromEnv(x_132, x_6, x_130);
lean_dec(x_6);
x_134 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_133, x_102);
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
lean_ctor_set(x_13, 0, x_135);
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_13);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_141 = x_134;
} else {
 lean_dec_ref(x_134);
 x_141 = lean_box(0);
}
x_142 = lean_io_error_to_string(x_139);
x_143 = 3;
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_143);
x_145 = lean_array_get_size(x_17);
x_146 = lean_array_push(x_17, x_144);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_146);
lean_ctor_set(x_13, 0, x_145);
if (lean_is_scalar(x_141)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_141;
 lean_ctor_set_tag(x_147, 0);
}
lean_ctor_set(x_147, 0, x_13);
lean_ctor_set(x_147, 1, x_140);
return x_147;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_148 = lean_ctor_get(x_13, 1);
lean_inc(x_148);
lean_dec(x_13);
x_149 = lean_ctor_get(x_14, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_14, 1);
lean_inc(x_150);
lean_dec(x_14);
x_151 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__6;
x_152 = lean_st_mk_ref(x_151, x_15);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_149, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_149, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_149, 2);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_149, 3);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_149, 4);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_149, 5);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_149, 6);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_149, 7);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_149, 8);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_149, 9);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_149, 10);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_149, 11);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_149, 12);
lean_inc(x_168);
x_169 = lean_ctor_get(x_149, 13);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_149, 14);
lean_inc(x_170);
x_171 = lean_ctor_get(x_149, 15);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_149, 16);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_149, 17);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_149, 18);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_149, 19);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_149, 20);
lean_inc(x_176);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 lean_ctor_release(x_149, 4);
 lean_ctor_release(x_149, 5);
 lean_ctor_release(x_149, 6);
 lean_ctor_release(x_149, 7);
 lean_ctor_release(x_149, 8);
 lean_ctor_release(x_149, 9);
 lean_ctor_release(x_149, 10);
 lean_ctor_release(x_149, 11);
 lean_ctor_release(x_149, 12);
 lean_ctor_release(x_149, 13);
 lean_ctor_release(x_149, 14);
 lean_ctor_release(x_149, 15);
 lean_ctor_release(x_149, 16);
 lean_ctor_release(x_149, 17);
 lean_ctor_release(x_149, 18);
 lean_ctor_release(x_149, 19);
 lean_ctor_release(x_149, 20);
 lean_ctor_release(x_149, 21);
 x_177 = x_149;
} else {
 lean_dec_ref(x_149);
 x_177 = lean_box(0);
}
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_153);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 22, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_156);
lean_ctor_set(x_179, 1, x_157);
lean_ctor_set(x_179, 2, x_158);
lean_ctor_set(x_179, 3, x_159);
lean_ctor_set(x_179, 4, x_160);
lean_ctor_set(x_179, 5, x_161);
lean_ctor_set(x_179, 6, x_162);
lean_ctor_set(x_179, 7, x_163);
lean_ctor_set(x_179, 8, x_164);
lean_ctor_set(x_179, 9, x_165);
lean_ctor_set(x_179, 10, x_166);
lean_ctor_set(x_179, 11, x_167);
lean_ctor_set(x_179, 12, x_168);
lean_ctor_set(x_179, 13, x_169);
lean_ctor_set(x_179, 14, x_170);
lean_ctor_set(x_179, 15, x_171);
lean_ctor_set(x_179, 16, x_172);
lean_ctor_set(x_179, 17, x_173);
lean_ctor_set(x_179, 18, x_174);
lean_ctor_set(x_179, 19, x_175);
lean_ctor_set(x_179, 20, x_176);
lean_ctor_set(x_179, 21, x_178);
x_180 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__7;
x_181 = lean_box(1);
x_182 = l___private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot___closed__8;
x_183 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_4);
lean_ctor_set(x_183, 2, x_5);
lean_ctor_set(x_183, 3, x_180);
lean_ctor_set(x_183, 4, x_181);
lean_ctor_set(x_183, 5, x_182);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_6);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_148);
if (lean_is_scalar(x_155)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_155;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_154);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_155);
x_186 = lean_ctor_get(x_150, 0);
lean_inc(x_186);
lean_dec_ref(x_150);
x_187 = l_Lake_Workspace_addFacetsFromEnv(x_186, x_6, x_183);
lean_dec(x_6);
x_188 = l_IO_ofExcept___at_____private_Lake_Load_Workspace_0__Lake_loadWorkspaceRoot_spec__0___redArg(x_187, x_154);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_148);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
x_197 = lean_io_error_to_string(x_194);
x_198 = 3;
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_198);
x_200 = lean_array_get_size(x_148);
x_201 = lean_array_push(x_148, x_199);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_196;
 lean_ctor_set_tag(x_203, 0);
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_195);
return x_203;
}
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_204 = !lean_is_exclusive(x_12);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_12, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_13);
if (x_206 == 0)
{
return x_12;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_13, 0);
x_208 = lean_ctor_get(x_13, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_13);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_12, 0, x_209);
return x_12;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_12, 1);
lean_inc(x_210);
lean_dec(x_12);
x_211 = lean_ctor_get(x_13, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_13, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_213 = x_13;
} else {
 lean_dec_ref(x_13);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
return x_215;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_48; uint8_t x_49; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
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
lean_inc_ref(x_2);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_19, x_52, x_53, x_51, x_2, x_17);
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
x_45 = l_Lake_loadWorkspace___closed__1;
x_46 = l_Lake_Workspace_updateAndMaterialize(x_18, x_45, x_9, x_12, x_2, x_20);
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
lean_dec_ref(x_16);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_lt(x_13, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_59, x_65, x_66, x_64, x_2, x_57);
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
lean_dec_ref(x_16);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_13, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
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
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_70, x_77, x_78, x_76, x_2, x_69);
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
uint8_t x_39; 
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_13, 1);
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_dec_ref(x_14);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_11, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_3);
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
lean_dec_ref(x_3);
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
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_42, x_48, x_49, x_47, x_3, x_40);
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
lean_dec_ref(x_14);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_lt(x_11, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_3);
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
lean_dec_ref(x_3);
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
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__0(x_53, x_60, x_61, x_59, x_3, x_52);
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
l_Lake_loadWorkspace___closed__0 = _init_l_Lake_loadWorkspace___closed__0();
lean_mark_persistent(l_Lake_loadWorkspace___closed__0);
l_Lake_loadWorkspace___closed__1 = _init_l_Lake_loadWorkspace___closed__1();
lean_mark_persistent(l_Lake_loadWorkspace___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
