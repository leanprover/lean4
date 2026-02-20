// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: public import Lake.Load.Config public import Lake.Config.Workspace import Lake.Load.Resolve import Lake.Load.Package import Lake.Load.Lean.Eval import Lake.Load.Toml import Lake.Build.InitFacets
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
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_loadWorkspaceRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[root]"};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__0 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__0_value;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lake_loadWorkspaceRoot___closed__1;
static lean_object* l_Lake_loadWorkspaceRoot___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_loadWorkspaceRoot___closed__3;
static const lean_string_object l_Lake_loadWorkspaceRoot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__4 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__4_value;
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_loadLakeConfig(lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lake_initFacetConfigs;
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_loadWorkspace___closed__0;
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_loadWorkspaceRoot___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_ctor_get(x_1, 9);
x_14 = lean_ctor_get(x_1, 10);
x_15 = lean_ctor_get(x_1, 11);
x_16 = lean_ctor_get(x_1, 12);
x_17 = lean_ctor_get(x_1, 13);
x_18 = lean_ctor_get(x_1, 3);
lean_dec(x_18);
x_19 = l_Lean_searchPathRef;
x_20 = l_Lake_Env_leanSearchPath(x_5);
x_21 = lean_st_ref_set(x_19, x_20);
lean_inc_ref(x_5);
x_22 = l_Lake_loadLakeConfig(x_5, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
x_26 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_15);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_ctor_set(x_1, 3, x_26);
x_27 = l_Lake_loadPackageCore(x_25, x_1, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lake_loadWorkspaceRoot___closed__2;
x_34 = lean_st_mk_ref(x_33);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_31, 6);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 23);
lean_dec(x_38);
x_39 = lean_ctor_get_uint8(x_36, sizeof(void*)*26);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_34);
lean_inc_ref(x_37);
lean_ctor_set(x_31, 23, x_40);
if (x_39 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_5, 7);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = l_Lake_defaultLakeDir;
x_62 = l_Lake_joinRelative(x_37, x_61);
x_63 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_64 = l_Lake_joinRelative(x_62, x_63);
x_41 = x_64;
goto block_59;
}
else
{
lean_object* x_65; 
lean_dec_ref(x_37);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_41 = x_65;
goto block_59;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_5, 8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = l_Lake_defaultLakeDir;
x_68 = l_Lake_joinRelative(x_37, x_67);
x_69 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_70 = l_Lake_joinRelative(x_68, x_69);
x_41 = x_70;
goto block_59;
}
else
{
lean_object* x_71; 
lean_dec_ref(x_37);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_41 = x_71;
goto block_59;
}
}
block_59:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = l_Lake_loadWorkspaceRoot___closed__3;
x_43 = lean_box(1);
x_44 = l_Lake_initFacetConfigs;
x_45 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_5);
lean_ctor_set(x_45, 2, x_23);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_6);
lean_ctor_set(x_45, 5, x_42);
lean_ctor_set(x_45, 6, x_43);
lean_ctor_set(x_45, 7, x_44);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
lean_dec_ref(x_32);
x_47 = l_Lake_Workspace_addFacetsFromEnv(x_46, x_15, x_45);
lean_dec_ref(x_15);
x_48 = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
if (lean_is_scalar(x_30)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_30;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_29);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec_ref(x_48);
x_52 = lean_io_error_to_string(x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_29);
x_56 = lean_array_push(x_29, x_54);
if (lean_is_scalar(x_30)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_30;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_32);
lean_dec_ref(x_15);
if (lean_is_scalar(x_30)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_30;
}
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_29);
return x_58;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_72 = lean_ctor_get(x_31, 6);
x_73 = lean_ctor_get(x_31, 0);
x_74 = lean_ctor_get(x_31, 1);
x_75 = lean_ctor_get(x_31, 2);
x_76 = lean_ctor_get(x_31, 3);
x_77 = lean_ctor_get(x_31, 4);
x_78 = lean_ctor_get(x_31, 5);
x_79 = lean_ctor_get(x_31, 7);
x_80 = lean_ctor_get(x_31, 8);
x_81 = lean_ctor_get(x_31, 9);
x_82 = lean_ctor_get(x_31, 10);
x_83 = lean_ctor_get(x_31, 11);
x_84 = lean_ctor_get(x_31, 12);
x_85 = lean_ctor_get(x_31, 13);
x_86 = lean_ctor_get(x_31, 14);
x_87 = lean_ctor_get(x_31, 15);
x_88 = lean_ctor_get(x_31, 16);
x_89 = lean_ctor_get(x_31, 17);
x_90 = lean_ctor_get(x_31, 18);
x_91 = lean_ctor_get(x_31, 19);
x_92 = lean_ctor_get(x_31, 20);
x_93 = lean_ctor_get(x_31, 21);
x_94 = lean_ctor_get(x_31, 22);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_72);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_31);
x_95 = lean_ctor_get_uint8(x_72, sizeof(void*)*26);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_34);
lean_inc_ref(x_77);
x_97 = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(x_97, 0, x_73);
lean_ctor_set(x_97, 1, x_74);
lean_ctor_set(x_97, 2, x_75);
lean_ctor_set(x_97, 3, x_76);
lean_ctor_set(x_97, 4, x_77);
lean_ctor_set(x_97, 5, x_78);
lean_ctor_set(x_97, 6, x_72);
lean_ctor_set(x_97, 7, x_79);
lean_ctor_set(x_97, 8, x_80);
lean_ctor_set(x_97, 9, x_81);
lean_ctor_set(x_97, 10, x_82);
lean_ctor_set(x_97, 11, x_83);
lean_ctor_set(x_97, 12, x_84);
lean_ctor_set(x_97, 13, x_85);
lean_ctor_set(x_97, 14, x_86);
lean_ctor_set(x_97, 15, x_87);
lean_ctor_set(x_97, 16, x_88);
lean_ctor_set(x_97, 17, x_89);
lean_ctor_set(x_97, 18, x_90);
lean_ctor_set(x_97, 19, x_91);
lean_ctor_set(x_97, 20, x_92);
lean_ctor_set(x_97, 21, x_93);
lean_ctor_set(x_97, 22, x_94);
lean_ctor_set(x_97, 23, x_96);
if (x_95 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_5, 7);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = l_Lake_defaultLakeDir;
x_119 = l_Lake_joinRelative(x_77, x_118);
x_120 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_121 = l_Lake_joinRelative(x_119, x_120);
x_98 = x_121;
goto block_116;
}
else
{
lean_object* x_122; 
lean_dec_ref(x_77);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_98 = x_122;
goto block_116;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_5, 8);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = l_Lake_defaultLakeDir;
x_125 = l_Lake_joinRelative(x_77, x_124);
x_126 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_127 = l_Lake_joinRelative(x_125, x_126);
x_98 = x_127;
goto block_116;
}
else
{
lean_object* x_128; 
lean_dec_ref(x_77);
x_128 = lean_ctor_get(x_123, 0);
lean_inc(x_128);
x_98 = x_128;
goto block_116;
}
}
block_116:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = l_Lake_loadWorkspaceRoot___closed__3;
x_100 = lean_box(1);
x_101 = l_Lake_initFacetConfigs;
x_102 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_102, 0, x_97);
lean_ctor_set(x_102, 1, x_5);
lean_ctor_set(x_102, 2, x_23);
lean_ctor_set(x_102, 3, x_98);
lean_ctor_set(x_102, 4, x_6);
lean_ctor_set(x_102, 5, x_99);
lean_ctor_set(x_102, 6, x_100);
lean_ctor_set(x_102, 7, x_101);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_32, 0);
lean_inc(x_103);
lean_dec_ref(x_32);
x_104 = l_Lake_Workspace_addFacetsFromEnv(x_103, x_15, x_102);
lean_dec_ref(x_15);
x_105 = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
if (lean_is_scalar(x_30)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_30;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_29);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec_ref(x_105);
x_109 = lean_io_error_to_string(x_108);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_get_size(x_29);
x_113 = lean_array_push(x_29, x_111);
if (lean_is_scalar(x_30)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_30;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_dec(x_32);
lean_dec_ref(x_15);
if (lean_is_scalar(x_30)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_30;
}
lean_ctor_set(x_115, 0, x_102);
lean_ctor_set(x_115, 1, x_29);
return x_115;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_23);
lean_dec_ref(x_15);
lean_dec(x_6);
lean_dec_ref(x_5);
x_129 = !lean_is_exclusive(x_27);
if (x_129 == 0)
{
return x_27;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_27, 0);
x_131 = lean_ctor_get(x_27, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_27);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_free_object(x_1);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_133 = !lean_is_exclusive(x_22);
if (x_133 == 0)
{
return x_22;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_22, 0);
x_135 = lean_ctor_get(x_22, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_22);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_137 = lean_ctor_get(x_1, 0);
x_138 = lean_ctor_get(x_1, 1);
x_139 = lean_ctor_get(x_1, 2);
x_140 = lean_ctor_get(x_1, 4);
x_141 = lean_ctor_get(x_1, 5);
x_142 = lean_ctor_get(x_1, 6);
x_143 = lean_ctor_get(x_1, 7);
x_144 = lean_ctor_get(x_1, 8);
x_145 = lean_ctor_get(x_1, 9);
x_146 = lean_ctor_get(x_1, 10);
x_147 = lean_ctor_get(x_1, 11);
x_148 = lean_ctor_get_uint8(x_1, sizeof(void*)*14);
x_149 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 1);
x_150 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 2);
x_151 = lean_ctor_get(x_1, 12);
x_152 = lean_ctor_get(x_1, 13);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_1);
x_153 = l_Lean_searchPathRef;
x_154 = l_Lake_Env_leanSearchPath(x_137);
x_155 = lean_st_ref_set(x_153, x_154);
lean_inc_ref(x_137);
x_156 = l_Lake_loadLakeConfig(x_137, x_2);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
x_160 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_147);
lean_inc(x_138);
lean_inc_ref(x_137);
x_161 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_161, 0, x_137);
lean_ctor_set(x_161, 1, x_138);
lean_ctor_set(x_161, 2, x_139);
lean_ctor_set(x_161, 3, x_160);
lean_ctor_set(x_161, 4, x_140);
lean_ctor_set(x_161, 5, x_141);
lean_ctor_set(x_161, 6, x_142);
lean_ctor_set(x_161, 7, x_143);
lean_ctor_set(x_161, 8, x_144);
lean_ctor_set(x_161, 9, x_145);
lean_ctor_set(x_161, 10, x_146);
lean_ctor_set(x_161, 11, x_147);
lean_ctor_set(x_161, 12, x_151);
lean_ctor_set(x_161, 13, x_152);
lean_ctor_set_uint8(x_161, sizeof(void*)*14, x_148);
lean_ctor_set_uint8(x_161, sizeof(void*)*14 + 1, x_149);
lean_ctor_set_uint8(x_161, sizeof(void*)*14 + 2, x_150);
x_162 = l_Lake_loadPackageCore(x_159, x_161, x_158);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
lean_dec(x_163);
x_168 = l_Lake_loadWorkspaceRoot___closed__2;
x_169 = lean_st_mk_ref(x_168);
x_170 = lean_ctor_get(x_166, 6);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_166, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_166, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_166, 4);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_166, 5);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_166, 7);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_166, 8);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_166, 9);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_166, 10);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_166, 11);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_166, 12);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_166, 13);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_166, 14);
lean_inc(x_184);
x_185 = lean_ctor_get(x_166, 15);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_166, 16);
lean_inc(x_186);
x_187 = lean_ctor_get(x_166, 17);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_166, 18);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_166, 19);
lean_inc_ref(x_189);
x_190 = lean_ctor_get(x_166, 20);
lean_inc_ref(x_190);
x_191 = lean_ctor_get(x_166, 21);
lean_inc_ref(x_191);
x_192 = lean_ctor_get(x_166, 22);
lean_inc(x_192);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 lean_ctor_release(x_166, 5);
 lean_ctor_release(x_166, 6);
 lean_ctor_release(x_166, 7);
 lean_ctor_release(x_166, 8);
 lean_ctor_release(x_166, 9);
 lean_ctor_release(x_166, 10);
 lean_ctor_release(x_166, 11);
 lean_ctor_release(x_166, 12);
 lean_ctor_release(x_166, 13);
 lean_ctor_release(x_166, 14);
 lean_ctor_release(x_166, 15);
 lean_ctor_release(x_166, 16);
 lean_ctor_release(x_166, 17);
 lean_ctor_release(x_166, 18);
 lean_ctor_release(x_166, 19);
 lean_ctor_release(x_166, 20);
 lean_ctor_release(x_166, 21);
 lean_ctor_release(x_166, 22);
 lean_ctor_release(x_166, 23);
 x_193 = x_166;
} else {
 lean_dec_ref(x_166);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get_uint8(x_170, sizeof(void*)*26);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_169);
lean_inc_ref(x_175);
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(0, 24, 0);
} else {
 x_196 = x_193;
}
lean_ctor_set(x_196, 0, x_171);
lean_ctor_set(x_196, 1, x_172);
lean_ctor_set(x_196, 2, x_173);
lean_ctor_set(x_196, 3, x_174);
lean_ctor_set(x_196, 4, x_175);
lean_ctor_set(x_196, 5, x_176);
lean_ctor_set(x_196, 6, x_170);
lean_ctor_set(x_196, 7, x_177);
lean_ctor_set(x_196, 8, x_178);
lean_ctor_set(x_196, 9, x_179);
lean_ctor_set(x_196, 10, x_180);
lean_ctor_set(x_196, 11, x_181);
lean_ctor_set(x_196, 12, x_182);
lean_ctor_set(x_196, 13, x_183);
lean_ctor_set(x_196, 14, x_184);
lean_ctor_set(x_196, 15, x_185);
lean_ctor_set(x_196, 16, x_186);
lean_ctor_set(x_196, 17, x_187);
lean_ctor_set(x_196, 18, x_188);
lean_ctor_set(x_196, 19, x_189);
lean_ctor_set(x_196, 20, x_190);
lean_ctor_set(x_196, 21, x_191);
lean_ctor_set(x_196, 22, x_192);
lean_ctor_set(x_196, 23, x_195);
if (x_194 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_137, 7);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = l_Lake_defaultLakeDir;
x_218 = l_Lake_joinRelative(x_175, x_217);
x_219 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_220 = l_Lake_joinRelative(x_218, x_219);
x_197 = x_220;
goto block_215;
}
else
{
lean_object* x_221; 
lean_dec_ref(x_175);
x_221 = lean_ctor_get(x_216, 0);
lean_inc(x_221);
x_197 = x_221;
goto block_215;
}
}
else
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_137, 8);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = l_Lake_defaultLakeDir;
x_224 = l_Lake_joinRelative(x_175, x_223);
x_225 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_226 = l_Lake_joinRelative(x_224, x_225);
x_197 = x_226;
goto block_215;
}
else
{
lean_object* x_227; 
lean_dec_ref(x_175);
x_227 = lean_ctor_get(x_222, 0);
lean_inc(x_227);
x_197 = x_227;
goto block_215;
}
}
block_215:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = l_Lake_loadWorkspaceRoot___closed__3;
x_199 = lean_box(1);
x_200 = l_Lake_initFacetConfigs;
x_201 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_201, 0, x_196);
lean_ctor_set(x_201, 1, x_137);
lean_ctor_set(x_201, 2, x_157);
lean_ctor_set(x_201, 3, x_197);
lean_ctor_set(x_201, 4, x_138);
lean_ctor_set(x_201, 5, x_198);
lean_ctor_set(x_201, 6, x_199);
lean_ctor_set(x_201, 7, x_200);
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_167, 0);
lean_inc(x_202);
lean_dec_ref(x_167);
x_203 = l_Lake_Workspace_addFacetsFromEnv(x_202, x_147, x_201);
lean_dec_ref(x_147);
x_204 = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
if (lean_is_scalar(x_165)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_165;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_164);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_207 = lean_ctor_get(x_204, 0);
lean_inc(x_207);
lean_dec_ref(x_204);
x_208 = lean_io_error_to_string(x_207);
x_209 = 3;
x_210 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_209);
x_211 = lean_array_get_size(x_164);
x_212 = lean_array_push(x_164, x_210);
if (lean_is_scalar(x_165)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_165;
 lean_ctor_set_tag(x_213, 1);
}
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; 
lean_dec(x_167);
lean_dec_ref(x_147);
if (lean_is_scalar(x_165)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_165;
}
lean_ctor_set(x_214, 0, x_201);
lean_ctor_set(x_214, 1, x_164);
return x_214;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_157);
lean_dec_ref(x_147);
lean_dec(x_138);
lean_dec_ref(x_137);
x_228 = lean_ctor_get(x_162, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_162, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_230 = x_162;
} else {
 lean_dec_ref(x_162);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec_ref(x_137);
x_232 = lean_ctor_get(x_156, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_156, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_234 = x_156;
} else {
 lean_dec_ref(x_156);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspaceRoot(x_1, x_2);
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
x_15 = l_Lake_loadWorkspaceRoot(x_1, x_14);
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
x_13 = l_Lake_loadWorkspaceRoot(x_1, x_12);
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
lean_object* initialize_Lake_Load_Toml(uint8_t builtin);
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
res = initialize_Lake_Load_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_loadWorkspaceRoot___closed__1 = _init_l_Lake_loadWorkspaceRoot___closed__1();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__1);
l_Lake_loadWorkspaceRoot___closed__2 = _init_l_Lake_loadWorkspaceRoot___closed__2();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__2);
l_Lake_loadWorkspaceRoot___closed__3 = _init_l_Lake_loadWorkspaceRoot___closed__3();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__3);
l_Lake_loadWorkspace___closed__0 = _init_l_Lake_loadWorkspace___closed__0();
lean_mark_persistent(l_Lake_loadWorkspace___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
