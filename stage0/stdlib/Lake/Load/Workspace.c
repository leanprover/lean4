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
static lean_once_cell_t l_Lake_loadWorkspaceRoot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_loadWorkspaceRoot___closed__1;
static lean_once_cell_t l_Lake_loadWorkspaceRoot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_loadWorkspaceRoot___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_loadWorkspaceRoot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__3 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__3_value;
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_loadWorkspace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadWorkspace___closed__0 = (const lean_object*)&l_Lake_loadWorkspace___closed__0_value;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_io_user_error(x_3);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_13 = x_1;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
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
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lake_loadWorkspaceRoot___closed__1, &l_Lake_loadWorkspaceRoot___closed__1_once, _init_l_Lake_loadWorkspaceRoot___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_133; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = lean_ctor_get(x_1, 9);
x_13 = lean_ctor_get(x_1, 10);
x_14 = lean_ctor_get(x_1, 11);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*14);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 2);
x_18 = lean_ctor_get(x_1, 12);
x_19 = lean_ctor_get(x_1, 13);
x_133 = !lean_is_exclusive(x_1);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_1, 3);
lean_dec(x_134);
x_20 = x_1;
x_21 = x_133;
goto block_132;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_searchPathRef;
x_23 = l_Lake_Env_leanSearchPath(x_4);
x_24 = lean_st_ref_set(x_22, x_23);
lean_inc_ref(x_4);
x_25 = l_Lake_loadLakeConfig(x_4, x_2);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
x_29 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_14);
lean_inc(x_5);
lean_inc_ref(x_4);
if (x_21 == 0)
{
lean_ctor_set(x_20, 3, x_29);
x_30 = x_20;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_122, 0, x_4);
lean_ctor_set(x_122, 1, x_5);
lean_ctor_set(x_122, 2, x_6);
lean_ctor_set(x_122, 3, x_29);
lean_ctor_set(x_122, 4, x_7);
lean_ctor_set(x_122, 5, x_8);
lean_ctor_set(x_122, 6, x_9);
lean_ctor_set(x_122, 7, x_10);
lean_ctor_set(x_122, 8, x_11);
lean_ctor_set(x_122, 9, x_12);
lean_ctor_set(x_122, 10, x_13);
lean_ctor_set(x_122, 11, x_14);
lean_ctor_set(x_122, 12, x_18);
lean_ctor_set(x_122, 13, x_19);
lean_ctor_set_uint8(x_122, sizeof(void*)*14, x_15);
lean_ctor_set_uint8(x_122, sizeof(void*)*14 + 1, x_16);
lean_ctor_set_uint8(x_122, sizeof(void*)*14 + 2, x_17);
x_30 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_31; 
x_31 = l_Lake_loadPackageCore(x_28, x_30, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_111; 
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_111 = !lean_is_exclusive(x_31);
if (x_111 == 0)
{
x_34 = x_31;
x_35 = x_111;
goto block_110;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_108; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_obj_once(&l_Lake_loadWorkspaceRoot___closed__2, &l_Lake_loadWorkspaceRoot___closed__2_once, _init_l_Lake_loadWorkspaceRoot___closed__2);
x_39 = lean_st_mk_ref(x_38);
x_40 = lean_ctor_get(x_36, 6);
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
x_43 = lean_ctor_get(x_36, 2);
x_44 = lean_ctor_get(x_36, 3);
x_45 = lean_ctor_get(x_36, 4);
x_46 = lean_ctor_get(x_36, 5);
x_47 = lean_ctor_get(x_36, 7);
x_48 = lean_ctor_get(x_36, 8);
x_49 = lean_ctor_get(x_36, 9);
x_50 = lean_ctor_get(x_36, 10);
x_51 = lean_ctor_get(x_36, 11);
x_52 = lean_ctor_get(x_36, 12);
x_53 = lean_ctor_get(x_36, 13);
x_54 = lean_ctor_get(x_36, 14);
x_55 = lean_ctor_get(x_36, 15);
x_56 = lean_ctor_get(x_36, 16);
x_57 = lean_ctor_get(x_36, 17);
x_58 = lean_ctor_get(x_36, 18);
x_59 = lean_ctor_get(x_36, 19);
x_60 = lean_ctor_get(x_36, 20);
x_61 = lean_ctor_get(x_36, 21);
x_62 = lean_ctor_get(x_36, 22);
x_108 = !lean_is_exclusive(x_36);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_36, 23);
lean_dec(x_109);
x_63 = x_36;
x_64 = x_108;
goto block_107;
}
else
{
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_40);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_63 = lean_box(0);
x_64 = x_108;
goto block_107;
}
block_107:
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get_uint8(x_40, sizeof(void*)*27);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_39);
lean_inc_ref(x_45);
if (x_64 == 0)
{
lean_ctor_set(x_63, 23, x_66);
x_67 = x_63;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(x_106, 0, x_41);
lean_ctor_set(x_106, 1, x_42);
lean_ctor_set(x_106, 2, x_43);
lean_ctor_set(x_106, 3, x_44);
lean_ctor_set(x_106, 4, x_45);
lean_ctor_set(x_106, 5, x_46);
lean_ctor_set(x_106, 6, x_40);
lean_ctor_set(x_106, 7, x_47);
lean_ctor_set(x_106, 8, x_48);
lean_ctor_set(x_106, 9, x_49);
lean_ctor_set(x_106, 10, x_50);
lean_ctor_set(x_106, 11, x_51);
lean_ctor_set(x_106, 12, x_52);
lean_ctor_set(x_106, 13, x_53);
lean_ctor_set(x_106, 14, x_54);
lean_ctor_set(x_106, 15, x_55);
lean_ctor_set(x_106, 16, x_56);
lean_ctor_set(x_106, 17, x_57);
lean_ctor_set(x_106, 18, x_58);
lean_ctor_set(x_106, 19, x_59);
lean_ctor_set(x_106, 20, x_60);
lean_ctor_set(x_106, 21, x_61);
lean_ctor_set(x_106, 22, x_62);
lean_ctor_set(x_106, 23, x_66);
x_67 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_68; 
if (x_65 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_4, 7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = l_Lake_defaultLakeDir;
x_95 = l_Lake_joinRelative(x_45, x_94);
x_96 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_97 = l_Lake_joinRelative(x_95, x_96);
x_68 = x_97;
goto block_92;
}
else
{
lean_object* x_98; 
lean_dec_ref(x_45);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_68 = x_98;
goto block_92;
}
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_4, 8);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = l_Lake_defaultLakeDir;
x_101 = l_Lake_joinRelative(x_45, x_100);
x_102 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
x_103 = l_Lake_joinRelative(x_101, x_102);
x_68 = x_103;
goto block_92;
}
else
{
lean_object* x_104; 
lean_dec_ref(x_45);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_68 = x_104;
goto block_92;
}
}
block_92:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__3));
x_70 = lean_box(1);
x_71 = l_Lake_initFacetConfigs;
x_72 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_4);
lean_ctor_set(x_72, 2, x_26);
lean_ctor_set(x_72, 3, x_68);
lean_ctor_set(x_72, 4, x_5);
lean_ctor_set(x_72, 5, x_69);
lean_ctor_set(x_72, 6, x_70);
lean_ctor_set(x_72, 7, x_71);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_37, 0);
lean_inc(x_73);
lean_dec_ref(x_37);
x_74 = l_Lake_Workspace_addFacetsFromEnv(x_73, x_14, x_72);
lean_dec_ref(x_14);
x_75 = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_76);
x_77 = x_34;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_33);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
lean_dec_ref(x_75);
x_81 = lean_io_error_to_string(x_80);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_84 = lean_array_get_size(x_33);
x_85 = lean_array_push(x_33, x_83);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_85);
lean_ctor_set(x_34, 0, x_84);
x_86 = x_34;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_85);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_37);
lean_dec_ref(x_14);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_72);
x_89 = x_34;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_33);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_120; 
lean_dec(x_26);
lean_dec_ref(x_14);
lean_dec(x_5);
lean_dec_ref(x_4);
x_112 = lean_ctor_get(x_31, 0);
x_113 = lean_ctor_get(x_31, 1);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
x_114 = x_31;
x_115 = x_120;
goto block_119;
}
else
{
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_31);
x_114 = lean_box(0);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_115 == 0)
{
x_116 = x_114;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_113);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_123 = lean_ctor_get(x_25, 0);
x_124 = lean_ctor_get(x_25, 1);
x_131 = !lean_is_exclusive(x_25);
if (x_131 == 0)
{
x_125 = x_25;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_25);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_124);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
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
x_8 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_8);
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*14);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 1);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
x_14 = l_Lake_loadWorkspaceRoot(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_43; uint8_t x_44; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_43 = lean_array_get_size(x_16);
x_44 = lean_nat_dec_lt(x_12, x_43);
if (x_44 == 0)
{
lean_dec(x_16);
goto block_42;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_box(0);
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
if (x_44 == 0)
{
lean_dec(x_16);
goto block_42;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_43);
lean_inc_ref(x_2);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_16, x_47, x_48, x_45, x_2);
lean_dec(x_16);
if (lean_obj_tag(x_49) == 0)
{
lean_dec_ref(x_49);
goto block_42;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_15);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_50 = lean_ctor_get(x_49, 0);
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
x_51 = x_49;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_43);
lean_inc_ref(x_2);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_16, x_58, x_59, x_45, x_2);
lean_dec(x_16);
if (lean_obj_tag(x_60) == 0)
{
lean_dec_ref(x_60);
goto block_42;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_15);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_61 = lean_ctor_get(x_60, 0);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
x_62 = x_60;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
block_42:
{
if (x_10 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 4);
x_19 = lean_ctor_get(x_17, 9);
lean_inc_ref(x_19);
lean_inc_ref(x_18);
x_20 = l_Lake_joinRelative(x_18, x_19);
x_21 = l_Lake_Manifest_load_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lake_Workspace_materializeDeps(x_15, x_23, x_8, x_9, x_7, x_2);
lean_dec_ref(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec_ref(x_7);
x_25 = l_Lean_NameSet_empty;
x_26 = l_Lake_Workspace_updateAndMaterialize(x_15, x_25, x_8, x_11, x_2);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_39; 
lean_dec(x_15);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_27 = lean_ctor_get(x_21, 0);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
x_28 = x_21;
x_29 = x_39;
goto block_38;
}
else
{
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_io_error_to_string(x_27);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_apply_2(x_2, x_32, lean_box(0));
x_34 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_34);
x_35 = x_28;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_7);
x_40 = l_Lean_NameSet_empty;
x_41 = l_Lake_Workspace_updateAndMaterialize(x_15, x_40, x_8, x_11, x_2);
return x_41;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_69 = lean_ctor_get(x_14, 1);
lean_inc(x_69);
lean_dec_ref(x_14);
x_70 = lean_array_get_size(x_69);
x_71 = lean_nat_dec_lt(x_12, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
lean_dec_ref(x_2);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_box(0);
x_75 = lean_nat_dec_le(x_70, x_70);
if (x_75 == 0)
{
if (x_71 == 0)
{
lean_dec(x_69);
lean_dec_ref(x_2);
goto block_6;
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_70);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_69, x_76, x_77, x_74, x_2);
lean_dec(x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
goto block_6;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
x_79 = lean_ctor_get(x_78, 0);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
x_80 = x_78;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_70);
x_89 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_69, x_87, x_88, x_74, x_2);
lean_dec(x_69);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
goto block_6;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
x_90 = lean_ctor_get(x_89, 0);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
x_91 = x_89;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*14 + 2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
x_12 = l_Lake_loadWorkspaceRoot(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_34; uint8_t x_35; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_34 = lean_array_get_size(x_14);
x_35 = lean_nat_dec_lt(x_10, x_34);
if (x_35 == 0)
{
lean_dec(x_14);
goto block_33;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(0);
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
if (x_35 == 0)
{
lean_dec(x_14);
goto block_33;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
lean_inc_ref(x_3);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_14, x_38, x_39, x_36, x_3);
lean_dec(x_14);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
goto block_33;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
return x_40;
}
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_34);
lean_inc_ref(x_3);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_14, x_41, x_42, x_36, x_3);
lean_dec(x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
goto block_33;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
return x_43;
}
}
}
block_33:
{
lean_object* x_15; 
x_15 = l_Lake_Workspace_updateAndMaterialize(x_13, x_2, x_8, x_9, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_16 = x_15;
x_17 = x_23;
goto block_22;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_15, 0);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
x_26 = x_15;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec_ref(x_8);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_dec_ref(x_12);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_10, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec_ref(x_3);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_box(0);
x_50 = lean_nat_dec_le(x_45, x_45);
if (x_50 == 0)
{
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec_ref(x_3);
goto block_7;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_44, x_51, x_52, x_49, x_3);
lean_dec(x_44);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
goto block_7;
}
else
{
return x_53;
}
}
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_45);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(x_44, x_54, x_55, x_49, x_3);
lean_dec(x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_dec_ref(x_56);
goto block_7;
}
else
{
return x_56;
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
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateManifest(x_1, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Resolve(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Toml(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_InitFacets(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Load_Config(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Resolve(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Eval(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Toml(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_InitFacets(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Lake_Load_Config(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Resolve(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InitFacets(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Workspace(builtin);
}
#ifdef __cplusplus
}
#endif
