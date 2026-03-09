// Lean compiler output
// Module: LeanChecker
// Imports: public import Init public import Lean.CoreM public import Lean.Replay public import LeanChecker.Replay public import Lake.Load.Manifest
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
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_replayFromImports___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_replayFromImports___closed__0;
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
static lean_once_cell_t l_replayFromImports___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_replayFromImports___closed__1;
static const lean_string_object l_replayFromImports___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to read module data"};
static const lean_object* l_replayFromImports___closed__2 = (const lean_object*)&l_replayFromImports___closed__2_value;
static const lean_ctor_object l_replayFromImports___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_replayFromImports___closed__2_value)}};
static const lean_object* l_replayFromImports___closed__3 = (const lean_object*)&l_replayFromImports___closed__3_value;
static const lean_string_object l_replayFromImports___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "object file '"};
static const lean_object* l_replayFromImports___closed__4 = (const lean_object*)&l_replayFromImports___closed__4_value;
static const lean_string_object l_replayFromImports___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' of module "};
static const lean_object* l_replayFromImports___closed__5 = (const lean_object*)&l_replayFromImports___closed__5_value;
static const lean_string_object l_replayFromImports___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " does not exist"};
static const lean_object* l_replayFromImports___closed__6 = (const lean_object*)&l_replayFromImports___closed__6_value;
lean_object* l_Lean_findOLean(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_replay_x27(lean_object*, lean_object*);
lean_object* lean_environment_free_regions(lean_object*);
lean_object* lean_read_module_data_parts(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_OLeanLevel_adjustFileName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_replayFromImports(lean_object*);
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t);
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_replayFromFresh___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_replayFromFresh___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_replayFromFresh___closed__0 = (const lean_object*)&l_replayFromFresh___closed__0_value;
lean_object* l_Lean_withImportModules___redArg(lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object*, lean_object*);
static const lean_string_object l_getCurrentModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lake-manifest.json"};
static const lean_object* l_getCurrentModule___closed__0 = (const lean_object*)&l_getCurrentModule___closed__0_value;
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
lean_object* l_Lean_Name_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_getCurrentModule();
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object*);
static const lean_string_object l_List_partition_loop___at___00main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_List_partition_loop___at___00main_spec__0___closed__0 = (const lean_object*)&l_List_partition_loop___at___00main_spec__0___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_List_partition_loop___at___00main_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_partition_loop___at___00main_spec__0___closed__1;
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00main_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Could not resolve module: "};
static const lean_object* l_List_mapM_loop___at___00main_spec__6___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00main_spec__6___closed__0_value;
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "replaying "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " with --fresh"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--fresh"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
uint8_t l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Could not find any oleans for: "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1_value;
lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "leanchecker found a problem in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value;
lean_object* lean_task_get_own(lean_object*);
lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_ctor_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_array_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "--fresh flag is only valid when specifying a single module:\n"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static const lean_string_object l_main___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-v"};
static const lean_object* l_main___closed__4 = (const lean_object*)&l_main___closed__4_value;
static const lean_string_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--verbose"};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(lean_object*);
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_42 = !lean_is_exclusive(x_4);
if (x_42 == 0)
{
x_10 = x_4;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
if (x_11 == 0)
{
x_16 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_37; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_20 = x_8;
x_21 = x_37;
goto block_36;
}
else
{
lean_dec(x_8);
x_20 = lean_box(0);
x_21 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_array_fget(x_12, x_13);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_13, x_24);
lean_dec(x_13);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_25);
x_26 = x_20;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_14);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; 
lean_inc(x_22);
x_27 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(x_9, x_22, x_23);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_27);
lean_ctor_set(x_10, 0, x_26);
x_28 = x_10;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
x_28 = x_33;
goto block_32;
}
block_32:
{
size_t x_29; size_t x_30; 
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_4 = x_28;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_replayFromImports___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_replayFromImports___closed__1(void) {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 2;
x_2 = l_Lean_instOrdOLeanLevel_ord(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_replayFromImports(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_findOLean(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_129; 
x_4 = lean_ctor_get(x_3, 0);
x_129 = !lean_is_exclusive(x_3);
if (x_129 == 0)
{
x_5 = x_3;
x_6 = x_129;
goto block_128;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_129;
goto block_128;
}
block_128:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_76; 
x_7 = l_System_FilePath_pathExists(x_4);
if (x_7 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = ((lean_object*)(l_replayFromImports___closed__4));
x_105 = lean_string_append(x_104, x_4);
lean_dec(x_4);
x_106 = ((lean_object*)(l_replayFromImports___closed__5));
x_107 = lean_string_append(x_105, x_106);
x_108 = 1;
x_109 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_108);
x_110 = lean_string_append(x_107, x_109);
lean_dec_ref(x_109);
x_111 = ((lean_object*)(l_replayFromImports___closed__6));
x_112 = lean_string_append(x_110, x_111);
x_113 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_113);
x_114 = x_5;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_113);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; 
lean_del_object(x_5);
lean_dec(x_1);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_mk_empty_array_with_capacity(x_117);
lean_inc(x_4);
x_119 = lean_array_push(x_118, x_4);
x_120 = 1;
lean_inc(x_4);
x_121 = l_Lean_OLeanLevel_adjustFileName(x_4, x_120);
x_122 = l_System_FilePath_pathExists(x_121);
if (x_122 == 0)
{
lean_dec_ref(x_121);
lean_dec(x_4);
x_76 = x_119;
goto block_103;
}
else
{
uint8_t x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_123 = 2;
x_124 = l_Lean_OLeanLevel_adjustFileName(x_4, x_123);
x_125 = l_System_FilePath_pathExists(x_124);
x_126 = lean_array_push(x_119, x_121);
if (x_125 == 0)
{
lean_dec_ref(x_124);
x_76 = x_126;
goto block_103;
}
else
{
lean_object* x_127; 
x_127 = lean_array_push(x_126, x_124);
x_76 = x_127;
goto block_103;
}
}
}
block_75:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_instInhabitedImportState_default;
x_17 = lean_st_mk_ref(x_16);
x_18 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_10);
lean_inc(x_17);
x_19 = l_Lean_importModulesCore(x_18, x_12, x_9, x_15, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; 
lean_dec_ref(x_19);
x_20 = lean_st_ref_get(x_17);
lean_dec(x_17);
x_21 = l_Lean_Options_empty;
x_22 = 0;
x_23 = l_Lean_finalizeImport(x_20, x_18, x_21, x_22, x_11, x_11, x_12, x_7);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_65; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_14, x_25);
lean_dec(x_14);
x_27 = lean_array_fget(x_8, x_26);
lean_dec(x_26);
lean_dec_ref(x_8);
x_28 = lean_ctor_get(x_27, 0);
x_65 = !lean_is_exclusive(x_27);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_27, 1);
lean_dec(x_66);
x_29 = x_27;
x_30 = x_65;
goto block_64;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_32);
lean_dec(x_28);
x_33 = lean_obj_once(&l_replayFromImports___closed__0, &l_replayFromImports___closed__0_once, _init_l_replayFromImports___closed__0);
lean_inc(x_13);
if (x_30 == 0)
{
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_13);
x_34 = x_29;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_13);
lean_ctor_set(x_63, 1, x_33);
x_34 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_35 = lean_array_get_size(x_32);
x_36 = l_Array_toSubarray___redArg(x_32, x_13, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_array_size(x_31);
x_39 = 0;
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(x_31, x_38, x_39, x_37);
lean_dec_ref(x_31);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Environment_replay_x27(x_42, x_24);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_environment_free_regions(x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
x_46 = lean_ctor_get(x_43, 0);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
x_47 = x_43;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_24);
x_54 = lean_ctor_get(x_40, 0);
x_61 = !lean_is_exclusive(x_40);
if (x_61 == 0)
{
x_55 = x_40;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_8);
x_67 = lean_ctor_get(x_23, 0);
x_74 = !lean_is_exclusive(x_23);
if (x_74 == 0)
{
x_68 = x_23;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_23);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_8);
return x_19;
}
}
block_103:
{
lean_object* x_77; 
x_77 = lean_read_module_data_parts(x_76);
lean_dec_ref(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_94; 
x_78 = lean_ctor_get(x_77, 0);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
x_79 = x_77;
x_80 = x_94;
goto block_93;
}
else
{
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_80 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_array_get_size(x_78);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_nat_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; 
lean_del_object(x_79);
x_84 = lean_array_fget_borrowed(x_78, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = 2;
x_87 = lean_box(1);
x_88 = lean_uint8_once(&l_replayFromImports___closed__1, &l_replayFromImports___closed__1_once, _init_l_replayFromImports___closed__1);
if (x_88 == 0)
{
x_8 = x_78;
x_9 = x_87;
x_10 = x_85;
x_11 = x_83;
x_12 = x_86;
x_13 = x_82;
x_14 = x_81;
x_15 = x_7;
goto block_75;
}
else
{
x_8 = x_78;
x_9 = x_87;
x_10 = x_85;
x_11 = x_83;
x_12 = x_86;
x_13 = x_82;
x_14 = x_81;
x_15 = x_83;
goto block_75;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
x_89 = ((lean_object*)(l_replayFromImports___closed__3));
if (x_80 == 0)
{
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_89);
x_90 = x_79;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_89);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
x_95 = lean_ctor_get(x_77, 0);
x_102 = !lean_is_exclusive(x_77);
if (x_102 == 0)
{
x_96 = x_77;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_77);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_137; 
lean_dec(x_1);
x_130 = lean_ctor_get(x_3, 0);
x_137 = !lean_is_exclusive(x_3);
if (x_137 == 0)
{
x_131 = x_3;
x_132 = x_137;
goto block_136;
}
else
{
lean_inc(x_130);
lean_dec(x_3);
x_131 = lean_box(0);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_132 == 0)
{
x_133 = x_131;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_130);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_replayFromImports(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_mk_empty_environment(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Environment_constants(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_Environment_replay_x27(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_9 = x_8;
x_10 = x_16;
goto block_15;
}
else
{
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_4, 0);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
x_27 = x_4;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_replayFromFresh___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; 
x_3 = ((lean_object*)(l_replayFromFresh___closed__0));
x_4 = 0;
x_5 = 1;
x_6 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 2, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_array_push(x_8, x_6);
x_10 = l_Lean_Options_empty;
x_11 = 0;
x_12 = l_Lean_withImportModules___redArg(x_9, x_10, x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_replayFromFresh(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_getCurrentModule() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_getCurrentModule___closed__0));
x_3 = l_Lake_Manifest_load_x3f(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_5 = x_3;
x_6 = x_18;
goto block_17;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_18;
goto block_17;
}
block_17:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Name_capitalize(x_12);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_13);
x_14 = x_5;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_19 = lean_ctor_get(x_3, 0);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
x_20 = x_3;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_getCurrentModule();
return x_2;
}
}
static lean_object* _init_l_List_partition_loop___at___00main_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_List_reverse___redArg(x_3);
x_8 = l_List_reverse___redArg(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_8);
lean_ctor_set(x_5, 0, x_7);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_42; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
x_16 = x_1;
x_17 = x_42;
goto block_41;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_40; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
x_20 = x_2;
x_21 = x_40;
goto block_39;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
x_31 = lean_string_utf8_byte_size(x_14);
x_32 = lean_obj_once(&l_List_partition_loop___at___00main_spec__0___closed__1, &l_List_partition_loop___at___00main_spec__0___closed__1_once, _init_l_List_partition_loop___at___00main_spec__0___closed__1);
x_33 = lean_nat_dec_le(x_32, x_31);
if (x_33 == 0)
{
goto block_29;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_string_memcmp(x_14, x_30, x_34, x_34, x_32);
if (x_35 == 0)
{
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_del_object(x_20);
lean_del_object(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_19);
x_1 = x_15;
x_2 = x_37;
goto _start;
}
}
block_29:
{
lean_object* x_22; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_19);
x_22 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_19);
x_22 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_23; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_22);
x_23 = x_20;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_22);
x_23 = x_26;
goto block_25;
}
block_25:
{
x_1 = x_15;
x_2 = x_23;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_replayFromImports(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
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
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_7 = x_1;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_io_as_task(x_9, x_10);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_11);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_11);
x_12 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_13; 
x_13 = lean_array_push(x_2, x_12);
x_1 = x_6;
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00main_spec__3___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___redArg(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_21; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
x_8 = x_1;
x_9 = x_21;
goto block_20;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_6);
x_10 = l_String_toName(x_6);
x_11 = l_Lean_Name_isAnonymous(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_10);
x_12 = x_8;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_2);
x_12 = x_15;
goto block_14;
}
block_14:
{
x_1 = x_7;
x_2 = x_12;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_del_object(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_16 = ((lean_object*)(l_List_mapM_loop___at___00main_spec__6___closed__0));
x_17 = lean_string_append(x_16, x_6);
lean_dec(x_6);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM_loop___at___00main_spec__6(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_box(0);
if (x_1 == 0)
{
goto block_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(x_6);
x_13 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_1);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
goto block_11;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
block_11:
{
lean_object* x_9; 
x_9 = l_replayFromFresh(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_9);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_7);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_List_forIn_x27_loop___at___00main_spec__5___redArg(x_5, x_2, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget_borrowed(x_4, x_6);
lean_inc(x_1);
lean_inc(x_16);
x_17 = l_Lean_searchModuleNameOfFileName(x_16, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_41; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
x_25 = x_7;
x_26 = x_41;
goto block_40;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_box(0);
x_26 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_27; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec_ref(x_18);
x_36 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
x_37 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
lean_inc(x_3);
x_38 = l_List_elem___redArg(x_36, x_37, x_3);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Name_isPrefixOf(x_2, x_27);
if (x_39 == 0)
{
goto block_35;
}
else
{
lean_del_object(x_25);
lean_dec(x_23);
goto block_30;
}
}
else
{
goto block_35;
}
block_30:
{
uint8_t x_28; 
x_28 = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(x_27, x_24);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_24);
x_19 = x_29;
goto block_22;
}
else
{
lean_dec(x_27);
x_19 = x_24;
goto block_22;
}
}
block_35:
{
uint8_t x_31; 
x_31 = lean_name_eq(x_2, x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
if (x_26 == 0)
{
x_32 = x_25;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_9 = x_32;
goto block_13;
}
}
else
{
lean_del_object(x_25);
lean_dec(x_23);
goto block_30;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_18);
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
x_44 = x_7;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_9 = x_46;
goto block_13;
}
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_9 = x_21;
goto block_13;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_ctor_get(x_17, 0);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
x_52 = x_17;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_17);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(x_1, x_2, x_3, x_4, x_9, x_10, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_56; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
x_9 = x_3;
x_10 = x_56;
goto block_55;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0));
lean_inc(x_1);
x_12 = l_Lean_SearchPath_findAllWithExt(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 0;
x_15 = lean_box(x_14);
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 0, x_15);
x_16 = x_9;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_4);
x_16 = x_46;
goto block_45;
}
block_45:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_array_size(x_13);
x_18 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(x_1, x_7, x_2, x_13, x_17, x_18, x_16);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_36; 
x_20 = lean_ctor_get(x_19, 0);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
x_21 = x_19;
x_22 = x_36;
goto block_35;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_25 = 1;
x_26 = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1));
x_27 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_7, x_25);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
if (x_22 == 0)
{
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_29);
x_30 = x_21;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
else
{
lean_object* x_33; 
lean_del_object(x_21);
lean_dec(x_7);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_3 = x_8;
x_4 = x_33;
goto _start;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_19, 0);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
x_38 = x_19;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_del_object(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_12, 0);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
x_48 = x_12;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00main_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget_borrowed(x_2, x_4);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_box(0);
if (x_1 == 0)
{
goto block_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(x_10);
x_32 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_10, x_1);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
goto block_30;
}
else
{
return x_34;
}
}
block_30:
{
lean_object* x_13; 
lean_inc(x_11);
x_13 = lean_task_get_own(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0));
lean_inc(x_10);
x_16 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_10, x_7);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_19 = x_18;
x_20 = x_25;
goto block_24;
}
else
{
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_14);
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_14);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_dec(x_14);
return x_18;
}
}
else
{
size_t x_27; size_t x_28; 
lean_dec(x_13);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_4 = x_28;
x_5 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(x_7, x_2, x_8, x_9, x_5);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l_main___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* x_1) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_main___closed__0));
x_7 = l_Lean_findSysroot(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_initSearchPath(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_112; 
lean_dec_ref(x_10);
x_11 = ((lean_object*)(l_main___closed__1));
x_12 = l_List_partition_loop___at___00main_spec__0(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_112 = !lean_is_exclusive(x_12);
if (x_112 == 0)
{
x_15 = x_12;
x_16 = x_112;
goto block_111;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_82; lean_object* x_107; uint8_t x_108; 
x_17 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
x_107 = ((lean_object*)(l_main___closed__4));
lean_inc(x_13);
x_108 = l_List_elem___redArg(x_17, x_107, x_13);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = ((lean_object*)(l_main___closed__5));
lean_inc(x_13);
x_110 = l_List_elem___redArg(x_17, x_109, x_13);
x_82 = x_110;
goto block_106;
}
else
{
x_82 = x_108;
goto block_106;
}
block_81:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_searchPathRef;
x_21 = lean_st_ref_get(x_20);
lean_inc(x_13);
x_22 = l_List_forIn_x27_loop___at___00main_spec__2___redArg(x_21, x_13, x_19, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_72; 
x_23 = lean_ctor_get(x_22, 0);
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
x_24 = x_22;
x_25 = x_72;
goto block_71;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_26; uint8_t x_27; 
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
x_27 = l_List_elem___redArg(x_17, x_26, x_13);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_del_object(x_24);
x_28 = ((lean_object*)(l_main___closed__2));
x_29 = l_List_forIn_x27_loop___at___00main_spec__3___redArg(x_23, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_box(0);
x_32 = lean_array_size(x_30);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(x_18, x_30, x_32, x_33, x_31);
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
goto block_5;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
x_35 = lean_ctor_get(x_34, 0);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
x_36 = x_34;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
x_43 = lean_ctor_get(x_29, 0);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
x_44 = x_29;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = l_List_lengthTR___redArg(x_23);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = ((lean_object*)(l_main___closed__3));
x_55 = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(x_23);
x_56 = lean_string_append(x_54, x_55);
lean_dec_ref(x_55);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_57);
x_58 = x_24;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_del_object(x_24);
x_61 = lean_box(0);
x_62 = l_List_forIn_x27_loop___at___00main_spec__5___redArg(x_18, x_23, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
goto block_5;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
x_63 = lean_ctor_get(x_62, 0);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
x_64 = x_62;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_13);
x_73 = lean_ctor_get(x_22, 0);
x_80 = !lean_is_exclusive(x_22);
if (x_80 == 0)
{
x_74 = x_22;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_22);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
block_106:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_83; 
x_83 = l_getCurrentModule();
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 0, x_84);
x_85 = x_15;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_9);
x_85 = x_87;
goto block_86;
}
block_86:
{
x_18 = x_82;
x_19 = x_85;
goto block_81;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_del_object(x_15);
lean_dec(x_13);
x_88 = lean_ctor_get(x_83, 0);
x_95 = !lean_is_exclusive(x_83);
if (x_95 == 0)
{
x_89 = x_83;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
else
{
lean_object* x_96; 
lean_del_object(x_15);
x_96 = l_List_mapM_loop___at___00main_spec__6(x_14, x_9);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_18 = x_82;
x_19 = x_97;
goto block_81;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_13);
x_98 = lean_ctor_get(x_96, 0);
x_105 = !lean_is_exclusive(x_96);
if (x_105 == 0)
{
x_99 = x_96;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_120; 
lean_dec(x_1);
x_113 = lean_ctor_get(x_10, 0);
x_120 = !lean_is_exclusive(x_10);
if (x_120 == 0)
{
x_114 = x_10;
x_115 = x_120;
goto block_119;
}
else
{
lean_inc(x_113);
lean_dec(x_10);
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
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_113);
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
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec(x_1);
x_121 = lean_ctor_get(x_7, 0);
x_128 = !lean_is_exclusive(x_7);
if (x_128 == 0)
{
x_122 = x_7;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_7);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_main___boxed__const__1;
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = _lean_main(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00main_spec__2___redArg(x_1, x_2, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00main_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00main_spec__3___redArg(x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00main_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___00main_spec__5___redArg(x_1, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_List_forIn_x27_loop___at___00main_spec__5(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_LeanChecker_Replay(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanChecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Replay(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanChecker_Replay(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
  #endif
  lean_object* in; lean_object* res;
argv = lean_setup_args(argc, argv);
lean_initialize();
lean_set_panic_messages(false);
res = initialize_LeanChecker(1 /* builtin */);
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
in = lean_box(0);
int i = argc;
while (i > 1) {
 lean_object* n;
 i--;
 n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
 in = n;
}
res = _lean_main(in);
}
lean_finalize_task_manager();
if (lean_io_result_is_ok(res)) {
  int ret = lean_unbox_uint32(lean_io_result_get_value(res));
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
