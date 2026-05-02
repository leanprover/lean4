// Lean compiler output
// Module: LeanChecker
// Imports: public import Init public meta import Init public import Lean.CoreM public import Lean.Replay public import Lake.Load.Manifest
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
uint8_t l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object*);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
lean_object* l_Lean_Name_capitalize(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_findOLean(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_replay(lean_object*, lean_object*);
lean_object* lean_environment_free_regions(lean_object*);
lean_object* lean_read_module_data_parts(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_OLeanLevel_adjustFileName(lean_object*, uint8_t);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_withImportModules___redArg(lean_object*, lean_object*, lean_object*, uint32_t);
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_replayFromImports___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_replayFromImports___closed__0;
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
LEAN_EXPORT lean_object* l_replayFromImports(lean_object*);
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_replayFromFresh___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_replayFromFresh___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_replayFromFresh___closed__0 = (const lean_object*)&l_replayFromFresh___closed__0_value;
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object*);
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object*, lean_object*);
static const lean_string_object l_getCurrentModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lake-manifest.json"};
static const lean_object* l_getCurrentModule___closed__0 = (const lean_object*)&l_getCurrentModule___closed__0_value;
LEAN_EXPORT lean_object* l_getCurrentModule();
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object*);
static const lean_string_object l_List_partition_loop___at___00main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_List_partition_loop___at___00main_spec__0___closed__0 = (const lean_object*)&l_List_partition_loop___at___00main_spec__0___closed__0_value;
static lean_once_cell_t l_List_partition_loop___at___00main_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_partition_loop___at___00main_spec__0___closed__1;
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00main_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Could not resolve module: "};
static const lean_object* l_List_mapM_loop___at___00main_spec__6___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00main_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "replaying "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " with --fresh"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--fresh"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Could not find any oleans for: "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "leanchecker found a problem in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value;
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
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(lean_object* v_as_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v_b_4_);
return v___x_7_;
}
else
{
lean_object* v_snd_8_; lean_object* v_fst_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_42_; 
v_snd_8_ = lean_ctor_get(v_b_4_, 1);
v_fst_9_ = lean_ctor_get(v_b_4_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v_b_4_);
if (v_isSharedCheck_42_ == 0)
{
v___x_11_ = v_b_4_;
v_isShared_12_ = v_isSharedCheck_42_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_snd_8_);
lean_inc(v_fst_9_);
lean_dec(v_b_4_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_42_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v_array_13_; lean_object* v_start_14_; lean_object* v_stop_15_; uint8_t v___x_16_; 
v_array_13_ = lean_ctor_get(v_snd_8_, 0);
v_start_14_ = lean_ctor_get(v_snd_8_, 1);
v_stop_15_ = lean_ctor_get(v_snd_8_, 2);
v___x_16_ = lean_nat_dec_lt(v_start_14_, v_stop_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_18_; 
if (v_isShared_12_ == 0)
{
v___x_18_ = v___x_11_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_fst_9_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_snd_8_);
v___x_18_ = v_reuseFailAlloc_20_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_19_; 
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
}
else
{
lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_38_; 
lean_inc(v_stop_15_);
lean_inc(v_start_14_);
lean_inc_ref(v_array_13_);
v_isSharedCheck_38_ = !lean_is_exclusive(v_snd_8_);
if (v_isSharedCheck_38_ == 0)
{
lean_object* v_unused_39_; lean_object* v_unused_40_; lean_object* v_unused_41_; 
v_unused_39_ = lean_ctor_get(v_snd_8_, 2);
lean_dec(v_unused_39_);
v_unused_40_ = lean_ctor_get(v_snd_8_, 1);
lean_dec(v_unused_40_);
v_unused_41_ = lean_ctor_get(v_snd_8_, 0);
lean_dec(v_unused_41_);
v___x_22_ = v_snd_8_;
v_isShared_23_ = v_isSharedCheck_38_;
goto v_resetjp_21_;
}
else
{
lean_dec(v_snd_8_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_38_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_a_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v_a_24_ = lean_array_uget_borrowed(v_as_1_, v_i_3_);
v___x_25_ = lean_array_fget(v_array_13_, v_start_14_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_start_14_, v___x_26_);
lean_dec(v_start_14_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_27_);
v___x_29_ = v___x_22_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_array_13_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_stop_15_);
v___x_29_ = v_reuseFailAlloc_37_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; lean_object* v___x_32_; 
lean_inc(v_a_24_);
v___x_30_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_9_, v_a_24_, v___x_25_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___x_29_);
lean_ctor_set(v___x_11_, 0, v___x_30_);
v___x_32_ = v___x_11_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_29_);
v___x_32_ = v_reuseFailAlloc_36_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
size_t v___x_33_; size_t v___x_34_; 
v___x_33_ = ((size_t)1ULL);
v___x_34_ = lean_usize_add(v_i_3_, v___x_33_);
v_i_3_ = v___x_34_;
v_b_4_ = v___x_32_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object* v_as_43_, lean_object* v_sz_44_, lean_object* v_i_45_, lean_object* v_b_46_, lean_object* v___y_47_){
_start:
{
size_t v_sz_boxed_48_; size_t v_i_boxed_49_; lean_object* v_res_50_; 
v_sz_boxed_48_ = lean_unbox_usize(v_sz_44_);
lean_dec(v_sz_44_);
v_i_boxed_49_ = lean_unbox_usize(v_i_45_);
lean_dec(v_i_45_);
v_res_50_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_as_43_, v_sz_boxed_48_, v_i_boxed_49_, v_b_46_);
lean_dec_ref(v_as_43_);
return v_res_50_;
}
}
static lean_object* _init_l_replayFromImports___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_unsigned_to_nat(16u);
v___x_53_ = lean_mk_array(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static uint8_t _init_l_replayFromImports___closed__1(void){
_start:
{
uint8_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 2;
v___x_55_ = l_Lean_instOrdOLeanLevel_ord(v___x_54_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_replayFromImports(lean_object* v_module_62_){
_start:
{
lean_object* v___x_64_; 
lean_inc(v_module_62_);
v___x_64_ = l_Lean_findOLean(v_module_62_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_190_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_190_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_190_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_190_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___x_69_; lean_object* v___y_71_; uint8_t v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_75_; uint8_t v___y_76_; lean_object* v___y_77_; uint8_t v___y_78_; lean_object* v_fnames_139_; 
v___x_69_ = l_System_FilePath_pathExists(v_a_65_);
if (v___x_69_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_166_ = ((lean_object*)(l_replayFromImports___closed__4));
v___x_167_ = lean_string_append(v___x_166_, v_a_65_);
lean_dec(v_a_65_);
v___x_168_ = ((lean_object*)(l_replayFromImports___closed__5));
v___x_169_ = lean_string_append(v___x_167_, v___x_168_);
v___x_170_ = 1;
v___x_171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_62_, v___x_170_);
v___x_172_ = lean_string_append(v___x_169_, v___x_171_);
lean_dec_ref(v___x_171_);
v___x_173_ = ((lean_object*)(l_replayFromImports___closed__6));
v___x_174_ = lean_string_append(v___x_172_, v___x_173_);
v___x_175_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 1);
lean_ctor_set(v___x_67_, 0, v___x_175_);
v___x_177_ = v___x_67_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
lean_del_object(v___x_67_);
lean_dec(v_module_62_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
lean_inc_n(v_a_65_, 2);
v___x_181_ = lean_array_push(v___x_180_, v_a_65_);
v___x_182_ = 1;
v___x_183_ = l_Lean_OLeanLevel_adjustFileName(v_a_65_, v___x_182_);
v___x_184_ = l_System_FilePath_pathExists(v___x_183_);
if (v___x_184_ == 0)
{
lean_dec_ref(v___x_183_);
lean_dec(v_a_65_);
v_fnames_139_ = v___x_181_;
goto v___jp_138_;
}
else
{
uint8_t v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; 
v___x_185_ = 2;
v___x_186_ = l_Lean_OLeanLevel_adjustFileName(v_a_65_, v___x_185_);
v___x_187_ = l_System_FilePath_pathExists(v___x_186_);
v___x_188_ = lean_array_push(v___x_181_, v___x_183_);
if (v___x_187_ == 0)
{
lean_dec_ref(v___x_186_);
v_fnames_139_ = v___x_188_;
goto v___jp_138_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_array_push(v___x_188_, v___x_186_);
v_fnames_139_ = v___x_189_;
goto v___jp_138_;
}
}
}
v___jp_70_:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_imports_81_; lean_object* v___x_82_; 
v___x_79_ = l_Lean_instInhabitedImportState_default;
v___x_80_ = lean_st_mk_ref(v___x_79_);
v_imports_81_ = lean_ctor_get(v___y_75_, 0);
lean_inc_ref(v_imports_81_);
lean_dec_ref(v___y_75_);
lean_inc(v___y_74_);
v___x_82_ = l_Lean_importModulesCore(v_imports_81_, v___y_76_, v___y_74_, v___y_78_, v___x_80_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; uint32_t v___x_85_; lean_object* v___x_86_; 
lean_dec_ref(v___x_82_);
v___x_83_ = lean_st_ref_get(v___x_80_);
lean_dec(v___x_80_);
v___x_84_ = l_Lean_Options_empty;
v___x_85_ = 0;
v___x_86_ = l_Lean_finalizeImport(v___x_83_, v_imports_81_, v___x_84_, v___x_85_, v___y_72_, v___y_72_, v___y_76_, v___x_69_);
lean_dec(v___x_83_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_fst_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_128_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
lean_dec_ref(v___x_86_);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_sub(v___y_77_, v___x_88_);
lean_dec(v___y_77_);
v___x_90_ = lean_array_fget(v___y_71_, v___x_89_);
lean_dec(v___x_89_);
lean_dec_ref(v___y_71_);
v_fst_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_90_, 1);
lean_dec(v_unused_129_);
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_128_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_fst_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_128_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_constNames_95_; lean_object* v_constants_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v_constNames_95_ = lean_ctor_get(v_fst_91_, 1);
lean_inc_ref(v_constNames_95_);
v_constants_96_ = lean_ctor_get(v_fst_91_, 2);
lean_inc_ref(v_constants_96_);
lean_dec(v_fst_91_);
v___x_97_ = lean_obj_once(&l_replayFromImports___closed__0, &l_replayFromImports___closed__0_once, _init_l_replayFromImports___closed__0);
lean_inc(v___y_73_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_73_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_array_get_size(v_constants_96_);
v___x_100_ = l_Array_toSubarray___redArg(v_constants_96_, v___y_73_, v___x_99_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v___x_100_);
lean_ctor_set(v___x_93_, 0, v___x_98_);
v___x_102_ = v___x_93_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_127_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
size_t v_sz_103_; size_t v___x_104_; lean_object* v___x_105_; 
v_sz_103_ = lean_array_size(v_constNames_95_);
v___x_104_ = ((size_t)0ULL);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_constNames_95_, v_sz_103_, v___x_104_, v___x_102_);
lean_dec_ref(v_constNames_95_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_fst_107_; lean_object* v___x_108_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref(v___x_105_);
v_fst_107_ = lean_ctor_get(v_a_106_, 0);
lean_inc(v_fst_107_);
lean_dec(v_a_106_);
v___x_108_ = l_Lean_Environment_replay(v_fst_107_, v_a_87_);
lean_dec(v_fst_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v___x_108_);
v___x_110_ = lean_environment_free_regions(v_a_109_);
return v___x_110_;
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_108_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_108_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
lean_dec(v_a_87_);
v_a_119_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_105_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_105_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v___y_77_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_71_);
v_a_130_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_86_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_86_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_dec_ref(v_imports_81_);
lean_dec(v___x_80_);
lean_dec(v___y_77_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_71_);
return v___x_82_;
}
}
v___jp_138_:
{
lean_object* v___x_140_; 
v___x_140_ = lean_read_module_data_parts(v_fnames_139_);
lean_dec_ref(v_fnames_139_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_157_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_157_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_157_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_157_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_145_ = lean_array_get_size(v_a_141_);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_nat_dec_eq(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v_fst_149_; uint8_t v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
lean_del_object(v___x_143_);
v___x_148_ = lean_array_fget_borrowed(v_a_141_, v___x_146_);
v_fst_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_fst_149_);
v___x_150_ = 2;
v___x_151_ = lean_box(1);
v___x_152_ = lean_uint8_once(&l_replayFromImports___closed__1, &l_replayFromImports___closed__1_once, _init_l_replayFromImports___closed__1);
if (v___x_152_ == 0)
{
v___y_71_ = v_a_141_;
v___y_72_ = v___x_147_;
v___y_73_ = v___x_146_;
v___y_74_ = v___x_151_;
v___y_75_ = v_fst_149_;
v___y_76_ = v___x_150_;
v___y_77_ = v___x_145_;
v___y_78_ = v___x_69_;
goto v___jp_70_;
}
else
{
v___y_71_ = v_a_141_;
v___y_72_ = v___x_147_;
v___y_73_ = v___x_146_;
v___y_74_ = v___x_151_;
v___y_75_ = v_fst_149_;
v___y_76_ = v___x_150_;
v___y_77_ = v___x_145_;
v___y_78_ = v___x_147_;
goto v___jp_70_;
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_155_; 
lean_dec(v_a_141_);
v___x_153_ = ((lean_object*)(l_replayFromImports___closed__3));
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 1);
lean_ctor_set(v___x_143_, 0, v___x_153_);
v___x_155_ = v___x_143_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_158_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_140_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_140_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_module_62_);
v_a_191_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_64_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_64_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object* v_module_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_replayFromImports(v_module_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object* v_env_202_){
_start:
{
uint32_t v___x_204_; lean_object* v___x_205_; 
v___x_204_ = 0;
v___x_205_ = lean_mk_empty_environment(v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; lean_object* v_map_u2081_208_; lean_object* v___x_209_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref(v___x_205_);
v___x_207_ = l_Lean_Environment_constants(v_env_202_);
v_map_u2081_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_map_u2081_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = l_Lean_Environment_replay(v_map_u2081_208_, v_a_206_);
lean_dec_ref(v_map_u2081_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v___x_209_, 0);
lean_dec(v_unused_218_);
v___x_211_ = v___x_209_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_dec(v___x_209_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_box(0);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
v_a_219_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_209_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_209_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v_env_202_);
v_a_227_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_205_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_205_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* v_env_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_replayFromFresh___lam__0(v_env_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object* v_module_239_){
_start:
{
lean_object* v___f_241_; uint8_t v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint32_t v___x_249_; lean_object* v___x_250_; 
v___f_241_ = ((lean_object*)(l_replayFromFresh___closed__0));
v___x_242_ = 0;
v___x_243_ = 1;
v___x_244_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_244_, 0, v_module_239_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*1, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*1 + 1, v___x_243_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*1 + 2, v___x_242_);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_mk_empty_array_with_capacity(v___x_245_);
v___x_247_ = lean_array_push(v___x_246_, v___x_244_);
v___x_248_ = l_Lean_Options_empty;
v___x_249_ = 0;
v___x_250_ = l_Lean_withImportModules___redArg(v___x_247_, v___x_248_, v___f_241_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* v_module_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_replayFromFresh(v_module_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_getCurrentModule(){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l_getCurrentModule___closed__0));
v___x_257_ = l_Lake_Manifest_load_x3f(v___x_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_272_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_272_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_272_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_272_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
if (lean_obj_tag(v_a_258_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_box(0);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
else
{
lean_object* v_val_266_; lean_object* v_name_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v_val_266_ = lean_ctor_get(v_a_258_, 0);
lean_inc(v_val_266_);
lean_dec_ref(v_a_258_);
v_name_267_ = lean_ctor_get(v_val_266_, 0);
lean_inc(v_name_267_);
lean_dec(v_val_266_);
v___x_268_ = l_Lean_Name_capitalize(v_name_267_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_268_);
v___x_270_ = v___x_260_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_257_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_257_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_getCurrentModule();
return v_res_282_;
}
}
static lean_object* _init_l_List_partition_loop___at___00main_spec__0___closed__1(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_285_ = lean_string_utf8_byte_size(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
if (lean_obj_tag(v_a_286_) == 0)
{
lean_object* v_fst_288_; lean_object* v_snd_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_298_; 
v_fst_288_ = lean_ctor_get(v_a_287_, 0);
v_snd_289_ = lean_ctor_get(v_a_287_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_298_ == 0)
{
v___x_291_ = v_a_287_;
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_snd_289_);
lean_inc(v_fst_288_);
lean_dec(v_a_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_293_ = l_List_reverse___redArg(v_fst_288_);
v___x_294_ = l_List_reverse___redArg(v_snd_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_294_);
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v_head_299_; lean_object* v_tail_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_327_; 
v_head_299_ = lean_ctor_get(v_a_286_, 0);
v_tail_300_ = lean_ctor_get(v_a_286_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_327_ == 0)
{
v___x_302_ = v_a_286_;
v_isShared_303_ = v_isSharedCheck_327_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_tail_300_);
lean_inc(v_head_299_);
lean_dec(v_a_286_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_327_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_326_; 
v_fst_304_ = lean_ctor_get(v_a_287_, 0);
v_snd_305_ = lean_ctor_get(v_a_287_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_326_ == 0)
{
v___x_307_ = v_a_287_;
v_isShared_308_ = v_isSharedCheck_326_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_snd_305_);
lean_inc(v_fst_304_);
lean_dec(v_a_287_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_326_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_317_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_318_ = lean_string_utf8_byte_size(v_head_299_);
v___x_319_ = lean_obj_once(&l_List_partition_loop___at___00main_spec__0___closed__1, &l_List_partition_loop___at___00main_spec__0___closed__1_once, _init_l_List_partition_loop___at___00main_spec__0___closed__1);
v___x_320_ = lean_nat_dec_le(v___x_319_, v___x_318_);
if (v___x_320_ == 0)
{
goto v___jp_309_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_string_memcmp(v_head_299_, v___x_317_, v___x_321_, v___x_321_, v___x_319_);
if (v___x_322_ == 0)
{
goto v___jp_309_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_del_object(v___x_307_);
lean_del_object(v___x_302_);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v_head_299_);
lean_ctor_set(v___x_323_, 1, v_fst_304_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_snd_305_);
v_a_286_ = v_tail_300_;
v_a_287_ = v___x_324_;
goto _start;
}
}
v___jp_309_:
{
lean_object* v___x_311_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v_snd_305_);
v___x_311_ = v___x_302_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_head_299_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_snd_305_);
v___x_311_ = v_reuseFailAlloc_316_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_311_);
v___x_313_ = v___x_307_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_fst_304_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_315_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
v_a_286_ = v_tail_300_;
v_a_287_ = v___x_313_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(lean_object* v_head_328_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_replayFromImports(v_head_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 1);
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_a_339_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_330_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_330_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 0);
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed(lean_object* v_head_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(v_head_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v_as_x27_350_, lean_object* v_b_351_){
_start:
{
if (lean_obj_tag(v_as_x27_350_) == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v_b_351_);
return v___x_353_;
}
else
{
lean_object* v_head_354_; lean_object* v_tail_355_; lean_object* v___f_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_head_354_ = lean_ctor_get(v_as_x27_350_, 0);
v_tail_355_ = lean_ctor_get(v_as_x27_350_, 1);
lean_inc_n(v_head_354_, 2);
v___f_356_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_356_, 0, v_head_354_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_io_as_task(v___f_356_, v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_head_354_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_array_push(v_b_351_, v___x_359_);
v_as_x27_350_ = v_tail_355_;
v_b_351_ = v___x_360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v_as_x27_362_, lean_object* v_b_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_362_, v_b_363_);
lean_dec(v_as_x27_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6(lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_List_reverse___redArg(v_x_368_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v_head_372_; lean_object* v_tail_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_387_; 
v_head_372_ = lean_ctor_get(v_x_367_, 0);
v_tail_373_ = lean_ctor_get(v_x_367_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_367_);
if (v_isSharedCheck_387_ == 0)
{
v___x_375_ = v_x_367_;
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_tail_373_);
lean_inc(v_head_372_);
lean_dec(v_x_367_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
lean_inc(v_head_372_);
v___x_377_ = l_String_toName(v_head_372_);
v___x_378_ = l_Lean_Name_isAnonymous(v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_380_; 
lean_dec(v_head_372_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v_x_368_);
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_x_368_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
v_x_367_ = v_tail_373_;
v_x_368_ = v___x_380_;
goto _start;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v___x_377_);
lean_del_object(v___x_375_);
lean_dec(v_tail_373_);
lean_dec(v_x_368_);
v___x_383_ = ((lean_object*)(l_List_mapM_loop___at___00main_spec__6___closed__0));
v___x_384_ = lean_string_append(v___x_383_, v_head_372_);
lean_dec(v_head_372_);
v___x_385_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6___boxed(lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_List_mapM_loop___at___00main_spec__6(v_x_388_, v_x_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg(uint8_t v___y_394_, lean_object* v_as_x27_395_, lean_object* v_b_396_){
_start:
{
if (lean_obj_tag(v_as_x27_395_) == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_b_396_);
return v___x_398_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; 
v_head_399_ = lean_ctor_get(v_as_x27_395_, 0);
v_tail_400_ = lean_ctor_get(v_as_x27_395_, 1);
v___x_401_ = lean_box(0);
if (v___y_394_ == 0)
{
goto v___jp_402_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(v_head_399_);
v___x_406_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_399_, v___y_394_);
v___x_407_ = lean_string_append(v___x_405_, v___x_406_);
lean_dec_ref(v___x_406_);
v___x_408_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1));
v___x_409_ = lean_string_append(v___x_407_, v___x_408_);
v___x_410_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_dec_ref(v___x_410_);
goto v___jp_402_;
}
else
{
return v___x_410_;
}
}
v___jp_402_:
{
lean_object* v___x_403_; 
lean_inc(v_head_399_);
v___x_403_ = l_replayFromFresh(v_head_399_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_dec_ref(v___x_403_);
v_as_x27_395_ = v_tail_400_;
v_b_396_ = v___x_401_;
goto _start;
}
else
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(lean_object* v___y_411_, lean_object* v_as_x27_412_, lean_object* v_b_413_, lean_object* v___y_414_){
_start:
{
uint8_t v___y_5439__boxed_415_; lean_object* v_res_416_; 
v___y_5439__boxed_415_ = lean_unbox(v___y_411_);
v_res_416_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_5439__boxed_415_, v_as_x27_412_, v_b_413_);
lean_dec(v_as_x27_412_);
return v_res_416_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0(void){
_start:
{
lean_object* v___x_417_; lean_object* v___f_418_; 
v___x_417_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_418_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_418_, 0, v___x_417_);
return v___f_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v_val_420_, lean_object* v_a_421_, lean_object* v_fst_422_, lean_object* v_as_423_, size_t v_sz_424_, size_t v_i_425_, lean_object* v_b_426_){
_start:
{
lean_object* v_a_429_; uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_dec(v_fst_422_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_b_426_);
return v___x_434_;
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; 
v_a_435_ = lean_array_uget_borrowed(v_as_423_, v_i_425_);
lean_inc(v_a_435_);
v___x_436_ = l_Lean_searchModuleNameOfFileName(v_a_435_, v_val_420_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___y_439_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref(v___x_436_);
if (lean_obj_tag(v_a_437_) == 1)
{
lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_460_; 
v_fst_442_ = lean_ctor_get(v_b_426_, 0);
v_snd_443_ = lean_ctor_get(v_b_426_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_b_426_);
if (v_isSharedCheck_460_ == 0)
{
v___x_445_ = v_b_426_;
v_isShared_446_ = v_isSharedCheck_460_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snd_443_);
lean_inc(v_fst_442_);
lean_dec(v_b_426_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_460_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_val_447_; lean_object* v___f_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_val_447_ = lean_ctor_get(v_a_437_, 0);
lean_inc(v_val_447_);
lean_dec_ref(v_a_437_);
v___f_456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
lean_inc(v_fst_422_);
v___x_458_ = l_List_elem___redArg(v___f_456_, v___x_457_, v_fst_422_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = l_Lean_Name_isPrefixOf(v_a_421_, v_val_447_);
if (v___x_459_ == 0)
{
goto v___jp_451_;
}
else
{
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
goto v___jp_448_;
}
}
else
{
goto v___jp_451_;
}
v___jp_448_:
{
uint8_t v___x_449_; 
v___x_449_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v_val_447_, v_fst_442_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v_val_447_);
lean_ctor_set(v___x_450_, 1, v_fst_442_);
v___y_439_ = v___x_450_;
goto v___jp_438_;
}
else
{
lean_dec(v_val_447_);
v___y_439_ = v_fst_442_;
goto v___jp_438_;
}
}
v___jp_451_:
{
uint8_t v___x_452_; 
v___x_452_ = lean_name_eq(v_a_421_, v_val_447_);
if (v___x_452_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v_val_447_);
if (v_isShared_446_ == 0)
{
v___x_454_ = v___x_445_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_fst_442_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_snd_443_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
v_a_429_ = v___x_454_;
goto v___jp_428_;
}
}
else
{
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
goto v___jp_448_;
}
}
}
}
else
{
lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_a_437_);
v_fst_461_ = lean_ctor_get(v_b_426_, 0);
v_snd_462_ = lean_ctor_get(v_b_426_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_b_426_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v_b_426_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v_b_426_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_fst_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_snd_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v_a_429_ = v___x_467_;
goto v___jp_428_;
}
}
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_box(v___x_433_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___y_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v_a_429_ = v___x_441_;
goto v___jp_428_;
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v_b_426_);
lean_dec(v_fst_422_);
v_a_470_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_436_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_436_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
v___jp_428_:
{
size_t v___x_430_; size_t v___x_431_; 
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_425_, v___x_430_);
v_i_425_ = v___x_431_;
v_b_426_ = v_a_429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v_val_478_, lean_object* v_a_479_, lean_object* v_fst_480_, lean_object* v_as_481_, lean_object* v_sz_482_, lean_object* v_i_483_, lean_object* v_b_484_, lean_object* v___y_485_){
_start:
{
size_t v_sz_boxed_486_; size_t v_i_boxed_487_; lean_object* v_res_488_; 
v_sz_boxed_486_ = lean_unbox_usize(v_sz_482_);
lean_dec(v_sz_482_);
v_i_boxed_487_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_val_478_, v_a_479_, v_fst_480_, v_as_481_, v_sz_boxed_486_, v_i_boxed_487_, v_b_484_);
lean_dec_ref(v_as_481_);
lean_dec(v_a_479_);
lean_dec(v_val_478_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_val_491_, lean_object* v_fst_492_, lean_object* v_as_x27_493_, lean_object* v_b_494_){
_start:
{
if (lean_obj_tag(v_as_x27_493_) == 0)
{
lean_object* v___x_496_; 
lean_dec(v_fst_492_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v_b_494_);
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v_tail_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_head_497_ = lean_ctor_get(v_as_x27_493_, 0);
v_tail_498_ = lean_ctor_get(v_as_x27_493_, 1);
v___x_499_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0));
v___x_500_ = l_Lean_SearchPath_findAllWithExt(v_val_491_, v___x_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = 0;
v___x_503_ = lean_box(v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_b_494_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v_sz_505_ = lean_array_size(v_a_501_);
v___x_506_ = ((size_t)0ULL);
lean_inc(v_fst_492_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_val_491_, v_head_497_, v_fst_492_, v_a_501_, v_sz_505_, v___x_506_, v___x_504_);
lean_dec(v_a_501_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_524_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_524_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_524_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_524_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_snd_512_; uint8_t v___x_513_; 
v_snd_512_ = lean_ctor_get(v_a_508_, 1);
v___x_513_ = lean_unbox(v_snd_512_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
lean_dec(v_a_508_);
lean_dec(v_fst_492_);
v___x_514_ = 1;
v___x_515_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1));
lean_inc(v_head_497_);
v___x_516_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_497_, v___x_514_);
v___x_517_ = lean_string_append(v___x_515_, v___x_516_);
lean_dec_ref(v___x_516_);
v___x_518_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 1);
lean_ctor_set(v___x_510_, 0, v___x_518_);
v___x_520_ = v___x_510_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_object* v_fst_522_; 
lean_del_object(v___x_510_);
v_fst_522_ = lean_ctor_get(v_a_508_, 0);
lean_inc(v_fst_522_);
lean_dec(v_a_508_);
v_as_x27_493_ = v_tail_498_;
v_b_494_ = v_fst_522_;
goto _start;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_fst_492_);
v_a_525_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_507_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_507_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_b_494_);
lean_dec(v_fst_492_);
v_a_533_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_500_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_500_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_val_541_, lean_object* v_fst_542_, lean_object* v_as_x27_543_, lean_object* v_b_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_val_541_, v_fst_542_, v_as_x27_543_, v_b_544_);
lean_dec(v_as_x27_543_);
lean_dec(v_val_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(uint8_t v___y_548_, lean_object* v_as_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_b_552_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v_b_552_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___x_559_; 
v_a_556_ = lean_array_uget_borrowed(v_as_549_, v_i_551_);
v_fst_557_ = lean_ctor_get(v_a_556_, 0);
v_snd_558_ = lean_ctor_get(v_a_556_, 1);
v___x_559_ = lean_box(0);
if (v___y_548_ == 0)
{
goto v___jp_560_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(v_fst_557_);
v___x_579_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_557_, v___y_548_);
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_dec_ref(v___x_581_);
goto v___jp_560_;
}
else
{
return v___x_581_;
}
}
v___jp_560_:
{
lean_object* v___x_561_; 
lean_inc(v_snd_558_);
v___x_561_ = lean_task_get_own(v_snd_558_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref(v___x_561_);
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0));
lean_inc(v_fst_557_);
v___x_564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_557_, v___x_554_);
v___x_565_ = lean_string_append(v___x_563_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_566_, 0);
lean_dec(v_unused_574_);
v___x_568_ = v___x_566_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_dec(v___x_566_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 1);
lean_ctor_set(v___x_568_, 0, v_a_562_);
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_562_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_dec(v_a_562_);
return v___x_566_;
}
}
else
{
size_t v___x_575_; size_t v___x_576_; 
lean_dec(v___x_561_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_551_, v___x_575_);
v_i_551_ = v___x_576_;
v_b_552_ = v___x_559_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___boxed(lean_object* v___y_582_, lean_object* v_as_583_, lean_object* v_sz_584_, lean_object* v_i_585_, lean_object* v_b_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___y_5687__boxed_588_; size_t v_sz_boxed_589_; size_t v_i_boxed_590_; lean_object* v_res_591_; 
v___y_5687__boxed_588_ = lean_unbox(v___y_582_);
v_sz_boxed_589_ = lean_unbox_usize(v_sz_584_);
lean_dec(v_sz_584_);
v_i_boxed_590_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_5687__boxed_588_, v_as_583_, v_sz_boxed_589_, v_i_boxed_590_, v_b_586_);
lean_dec_ref(v_as_583_);
return v_res_591_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_600_; lean_object* v___x_601_; 
v___x_600_ = 0;
v___x_601_ = lean_box_uint32(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_602_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_main___closed__0));
v___x_608_ = l_Lean_findSysroot(v___x_607_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref(v___x_608_);
v___x_610_ = lean_box(0);
v___x_611_ = l_Lean_initSearchPath(v_a_609_, v___x_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___x_611_);
v___x_612_ = ((lean_object*)(l_main___closed__1));
v___x_613_ = l_List_partition_loop___at___00main_spec__0(v_args_602_, v___x_612_);
v_fst_614_ = lean_ctor_get(v___x_613_, 0);
v_snd_615_ = lean_ctor_get(v___x_613_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_713_ == 0)
{
v___x_617_ = v___x_613_;
v_isShared_618_ = v_isSharedCheck_713_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snd_615_);
lean_inc(v_fst_614_);
lean_dec(v___x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_713_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___f_619_; uint8_t v___y_621_; lean_object* v_targets_622_; uint8_t v___y_685_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___f_619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_709_ = ((lean_object*)(l_main___closed__4));
lean_inc(v_fst_614_);
v___x_710_ = l_List_elem___redArg(v___f_619_, v___x_709_, v_fst_614_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = ((lean_object*)(l_main___closed__5));
lean_inc(v_fst_614_);
v___x_712_ = l_List_elem___redArg(v___f_619_, v___x_711_, v_fst_614_);
v___y_685_ = v___x_712_;
goto v___jp_684_;
}
else
{
v___y_685_ = v___x_710_;
goto v___jp_684_;
}
v___jp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_searchPathRef;
v___x_624_ = lean_st_ref_get(v___x_623_);
lean_inc(v_fst_614_);
v___x_625_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_624_, v_fst_614_, v_targets_622_, v___x_610_);
lean_dec(v_targets_622_);
lean_dec(v___x_624_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_675_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_675_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_675_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_675_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
v___x_631_ = l_List_elem___redArg(v___f_619_, v___x_630_, v_fst_614_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_del_object(v___x_628_);
v___x_632_ = ((lean_object*)(l_main___closed__2));
v___x_633_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_a_626_, v___x_632_);
lean_dec(v_a_626_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; size_t v_sz_636_; size_t v___x_637_; lean_object* v___x_638_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_box(0);
v_sz_636_ = lean_array_size(v_a_634_);
v___x_637_ = ((size_t)0ULL);
v___x_638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_621_, v_a_634_, v_sz_636_, v___x_637_, v___x_635_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref(v___x_638_);
goto v___jp_604_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_633_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_633_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = l_List_lengthTR___redArg(v_a_626_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
lean_dec(v___x_655_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_658_ = ((lean_object*)(l_main___closed__3));
v___x_659_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_626_);
v___x_660_ = lean_string_append(v___x_658_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 1);
lean_ctor_set(v___x_628_, 0, v___x_661_);
v___x_663_ = v___x_628_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_del_object(v___x_628_);
v___x_665_ = lean_box(0);
v___x_666_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_621_, v_a_626_, v___x_665_);
lean_dec(v_a_626_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec_ref(v___x_666_);
goto v___jp_604_;
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_fst_614_);
v_a_676_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_625_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_625_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
v___jp_684_:
{
if (lean_obj_tag(v_snd_615_) == 0)
{
lean_object* v___x_686_; 
v___x_686_ = l_getCurrentModule();
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v___x_686_);
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 1);
lean_ctor_set(v___x_617_, 1, v___x_610_);
lean_ctor_set(v___x_617_, 0, v_a_687_);
v___x_689_ = v___x_617_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_687_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_610_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v___y_621_ = v___y_685_;
v_targets_622_ = v___x_689_;
goto v___jp_620_;
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_del_object(v___x_617_);
lean_dec(v_fst_614_);
v_a_691_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_686_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_686_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v___x_699_; 
lean_del_object(v___x_617_);
v___x_699_ = l_List_mapM_loop___at___00main_spec__6(v_snd_615_, v___x_610_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
v___y_621_ = v___y_685_;
v_targets_622_ = v_a_700_;
goto v___jp_620_;
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_fst_614_);
v_a_701_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_699_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_699_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_args_602_);
v_a_714_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_611_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_611_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_args_602_);
v_a_722_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_608_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_608_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
v___jp_604_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = l_main___boxed__const__1;
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = _lean_main(v_args_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_val_733_, lean_object* v_fst_734_, lean_object* v_as_735_, lean_object* v_as_x27_736_, lean_object* v_b_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_val_733_, v_fst_734_, v_as_x27_736_, v_b_737_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_val_741_, lean_object* v_fst_742_, lean_object* v_as_743_, lean_object* v_as_x27_744_, lean_object* v_b_745_, lean_object* v_a_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_List_forIn_x27_loop___at___00main_spec__2(v_val_741_, v_fst_742_, v_as_743_, v_as_x27_744_, v_b_745_, v_a_746_);
lean_dec(v_as_x27_744_);
lean_dec(v_as_743_);
lean_dec(v_val_741_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_749_, lean_object* v_as_x27_750_, lean_object* v_b_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_750_, v_b_751_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_755_, lean_object* v_as_x27_756_, lean_object* v_b_757_, lean_object* v_a_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_755_, v_as_x27_756_, v_b_757_, v_a_758_);
lean_dec(v_as_x27_756_);
lean_dec(v_as_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5(uint8_t v___y_761_, lean_object* v_as_762_, lean_object* v_as_x27_763_, lean_object* v_b_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_761_, v_as_x27_763_, v_b_764_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___boxed(lean_object* v___y_768_, lean_object* v_as_769_, lean_object* v_as_x27_770_, lean_object* v_b_771_, lean_object* v_a_772_, lean_object* v___y_773_){
_start:
{
uint8_t v___y_6062__boxed_774_; lean_object* v_res_775_; 
v___y_6062__boxed_774_ = lean_unbox(v___y_768_);
v_res_775_ = l_List_forIn_x27_loop___at___00main_spec__5(v___y_6062__boxed_774_, v_as_769_, v_as_x27_770_, v_b_771_, v_a_772_);
lean_dec(v_as_x27_770_);
lean_dec(v_as_769_);
return v_res_775_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanChecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin);
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
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = initialize_LeanChecker(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
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
