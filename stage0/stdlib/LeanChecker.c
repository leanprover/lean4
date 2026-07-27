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
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_Kernel_Environment_replay(lean_object*, lean_object*);
lean_object* lean_environment_free_regions(lean_object*);
lean_object* l_Lean_readModuleDataParts(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_OLeanLevel_adjustFileName(lean_object*, uint8_t);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
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
v_imports_81_ = lean_ctor_get(v___y_73_, 0);
lean_inc_ref(v_imports_81_);
lean_dec_ref(v___y_73_);
lean_inc(v___y_71_);
v___x_82_ = l_Lean_importModulesCore(v_imports_81_, v___y_76_, v___y_71_, v___y_78_, v___y_72_, v___x_80_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; uint32_t v___x_85_; lean_object* v___x_86_; 
lean_dec_ref_known(v___x_82_, 1);
v___x_83_ = lean_st_ref_get(v___x_80_);
lean_dec(v___x_80_);
v___x_84_ = l_Lean_Options_empty;
v___x_85_ = 0;
v___x_86_ = l_Lean_finalizeImport(v___x_83_, v_imports_81_, v___x_84_, v___x_85_, v___y_72_, v___y_72_, v___y_76_, v___x_69_, v___y_72_);
lean_dec(v___x_83_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_fst_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_128_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_86_, 1);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_sub(v___y_75_, v___x_88_);
lean_dec(v___y_75_);
v___x_90_ = lean_array_fget(v___y_74_, v___x_89_);
lean_dec(v___x_89_);
lean_dec_ref(v___y_74_);
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
lean_inc(v___y_77_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_77_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_array_get_size(v_constants_96_);
v___x_100_ = l_Array_toSubarray___redArg(v_constants_96_, v___y_77_, v___x_99_);
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
lean_object* v_a_106_; lean_object* v_fst_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v_fst_107_ = lean_ctor_get(v_a_106_, 0);
lean_inc(v_fst_107_);
lean_dec(v_a_106_);
lean_inc(v_a_87_);
v___x_108_ = lean_elab_environment_to_kernel_env(v_a_87_);
v___x_109_ = l_Lean_Kernel_Environment_replay(v_fst_107_, v___x_108_);
lean_dec(v_fst_107_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_110_; 
lean_dec_ref_known(v___x_109_, 1);
v___x_110_ = lean_environment_free_regions(v_a_87_);
return v___x_110_;
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
lean_dec(v_a_87_);
v_a_111_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_109_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_109_);
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
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
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
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v___x_82_;
}
}
v___jp_138_:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_readModuleDataParts(v_fnames_139_);
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
v___y_71_ = v___x_151_;
v___y_72_ = v___x_147_;
v___y_73_ = v_fst_149_;
v___y_74_ = v_a_141_;
v___y_75_ = v___x_145_;
v___y_76_ = v___x_150_;
v___y_77_ = v___x_146_;
v___y_78_ = v___x_69_;
goto v___jp_70_;
}
else
{
v___y_71_ = v___x_151_;
v___y_72_ = v___x_147_;
v___y_73_ = v_fst_149_;
v___y_74_ = v_a_141_;
v___y_75_ = v___x_145_;
v___y_76_ = v___x_150_;
v___y_77_ = v___x_146_;
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
v___x_205_ = l_Lean_mkEmptyEnvironment(v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; lean_object* v_map_u2081_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
v___x_207_ = l_Lean_Environment_constants(v_env_202_);
v_map_u2081_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_map_u2081_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = lean_elab_environment_to_kernel_env(v_a_206_);
v___x_210_ = l_Lean_Kernel_Environment_replay(v_map_u2081_208_, v___x_209_);
lean_dec_ref(v_map_u2081_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_210_, 0);
lean_dec(v_unused_219_);
v___x_212_ = v___x_210_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_dec(v___x_210_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_box(0);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_a_220_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_210_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_210_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_env_202_);
v_a_228_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_205_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_205_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* v_env_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_replayFromFresh___lam__0(v_env_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object* v_module_240_){
_start:
{
lean_object* v___f_242_; uint8_t v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint32_t v___x_250_; lean_object* v___x_251_; 
v___f_242_ = ((lean_object*)(l_replayFromFresh___closed__0));
v___x_243_ = 0;
v___x_244_ = 1;
v___x_245_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_245_, 0, v_module_240_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1 + 1, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1 + 2, v___x_243_);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_mk_empty_array_with_capacity(v___x_246_);
v___x_248_ = lean_array_push(v___x_247_, v___x_245_);
v___x_249_ = l_Lean_Options_empty;
v___x_250_ = 0;
v___x_251_ = l_Lean_withImportModules___redArg(v___x_248_, v___x_249_, v___f_242_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* v_module_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_replayFromFresh(v_module_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_getCurrentModule(){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_getCurrentModule___closed__0));
v___x_258_ = l_Lake_Manifest_load_x3f(v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_273_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_273_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_273_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_273_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
if (lean_obj_tag(v_a_259_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_object* v_val_267_; lean_object* v_name_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v_val_267_ = lean_ctor_get(v_a_259_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_a_259_, 1);
v_name_268_ = lean_ctor_get(v_val_267_, 0);
lean_inc(v_name_268_);
lean_dec(v_val_267_);
v___x_269_ = l_Lean_Name_capitalize(v_name_268_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_269_);
v___x_271_ = v___x_261_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_258_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_258_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_getCurrentModule();
return v_res_283_;
}
}
static lean_object* _init_l_List_partition_loop___at___00main_spec__0___closed__1(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_286_ = lean_string_utf8_byte_size(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
if (lean_obj_tag(v_a_287_) == 0)
{
lean_object* v_fst_289_; lean_object* v_snd_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_299_; 
v_fst_289_ = lean_ctor_get(v_a_288_, 0);
v_snd_290_ = lean_ctor_get(v_a_288_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_299_ == 0)
{
v___x_292_ = v_a_288_;
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_snd_290_);
lean_inc(v_fst_289_);
lean_dec(v_a_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_294_ = l_List_reverse___redArg(v_fst_289_);
v___x_295_ = l_List_reverse___redArg(v_snd_290_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_295_);
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_head_300_; lean_object* v_tail_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_328_; 
v_head_300_ = lean_ctor_get(v_a_287_, 0);
v_tail_301_ = lean_ctor_get(v_a_287_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_328_ == 0)
{
v___x_303_ = v_a_287_;
v_isShared_304_ = v_isSharedCheck_328_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_tail_301_);
lean_inc(v_head_300_);
lean_dec(v_a_287_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_328_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_327_; 
v_fst_305_ = lean_ctor_get(v_a_288_, 0);
v_snd_306_ = lean_ctor_get(v_a_288_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_327_ == 0)
{
v___x_308_ = v_a_288_;
v_isShared_309_ = v_isSharedCheck_327_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snd_306_);
lean_inc(v_fst_305_);
lean_dec(v_a_288_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_327_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_319_ = lean_string_utf8_byte_size(v_head_300_);
v___x_320_ = lean_obj_once(&l_List_partition_loop___at___00main_spec__0___closed__1, &l_List_partition_loop___at___00main_spec__0___closed__1_once, _init_l_List_partition_loop___at___00main_spec__0___closed__1);
v___x_321_ = lean_nat_dec_le(v___x_320_, v___x_319_);
if (v___x_321_ == 0)
{
goto v___jp_310_;
}
else
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_string_memcmp(v_head_300_, v___x_318_, v___x_322_, v___x_322_, v___x_320_);
if (v___x_323_ == 0)
{
goto v___jp_310_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_del_object(v___x_308_);
lean_del_object(v___x_303_);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v_head_300_);
lean_ctor_set(v___x_324_, 1, v_fst_305_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_snd_306_);
v_a_287_ = v_tail_301_;
v_a_288_ = v___x_325_;
goto _start;
}
}
v___jp_310_:
{
lean_object* v___x_312_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_snd_306_);
v___x_312_ = v___x_303_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_head_300_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_snd_306_);
v___x_312_ = v_reuseFailAlloc_317_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_312_);
v___x_314_ = v___x_308_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_fst_305_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_316_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
v_a_287_ = v_tail_301_;
v_a_288_ = v___x_314_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(lean_object* v_head_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_replayFromImports(v_head_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set_tag(v___x_334_, 1);
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_331_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_331_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 0);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed(lean_object* v_head_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(v_head_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v_as_x27_351_, lean_object* v_b_352_){
_start:
{
if (lean_obj_tag(v_as_x27_351_) == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v_b_352_);
return v___x_354_;
}
else
{
lean_object* v_head_355_; lean_object* v_tail_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_head_355_ = lean_ctor_get(v_as_x27_351_, 0);
v_tail_356_ = lean_ctor_get(v_as_x27_351_, 1);
lean_inc_n(v_head_355_, 2);
v___f_357_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_357_, 0, v_head_355_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_io_as_task(v___f_357_, v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_head_355_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_array_push(v_b_352_, v___x_360_);
v_as_x27_351_ = v_tail_356_;
v_b_352_ = v___x_361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v_as_x27_363_, lean_object* v_b_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_363_, v_b_364_);
lean_dec(v_as_x27_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l_List_reverse___redArg(v_x_369_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
else
{
lean_object* v_head_373_; lean_object* v_tail_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_388_; 
v_head_373_ = lean_ctor_get(v_x_368_, 0);
v_tail_374_ = lean_ctor_get(v_x_368_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_388_ == 0)
{
v___x_376_ = v_x_368_;
v_isShared_377_ = v_isSharedCheck_388_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_tail_374_);
lean_inc(v_head_373_);
lean_dec(v_x_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_388_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
lean_inc(v_head_373_);
v___x_378_ = l_String_toName(v_head_373_);
v___x_379_ = l_Lean_Name_isAnonymous(v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_head_373_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v_x_369_);
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_x_369_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
v_x_368_ = v_tail_374_;
v_x_369_ = v___x_381_;
goto _start;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v___x_378_);
lean_del_object(v___x_376_);
lean_dec(v_tail_374_);
lean_dec(v_x_369_);
v___x_384_ = ((lean_object*)(l_List_mapM_loop___at___00main_spec__6___closed__0));
v___x_385_ = lean_string_append(v___x_384_, v_head_373_);
lean_dec(v_head_373_);
v___x_386_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6___boxed(lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_List_mapM_loop___at___00main_spec__6(v_x_389_, v_x_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg(uint8_t v___y_395_, lean_object* v_as_x27_396_, lean_object* v_b_397_){
_start:
{
if (lean_obj_tag(v_as_x27_396_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_b_397_);
return v___x_399_;
}
else
{
lean_object* v_head_400_; lean_object* v_tail_401_; lean_object* v___x_402_; 
v_head_400_ = lean_ctor_get(v_as_x27_396_, 0);
v_tail_401_ = lean_ctor_get(v_as_x27_396_, 1);
v___x_402_ = lean_box(0);
if (v___y_395_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_406_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(v_head_400_);
v___x_407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_400_, v___y_395_);
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
lean_dec_ref(v___x_407_);
v___x_409_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1));
v___x_410_ = lean_string_append(v___x_408_, v___x_409_);
v___x_411_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref_known(v___x_411_, 1);
goto v___jp_403_;
}
else
{
return v___x_411_;
}
}
v___jp_403_:
{
lean_object* v___x_404_; 
lean_inc(v_head_400_);
v___x_404_ = l_replayFromFresh(v_head_400_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_dec_ref_known(v___x_404_, 1);
v_as_x27_396_ = v_tail_401_;
v_b_397_ = v___x_402_;
goto _start;
}
else
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(lean_object* v___y_412_, lean_object* v_as_x27_413_, lean_object* v_b_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___y_5439__boxed_416_; lean_object* v_res_417_; 
v___y_5439__boxed_416_ = lean_unbox(v___y_412_);
v_res_417_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_5439__boxed_416_, v_as_x27_413_, v_b_414_);
lean_dec(v_as_x27_413_);
return v_res_417_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0(void){
_start:
{
lean_object* v___x_418_; lean_object* v___f_419_; 
v___x_418_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_419_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_419_, 0, v___x_418_);
return v___f_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v_val_421_, lean_object* v_a_422_, lean_object* v_fst_423_, lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_){
_start:
{
lean_object* v_a_430_; uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec(v_fst_423_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v_b_427_);
return v___x_435_;
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_array_uget_borrowed(v_as_424_, v_i_426_);
lean_inc(v_a_436_);
v___x_437_ = l_Lean_searchModuleNameOfFileName(v_a_436_, v_val_421_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___y_440_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
if (lean_obj_tag(v_a_438_) == 1)
{
lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_461_; 
v_fst_443_ = lean_ctor_get(v_b_427_, 0);
v_snd_444_ = lean_ctor_get(v_b_427_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_b_427_);
if (v_isSharedCheck_461_ == 0)
{
v___x_446_ = v_b_427_;
v_isShared_447_ = v_isSharedCheck_461_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snd_444_);
lean_inc(v_fst_443_);
lean_dec(v_b_427_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_461_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_val_448_; lean_object* v___f_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_val_448_ = lean_ctor_get(v_a_438_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v_a_438_, 1);
v___f_457_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
lean_inc(v_fst_423_);
v___x_459_ = l_List_elem___redArg(v___f_457_, v___x_458_, v_fst_423_);
if (v___x_459_ == 0)
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_Name_isPrefixOf(v_a_422_, v_val_448_);
if (v___x_460_ == 0)
{
goto v___jp_452_;
}
else
{
lean_del_object(v___x_446_);
lean_dec(v_snd_444_);
goto v___jp_449_;
}
}
else
{
goto v___jp_452_;
}
v___jp_449_:
{
uint8_t v___x_450_; 
v___x_450_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v_val_448_, v_fst_443_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v_val_448_);
lean_ctor_set(v___x_451_, 1, v_fst_443_);
v___y_440_ = v___x_451_;
goto v___jp_439_;
}
else
{
lean_dec(v_val_448_);
v___y_440_ = v_fst_443_;
goto v___jp_439_;
}
}
v___jp_452_:
{
uint8_t v___x_453_; 
v___x_453_ = lean_name_eq(v_a_422_, v_val_448_);
if (v___x_453_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v_val_448_);
if (v_isShared_447_ == 0)
{
v___x_455_ = v___x_446_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_fst_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_snd_444_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v_a_430_ = v___x_455_;
goto v___jp_429_;
}
}
else
{
lean_del_object(v___x_446_);
lean_dec(v_snd_444_);
goto v___jp_449_;
}
}
}
}
else
{
lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_438_);
v_fst_462_ = lean_ctor_get(v_b_427_, 0);
v_snd_463_ = lean_ctor_get(v_b_427_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_b_427_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v_b_427_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_snd_463_);
lean_inc(v_fst_462_);
lean_dec(v_b_427_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_fst_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v_a_430_ = v___x_468_;
goto v___jp_429_;
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(v___x_434_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v_a_430_ = v___x_442_;
goto v___jp_429_;
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_b_427_);
lean_dec(v_fst_423_);
v_a_471_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_437_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_437_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
v___jp_429_:
{
size_t v___x_431_; size_t v___x_432_; 
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_add(v_i_426_, v___x_431_);
v_i_426_ = v___x_432_;
v_b_427_ = v_a_430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v_val_479_, lean_object* v_a_480_, lean_object* v_fst_481_, lean_object* v_as_482_, lean_object* v_sz_483_, lean_object* v_i_484_, lean_object* v_b_485_, lean_object* v___y_486_){
_start:
{
size_t v_sz_boxed_487_; size_t v_i_boxed_488_; lean_object* v_res_489_; 
v_sz_boxed_487_ = lean_unbox_usize(v_sz_483_);
lean_dec(v_sz_483_);
v_i_boxed_488_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_res_489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_val_479_, v_a_480_, v_fst_481_, v_as_482_, v_sz_boxed_487_, v_i_boxed_488_, v_b_485_);
lean_dec_ref(v_as_482_);
lean_dec(v_a_480_);
lean_dec(v_val_479_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_val_492_, lean_object* v_fst_493_, lean_object* v_as_x27_494_, lean_object* v_b_495_){
_start:
{
if (lean_obj_tag(v_as_x27_494_) == 0)
{
lean_object* v___x_497_; 
lean_dec(v_fst_493_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v_b_495_);
return v___x_497_;
}
else
{
lean_object* v_head_498_; lean_object* v_tail_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_head_498_ = lean_ctor_get(v_as_x27_494_, 0);
v_tail_499_ = lean_ctor_get(v_as_x27_494_, 1);
v___x_500_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0));
v___x_501_ = l_Lean_SearchPath_findAllWithExt(v_val_492_, v___x_500_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = 0;
v___x_504_ = lean_box(v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v_b_495_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v_sz_506_ = lean_array_size(v_a_502_);
v___x_507_ = ((size_t)0ULL);
lean_inc(v_fst_493_);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_val_492_, v_head_498_, v_fst_493_, v_a_502_, v_sz_506_, v___x_507_, v___x_505_);
lean_dec(v_a_502_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_525_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_525_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_snd_513_; uint8_t v___x_514_; 
v_snd_513_ = lean_ctor_get(v_a_509_, 1);
v___x_514_ = lean_unbox(v_snd_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec(v_a_509_);
lean_dec(v_fst_493_);
v___x_515_ = 1;
v___x_516_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1));
lean_inc(v_head_498_);
v___x_517_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_498_, v___x_515_);
v___x_518_ = lean_string_append(v___x_516_, v___x_517_);
lean_dec_ref(v___x_517_);
v___x_519_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 1);
lean_ctor_set(v___x_511_, 0, v___x_519_);
v___x_521_ = v___x_511_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
lean_object* v_fst_523_; 
lean_del_object(v___x_511_);
v_fst_523_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_fst_523_);
lean_dec(v_a_509_);
v_as_x27_494_ = v_tail_499_;
v_b_495_ = v_fst_523_;
goto _start;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_fst_493_);
v_a_526_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_508_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_508_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_b_495_);
lean_dec(v_fst_493_);
v_a_534_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_501_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_501_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_val_542_, lean_object* v_fst_543_, lean_object* v_as_x27_544_, lean_object* v_b_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_val_542_, v_fst_543_, v_as_x27_544_, v_b_545_);
lean_dec(v_as_x27_544_);
lean_dec(v_val_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(uint8_t v___y_549_, lean_object* v_as_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_b_553_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v_b_553_);
return v___x_556_;
}
else
{
lean_object* v_a_557_; lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_560_; 
v_a_557_ = lean_array_uget_borrowed(v_as_550_, v_i_552_);
v_fst_558_ = lean_ctor_get(v_a_557_, 0);
v_snd_559_ = lean_ctor_get(v_a_557_, 1);
v___x_560_ = lean_box(0);
if (v___y_549_ == 0)
{
goto v___jp_561_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(v_fst_558_);
v___x_580_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_558_, v___y_549_);
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_dec_ref_known(v___x_582_, 1);
goto v___jp_561_;
}
else
{
return v___x_582_;
}
}
v___jp_561_:
{
lean_object* v___x_562_; 
lean_inc(v_snd_559_);
v___x_562_ = lean_task_get_own(v_snd_559_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0));
lean_inc(v_fst_558_);
v___x_565_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_558_, v___x_555_);
v___x_566_ = lean_string_append(v___x_564_, v___x_565_);
lean_dec_ref(v___x_565_);
v___x_567_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_566_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v___x_567_, 0);
lean_dec(v_unused_575_);
v___x_569_ = v___x_567_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_dec(v___x_567_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 1);
lean_ctor_set(v___x_569_, 0, v_a_563_);
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_563_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
lean_dec(v_a_563_);
return v___x_567_;
}
}
else
{
size_t v___x_576_; size_t v___x_577_; 
lean_dec(v___x_562_);
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_add(v_i_552_, v___x_576_);
v_i_552_ = v___x_577_;
v_b_553_ = v___x_560_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___boxed(lean_object* v___y_583_, lean_object* v_as_584_, lean_object* v_sz_585_, lean_object* v_i_586_, lean_object* v_b_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___y_5687__boxed_589_; size_t v_sz_boxed_590_; size_t v_i_boxed_591_; lean_object* v_res_592_; 
v___y_5687__boxed_589_ = lean_unbox(v___y_583_);
v_sz_boxed_590_ = lean_unbox_usize(v_sz_585_);
lean_dec(v_sz_585_);
v_i_boxed_591_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_5687__boxed_589_, v_as_584_, v_sz_boxed_590_, v_i_boxed_591_, v_b_587_);
lean_dec_ref(v_as_584_);
return v_res_592_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_601_; lean_object* v___x_602_; 
v___x_601_ = 0;
v___x_602_ = lean_box_uint32(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_603_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_main___closed__0));
v___x_609_ = l_Lean_findSysroot(v___x_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v___x_611_ = lean_box(0);
v___x_612_ = l_Lean_initSearchPath(v_a_610_, v___x_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref_known(v___x_612_, 1);
v___x_613_ = ((lean_object*)(l_main___closed__1));
v___x_614_ = l_List_partition_loop___at___00main_spec__0(v_args_603_, v___x_613_);
v_fst_615_ = lean_ctor_get(v___x_614_, 0);
v_snd_616_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_714_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_714_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_714_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___f_620_; uint8_t v___y_622_; lean_object* v_targets_623_; uint8_t v___y_686_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___f_620_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_710_ = ((lean_object*)(l_main___closed__4));
lean_inc(v_fst_615_);
v___x_711_ = l_List_elem___redArg(v___f_620_, v___x_710_, v_fst_615_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = ((lean_object*)(l_main___closed__5));
lean_inc(v_fst_615_);
v___x_713_ = l_List_elem___redArg(v___f_620_, v___x_712_, v_fst_615_);
v___y_686_ = v___x_713_;
goto v___jp_685_;
}
else
{
v___y_686_ = v___x_711_;
goto v___jp_685_;
}
v___jp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = l_Lean_searchPathRef;
v___x_625_ = lean_st_ref_get(v___x_624_);
lean_inc(v_fst_615_);
v___x_626_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_625_, v_fst_615_, v_targets_623_, v___x_611_);
lean_dec(v_targets_623_);
lean_dec(v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_676_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_676_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_676_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_676_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
v___x_632_ = l_List_elem___redArg(v___f_620_, v___x_631_, v_fst_615_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_del_object(v___x_629_);
v___x_633_ = ((lean_object*)(l_main___closed__2));
v___x_634_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_a_627_, v___x_633_);
lean_dec(v_a_627_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; size_t v_sz_637_; size_t v___x_638_; lean_object* v___x_639_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = lean_box(0);
v_sz_637_ = lean_array_size(v_a_635_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_622_, v_a_635_, v_sz_637_, v___x_638_, v___x_636_);
lean_dec(v_a_635_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
goto v___jp_605_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_634_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_634_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = l_List_lengthTR___redArg(v_a_627_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_dec_eq(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_659_ = ((lean_object*)(l_main___closed__3));
v___x_660_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_627_);
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
lean_dec_ref(v___x_660_);
v___x_662_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 1);
lean_ctor_set(v___x_629_, 0, v___x_662_);
v___x_664_ = v___x_629_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_del_object(v___x_629_);
v___x_666_ = lean_box(0);
v___x_667_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_622_, v_a_627_, v___x_666_);
lean_dec(v_a_627_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_dec_ref_known(v___x_667_, 1);
goto v___jp_605_;
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_fst_615_);
v_a_677_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_626_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_626_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
v___jp_685_:
{
if (lean_obj_tag(v_snd_616_) == 0)
{
lean_object* v___x_687_; 
v___x_687_ = l_getCurrentModule();
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 1);
lean_ctor_set(v___x_618_, 1, v___x_611_);
lean_ctor_set(v___x_618_, 0, v_a_688_);
v___x_690_ = v___x_618_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_688_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_611_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_622_ = v___y_686_;
v_targets_623_ = v___x_690_;
goto v___jp_621_;
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_del_object(v___x_618_);
lean_dec(v_fst_615_);
v_a_692_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_687_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_687_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_700_; 
lean_del_object(v___x_618_);
v___x_700_ = l_List_mapM_loop___at___00main_spec__6(v_snd_616_, v___x_611_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___y_622_ = v___y_686_;
v_targets_623_ = v_a_701_;
goto v___jp_621_;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_fst_615_);
v_a_702_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_700_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_args_603_);
v_a_715_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_612_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_612_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_args_603_);
v_a_723_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_609_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_609_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
v___jp_605_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = l_main___boxed__const__1;
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = _lean_main(v_args_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_val_734_, lean_object* v_fst_735_, lean_object* v_as_736_, lean_object* v_as_x27_737_, lean_object* v_b_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_val_734_, v_fst_735_, v_as_x27_737_, v_b_738_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_val_742_, lean_object* v_fst_743_, lean_object* v_as_744_, lean_object* v_as_x27_745_, lean_object* v_b_746_, lean_object* v_a_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_List_forIn_x27_loop___at___00main_spec__2(v_val_742_, v_fst_743_, v_as_744_, v_as_x27_745_, v_b_746_, v_a_747_);
lean_dec(v_as_x27_745_);
lean_dec(v_as_744_);
lean_dec(v_val_742_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_750_, lean_object* v_as_x27_751_, lean_object* v_b_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_751_, v_b_752_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_756_, lean_object* v_as_x27_757_, lean_object* v_b_758_, lean_object* v_a_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_756_, v_as_x27_757_, v_b_758_, v_a_759_);
lean_dec(v_as_x27_757_);
lean_dec(v_as_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5(uint8_t v___y_762_, lean_object* v_as_763_, lean_object* v_as_x27_764_, lean_object* v_b_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_762_, v_as_x27_764_, v_b_765_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___boxed(lean_object* v___y_769_, lean_object* v_as_770_, lean_object* v_as_x27_771_, lean_object* v_b_772_, lean_object* v_a_773_, lean_object* v___y_774_){
_start:
{
uint8_t v___y_6062__boxed_775_; lean_object* v_res_776_; 
v___y_6062__boxed_775_ = lean_unbox(v___y_769_);
v_res_776_ = l_List_forIn_x27_loop___at___00main_spec__5(v___y_6062__boxed_775_, v_as_770_, v_as_x27_771_, v_b_772_, v_a_773_);
lean_dec(v_as_x27_771_);
lean_dec(v_as_770_);
return v_res_776_;
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
