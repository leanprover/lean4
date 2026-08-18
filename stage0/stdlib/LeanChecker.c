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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
lean_object* l_Lean_Name_capitalize(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_Kernel_Environment_replay(lean_object*, lean_object*);
lean_object* lean_environment_free_regions(lean_object*);
lean_object* l_Lean_readModuleDataParts(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
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
static lean_object* l_replayFromImports___closed__1;
static lean_once_cell_t l_replayFromImports___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_replayFromImports___closed__2;
static const lean_string_object l_replayFromImports___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to read module data"};
static const lean_object* l_replayFromImports___closed__3 = (const lean_object*)&l_replayFromImports___closed__3_value;
static const lean_ctor_object l_replayFromImports___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_replayFromImports___closed__3_value)}};
static const lean_object* l_replayFromImports___closed__4 = (const lean_object*)&l_replayFromImports___closed__4_value;
static const lean_string_object l_replayFromImports___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "object file '"};
static const lean_object* l_replayFromImports___closed__5 = (const lean_object*)&l_replayFromImports___closed__5_value;
static const lean_string_object l_replayFromImports___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "' of module "};
static const lean_object* l_replayFromImports___closed__6 = (const lean_object*)&l_replayFromImports___closed__6_value;
static const lean_string_object l_replayFromImports___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " does not exist"};
static const lean_object* l_replayFromImports___closed__7 = (const lean_object*)&l_replayFromImports___closed__7_value;
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
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "replaying "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " with --fresh"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00main_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Could not resolve module: "};
static const lean_object* l_List_mapM_loop___at___00main_spec__6___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00main_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_snd_8_; lean_object* v_fst_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_103_; 
v_snd_8_ = lean_ctor_get(v_b_4_, 1);
v_fst_9_ = lean_ctor_get(v_b_4_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_b_4_);
if (v_isSharedCheck_103_ == 0)
{
v___x_11_ = v_b_4_;
v_isShared_12_ = v_isSharedCheck_103_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_snd_8_);
lean_inc(v_fst_9_);
lean_dec(v_b_4_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_103_;
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
lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_99_; 
lean_inc(v_stop_15_);
lean_inc(v_start_14_);
lean_inc_ref(v_array_13_);
v_isSharedCheck_99_ = !lean_is_exclusive(v_snd_8_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_100_ = lean_ctor_get(v_snd_8_, 2);
lean_dec(v_unused_100_);
v_unused_101_ = lean_ctor_get(v_snd_8_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_snd_8_, 0);
lean_dec(v_unused_102_);
v___x_22_ = v_snd_8_;
v_isShared_23_ = v_isSharedCheck_99_;
goto v_resetjp_21_;
}
else
{
lean_dec(v_snd_8_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_99_;
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
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_array_13_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_stop_15_);
v___x_29_ = v_reuseFailAlloc_98_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___y_31_; lean_object* v___y_39_; lean_object* v_i_40_; lean_object* v___y_55_; lean_object* v_i_56_; lean_object* v___y_61_; lean_object* v___x_70_; 
v___x_70_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4_spec__7___redArg(v_fst_9_, v_a_24_);
switch(lean_obj_tag(v___x_70_))
{
case 0:
{
lean_object* v_index_71_; lean_object* v_size_72_; lean_object* v___x_73_; 
v_index_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_index_71_);
lean_dec_ref_known(v___x_70_, 3);
v_size_72_ = lean_ctor_get(v_fst_9_, 0);
lean_inc(v_size_72_);
lean_inc(v_a_24_);
v___x_73_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_9_, v_size_72_, v_index_71_, v_a_24_, v___x_25_);
lean_dec(v_index_71_);
v___y_31_ = v___x_73_;
goto v___jp_30_;
}
case 1:
{
lean_object* v_index_74_; lean_object* v_size_75_; lean_object* v_keyArray_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_index_74_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_index_74_);
lean_dec_ref_known(v___x_70_, 1);
v_size_75_ = lean_ctor_get(v_fst_9_, 0);
v_keyArray_76_ = lean_ctor_get(v_fst_9_, 1);
v___x_77_ = lean_nat_add(v_size_75_, v___x_26_);
v___x_78_ = lean_array_get_size(v_keyArray_76_);
v___x_79_ = lean_nat_dec_lt(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_dec(v___x_77_);
lean_dec(v_index_74_);
goto v___jp_44_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_80_ = lean_unsigned_to_nat(4u);
v___x_81_ = lean_nat_mul(v___x_77_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(3u);
v___x_83_ = lean_nat_mul(v___x_78_, v___x_82_);
v___x_84_ = lean_nat_dec_le(v___x_81_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_81_);
if (v___x_84_ == 0)
{
lean_dec(v___x_77_);
lean_dec(v_index_74_);
goto v___jp_44_;
}
else
{
lean_object* v___x_85_; 
lean_inc(v_a_24_);
v___x_85_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_9_, v___x_77_, v_index_74_, v_a_24_, v___x_25_);
lean_dec(v_index_74_);
v___y_31_ = v___x_85_;
goto v___jp_30_;
}
}
}
default: 
{
lean_object* v_size_86_; lean_object* v_keyArray_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_size_86_ = lean_ctor_get(v_fst_9_, 0);
v_keyArray_87_ = lean_ctor_get(v_fst_9_, 1);
v___x_88_ = lean_nat_add(v_size_86_, v___x_26_);
v___x_89_ = lean_array_get_size(v_keyArray_87_);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v___x_88_);
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_9_);
lean_dec(v_fst_9_);
v___y_61_ = v___x_91_;
goto v___jp_60_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_92_ = lean_unsigned_to_nat(4u);
v___x_93_ = lean_nat_mul(v___x_88_, v___x_92_);
lean_dec(v___x_88_);
v___x_94_ = lean_unsigned_to_nat(3u);
v___x_95_ = lean_nat_mul(v___x_89_, v___x_94_);
v___x_96_ = lean_nat_dec_le(v___x_93_, v___x_95_);
lean_dec(v___x_95_);
lean_dec(v___x_93_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_9_);
lean_dec(v_fst_9_);
v___y_61_ = v___x_97_;
goto v___jp_60_;
}
else
{
v___y_61_ = v_fst_9_;
goto v___jp_60_;
}
}
}
}
v___jp_30_:
{
lean_object* v___x_33_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___x_29_);
lean_ctor_set(v___x_11_, 0, v___y_31_);
v___x_33_ = v___x_11_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___y_31_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_29_);
v___x_33_ = v_reuseFailAlloc_37_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
size_t v___x_34_; size_t v___x_35_; 
v___x_34_ = ((size_t)1ULL);
v___x_35_ = lean_usize_add(v_i_3_, v___x_34_);
v_i_3_ = v___x_35_;
v_b_4_ = v___x_33_;
goto _start;
}
}
v___jp_38_:
{
lean_object* v_size_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_size_41_ = lean_ctor_get(v___y_39_, 0);
v___x_42_ = lean_nat_add(v_size_41_, v___x_26_);
lean_inc(v_a_24_);
v___x_43_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_39_, v___x_42_, v_i_40_, v_a_24_, v___x_25_);
lean_dec(v_i_40_);
v___y_31_ = v___x_43_;
goto v___jp_30_;
}
v___jp_44_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_9_);
lean_dec(v_fst_9_);
v___x_46_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4_spec__7___redArg(v___x_45_, v_a_24_);
switch(lean_obj_tag(v___x_46_))
{
case 0:
{
lean_object* v_index_47_; lean_object* v_size_48_; lean_object* v___x_49_; 
v_index_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_index_47_);
lean_dec_ref_known(v___x_46_, 3);
v_size_48_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_size_48_);
lean_inc(v_a_24_);
v___x_49_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_45_, v_size_48_, v_index_47_, v_a_24_, v___x_25_);
lean_dec(v_index_47_);
v___y_31_ = v___x_49_;
goto v___jp_30_;
}
case 1:
{
lean_object* v_index_50_; 
v_index_50_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_index_50_);
lean_dec_ref_known(v___x_46_, 1);
v___y_39_ = v___x_45_;
v_i_40_ = v_index_50_;
goto v___jp_38_;
}
default: 
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_45_, v___x_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_index_53_; 
v_index_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_index_53_);
lean_dec_ref_known(v___x_52_, 1);
v___y_39_ = v___x_45_;
v_i_40_ = v_index_53_;
goto v___jp_38_;
}
else
{
lean_dec(v___x_25_);
v___y_31_ = v___x_45_;
goto v___jp_30_;
}
}
}
}
v___jp_54_:
{
lean_object* v_size_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_size_57_ = lean_ctor_get(v___y_55_, 0);
v___x_58_ = lean_nat_add(v_size_57_, v___x_26_);
lean_inc(v_a_24_);
v___x_59_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_55_, v___x_58_, v_i_56_, v_a_24_, v___x_25_);
lean_dec(v_i_56_);
v___y_31_ = v___x_59_;
goto v___jp_30_;
}
v___jp_60_:
{
lean_object* v___x_62_; 
v___x_62_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4_spec__7___redArg(v___y_61_, v_a_24_);
switch(lean_obj_tag(v___x_62_))
{
case 0:
{
lean_object* v_index_63_; lean_object* v_size_64_; lean_object* v___x_65_; 
v_index_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_index_63_);
lean_dec_ref_known(v___x_62_, 3);
v_size_64_ = lean_ctor_get(v___y_61_, 0);
lean_inc(v_size_64_);
lean_inc(v_a_24_);
v___x_65_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_61_, v_size_64_, v_index_63_, v_a_24_, v___x_25_);
lean_dec(v_index_63_);
v___y_31_ = v___x_65_;
goto v___jp_30_;
}
case 1:
{
lean_object* v_index_66_; 
v_index_66_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_index_66_);
lean_dec_ref_known(v___x_62_, 1);
v___y_55_ = v___y_61_;
v_i_56_ = v_index_66_;
goto v___jp_54_;
}
default: 
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_61_, v___x_67_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_index_69_; 
v_index_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_index_69_);
lean_dec_ref_known(v___x_68_, 1);
v___y_55_ = v___y_61_;
v_i_56_ = v_index_69_;
goto v___jp_54_;
}
else
{
lean_dec(v___x_25_);
v___y_31_ = v___y_61_;
goto v___jp_30_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(lean_object* v_as_104_, lean_object* v_sz_105_, lean_object* v_i_106_, lean_object* v_b_107_, lean_object* v___y_108_){
_start:
{
size_t v_sz_boxed_109_; size_t v_i_boxed_110_; lean_object* v_res_111_; 
v_sz_boxed_109_ = lean_unbox_usize(v_sz_105_);
lean_dec(v_sz_105_);
v_i_boxed_110_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_as_104_, v_sz_boxed_109_, v_i_boxed_110_, v_b_107_);
lean_dec_ref(v_as_104_);
return v_res_111_;
}
}
static lean_object* _init_l_replayFromImports___closed__0(void){
_start:
{
lean_object* v_cellCount_112_; lean_object* v___x_113_; 
v_cellCount_112_ = lean_unsigned_to_nat(16u);
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_112_);
return v___x_113_;
}
}
static lean_object* _init_l_replayFromImports___closed__1(void){
_start:
{
lean_object* v_cellCount_114_; lean_object* v___x_115_; 
v_cellCount_114_ = lean_unsigned_to_nat(16u);
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_114_);
return v___x_115_;
}
}
static uint8_t _init_l_replayFromImports___closed__2(void){
_start:
{
uint8_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = 2;
v___x_117_ = l_Lean_instOrdOLeanLevel_ord(v___x_116_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_replayFromImports(lean_object* v_module_124_){
_start:
{
lean_object* v___x_126_; 
lean_inc(v_module_124_);
v___x_126_ = l_Lean_findOLean(v_module_124_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_253_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_253_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_253_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_253_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
uint8_t v___x_131_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; uint8_t v___y_137_; uint8_t v___y_138_; lean_object* v___y_139_; uint8_t v___y_140_; lean_object* v_fnames_202_; 
v___x_131_ = l_System_FilePath_pathExists(v_a_127_);
if (v___x_131_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_229_ = ((lean_object*)(l_replayFromImports___closed__5));
v___x_230_ = lean_string_append(v___x_229_, v_a_127_);
lean_dec(v_a_127_);
v___x_231_ = ((lean_object*)(l_replayFromImports___closed__6));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
v___x_233_ = 1;
v___x_234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_124_, v___x_233_);
v___x_235_ = lean_string_append(v___x_232_, v___x_234_);
lean_dec_ref(v___x_234_);
v___x_236_ = ((lean_object*)(l_replayFromImports___closed__7));
v___x_237_ = lean_string_append(v___x_235_, v___x_236_);
v___x_238_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 1);
lean_ctor_set(v___x_129_, 0, v___x_238_);
v___x_240_ = v___x_129_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
lean_del_object(v___x_129_);
lean_dec(v_module_124_);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
lean_inc_n(v_a_127_, 2);
v___x_244_ = lean_array_push(v___x_243_, v_a_127_);
v___x_245_ = 1;
v___x_246_ = l_Lean_OLeanLevel_adjustFileName(v_a_127_, v___x_245_);
v___x_247_ = l_System_FilePath_pathExists(v___x_246_);
if (v___x_247_ == 0)
{
lean_dec_ref(v___x_246_);
lean_dec(v_a_127_);
v_fnames_202_ = v___x_244_;
goto v___jp_201_;
}
else
{
uint8_t v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; 
v___x_248_ = 2;
v___x_249_ = l_Lean_OLeanLevel_adjustFileName(v_a_127_, v___x_248_);
v___x_250_ = l_System_FilePath_pathExists(v___x_249_);
v___x_251_ = lean_array_push(v___x_244_, v___x_246_);
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_249_);
v_fnames_202_ = v___x_251_;
goto v___jp_201_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_array_push(v___x_251_, v___x_249_);
v_fnames_202_ = v___x_252_;
goto v___jp_201_;
}
}
}
v___jp_132_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_imports_143_; lean_object* v___x_144_; 
v___x_141_ = l_Lean_instInhabitedImportState_default;
v___x_142_ = lean_st_mk_ref(v___x_141_);
v_imports_143_ = lean_ctor_get(v___y_133_, 0);
lean_inc_ref(v_imports_143_);
lean_dec_ref(v___y_133_);
lean_inc(v___y_136_);
v___x_144_ = l_Lean_importModulesCore(v_imports_143_, v___y_138_, v___y_136_, v___y_140_, v___y_137_, v___x_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; uint32_t v___x_147_; lean_object* v___x_148_; 
lean_dec_ref_known(v___x_144_, 1);
v___x_145_ = lean_st_ref_get(v___x_142_);
lean_dec(v___x_142_);
v___x_146_ = l_Lean_Options_empty;
v___x_147_ = 0;
v___x_148_ = l_Lean_finalizeImport(v___x_145_, v_imports_143_, v___x_146_, v___x_147_, v___y_137_, v___y_137_, v___y_138_, v___x_131_, v___y_137_);
lean_dec(v___x_145_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_fst_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_191_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_sub(v___y_134_, v___x_150_);
lean_dec(v___y_134_);
v___x_152_ = lean_array_fget(v___y_139_, v___x_151_);
lean_dec(v___x_151_);
lean_dec_ref(v___y_139_);
v_fst_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v___x_152_, 1);
lean_dec(v_unused_192_);
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_191_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_fst_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_191_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_constNames_157_; lean_object* v_constants_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v_constNames_157_ = lean_ctor_get(v_fst_153_, 1);
lean_inc_ref(v_constNames_157_);
v_constants_158_ = lean_ctor_get(v_fst_153_, 2);
lean_inc_ref(v_constants_158_);
lean_dec(v_fst_153_);
v___x_159_ = lean_obj_once(&l_replayFromImports___closed__0, &l_replayFromImports___closed__0_once, _init_l_replayFromImports___closed__0);
v___x_160_ = lean_obj_once(&l_replayFromImports___closed__1, &l_replayFromImports___closed__1_once, _init_l_replayFromImports___closed__1);
lean_inc(v___y_135_);
v___x_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_161_, 0, v___y_135_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
lean_ctor_set(v___x_161_, 2, v___x_160_);
v___x_162_ = lean_array_get_size(v_constants_158_);
v___x_163_ = l_Array_toSubarray___redArg(v_constants_158_, v___y_135_, v___x_162_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_163_);
lean_ctor_set(v___x_155_, 0, v___x_161_);
v___x_165_ = v___x_155_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_190_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
size_t v_sz_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_sz_166_ = lean_array_size(v_constNames_157_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_constNames_157_, v_sz_166_, v___x_167_, v___x_165_);
lean_dec_ref(v_constNames_157_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_fst_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_168_, 1);
v_fst_170_ = lean_ctor_get(v_a_169_, 0);
lean_inc(v_fst_170_);
lean_dec(v_a_169_);
lean_inc(v_a_149_);
v___x_171_ = lean_elab_environment_to_kernel_env(v_a_149_);
v___x_172_ = l_Lean_Kernel_Environment_replay(v_fst_170_, v___x_171_);
lean_dec(v_fst_170_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v___x_173_; 
lean_dec_ref_known(v___x_172_, 1);
v___x_173_ = lean_environment_free_regions(v_a_149_);
return v___x_173_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_a_149_);
v_a_174_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_172_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec(v_a_149_);
v_a_182_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_168_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_168_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v___y_139_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
v_a_193_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_148_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_148_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_dec_ref(v_imports_143_);
lean_dec(v___x_142_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
return v___x_144_;
}
}
v___jp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_readModuleDataParts(v_fnames_202_);
lean_dec_ref(v_fnames_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_220_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_220_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_220_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_220_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_208_ = lean_array_get_size(v_a_204_);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_nat_dec_eq(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v_fst_212_; uint8_t v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
lean_del_object(v___x_206_);
v___x_211_ = lean_array_fget_borrowed(v_a_204_, v___x_209_);
v_fst_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_fst_212_);
v___x_213_ = 2;
v___x_214_ = lean_box(1);
v___x_215_ = lean_uint8_once(&l_replayFromImports___closed__2, &l_replayFromImports___closed__2_once, _init_l_replayFromImports___closed__2);
if (v___x_215_ == 0)
{
v___y_133_ = v_fst_212_;
v___y_134_ = v___x_208_;
v___y_135_ = v___x_209_;
v___y_136_ = v___x_214_;
v___y_137_ = v___x_210_;
v___y_138_ = v___x_213_;
v___y_139_ = v_a_204_;
v___y_140_ = v___x_131_;
goto v___jp_132_;
}
else
{
v___y_133_ = v_fst_212_;
v___y_134_ = v___x_208_;
v___y_135_ = v___x_209_;
v___y_136_ = v___x_214_;
v___y_137_ = v___x_210_;
v___y_138_ = v___x_213_;
v___y_139_ = v_a_204_;
v___y_140_ = v___x_210_;
goto v___jp_132_;
}
}
else
{
lean_object* v___x_216_; lean_object* v___x_218_; 
lean_dec(v_a_204_);
v___x_216_ = ((lean_object*)(l_replayFromImports___closed__4));
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 1);
lean_ctor_set(v___x_206_, 0, v___x_216_);
v___x_218_ = v___x_206_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_203_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_203_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_module_124_);
v_a_254_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_126_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_126_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromImports___boxed(lean_object* v_module_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_replayFromImports(v_module_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0(lean_object* v_env_265_){
_start:
{
uint32_t v___x_267_; lean_object* v___x_268_; 
v___x_267_ = 0;
v___x_268_ = l_Lean_mkEmptyEnvironment(v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v_map_u2081_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = l_Lean_Environment_constants(v_env_265_);
v_map_u2081_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_map_u2081_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = lean_elab_environment_to_kernel_env(v_a_269_);
v___x_273_ = l_Lean_Kernel_Environment_replay(v_map_u2081_271_, v___x_272_);
lean_dec_ref(v_map_u2081_271_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_273_, 0);
lean_dec(v_unused_282_);
v___x_275_ = v___x_273_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_dec(v___x_273_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_box(0);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_273_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_env_265_);
v_a_291_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_268_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_268_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___lam__0___boxed(lean_object* v_env_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_replayFromFresh___lam__0(v_env_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh(lean_object* v_module_303_){
_start:
{
lean_object* v___f_305_; uint8_t v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint32_t v___x_313_; lean_object* v___x_314_; 
v___f_305_ = ((lean_object*)(l_replayFromFresh___closed__0));
v___x_306_ = 0;
v___x_307_ = 1;
v___x_308_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_308_, 0, v_module_303_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1 + 1, v___x_307_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1 + 2, v___x_306_);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_mk_empty_array_with_capacity(v___x_309_);
v___x_311_ = lean_array_push(v___x_310_, v___x_308_);
v___x_312_ = l_Lean_Options_empty;
v___x_313_ = 0;
v___x_314_ = l_Lean_withImportModules___redArg(v___x_311_, v___x_312_, v___f_305_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_replayFromFresh___boxed(lean_object* v_module_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_replayFromFresh(v_module_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_getCurrentModule(){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_getCurrentModule___closed__0));
v___x_321_ = l_Lake_Manifest_load_x3f(v___x_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_336_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_336_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_336_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_336_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
if (lean_obj_tag(v_a_322_) == 0)
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_box(0);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
else
{
lean_object* v_val_330_; lean_object* v_name_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v_val_330_ = lean_ctor_get(v_a_322_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v_a_322_, 1);
v_name_331_ = lean_ctor_get(v_val_330_, 0);
lean_inc(v_name_331_);
lean_dec(v_val_330_);
v___x_332_ = l_Lean_Name_capitalize(v_name_331_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_332_);
v___x_334_ = v___x_324_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_321_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_321_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_getCurrentModule___boxed(lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_getCurrentModule();
return v_res_346_;
}
}
static lean_object* _init_l_List_partition_loop___at___00main_spec__0___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_349_ = lean_string_utf8_byte_size(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
if (lean_obj_tag(v_a_350_) == 0)
{
lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_362_; 
v_fst_352_ = lean_ctor_get(v_a_351_, 0);
v_snd_353_ = lean_ctor_get(v_a_351_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_a_351_);
if (v_isSharedCheck_362_ == 0)
{
v___x_355_ = v_a_351_;
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_snd_353_);
lean_inc(v_fst_352_);
lean_dec(v_a_351_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = l_List_reverse___redArg(v_fst_352_);
v___x_358_ = l_List_reverse___redArg(v_snd_353_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_358_);
lean_ctor_set(v___x_355_, 0, v___x_357_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v_head_363_; lean_object* v_tail_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_391_; 
v_head_363_ = lean_ctor_get(v_a_350_, 0);
v_tail_364_ = lean_ctor_get(v_a_350_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_a_350_);
if (v_isSharedCheck_391_ == 0)
{
v___x_366_ = v_a_350_;
v_isShared_367_ = v_isSharedCheck_391_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_tail_364_);
lean_inc(v_head_363_);
lean_dec(v_a_350_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_391_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_390_; 
v_fst_368_ = lean_ctor_get(v_a_351_, 0);
v_snd_369_ = lean_ctor_get(v_a_351_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_a_351_);
if (v_isSharedCheck_390_ == 0)
{
v___x_371_ = v_a_351_;
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snd_369_);
lean_inc(v_fst_368_);
lean_dec(v_a_351_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_381_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_382_ = lean_string_utf8_byte_size(v_head_363_);
v___x_383_ = lean_obj_once(&l_List_partition_loop___at___00main_spec__0___closed__1, &l_List_partition_loop___at___00main_spec__0___closed__1_once, _init_l_List_partition_loop___at___00main_spec__0___closed__1);
v___x_384_ = lean_nat_dec_le(v___x_383_, v___x_382_);
if (v___x_384_ == 0)
{
goto v___jp_373_;
}
else
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_string_memcmp(v_head_363_, v___x_381_, v___x_385_, v___x_385_, v___x_383_);
if (v___x_386_ == 0)
{
goto v___jp_373_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_del_object(v___x_371_);
lean_del_object(v___x_366_);
v___x_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_387_, 0, v_head_363_);
lean_ctor_set(v___x_387_, 1, v_fst_368_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_snd_369_);
v_a_350_ = v_tail_364_;
v_a_351_ = v___x_388_;
goto _start;
}
}
v___jp_373_:
{
lean_object* v___x_375_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v_snd_369_);
v___x_375_ = v___x_366_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_head_363_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_snd_369_);
v___x_375_ = v_reuseFailAlloc_380_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v___x_375_);
v___x_377_ = v___x_371_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_fst_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
v_a_350_ = v_tail_364_;
v_a_351_ = v___x_377_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(lean_object* v_head_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_replayFromImports(v_head_392_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 1);
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_a_403_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_394_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_394_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 0);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed(lean_object* v_head_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(v_head_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v_as_x27_414_, lean_object* v_b_415_){
_start:
{
if (lean_obj_tag(v_as_x27_414_) == 0)
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v_b_415_);
return v___x_417_;
}
else
{
lean_object* v_head_418_; lean_object* v_tail_419_; lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_head_418_ = lean_ctor_get(v_as_x27_414_, 0);
v_tail_419_ = lean_ctor_get(v_as_x27_414_, 1);
lean_inc_n(v_head_418_, 2);
v___f_420_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_420_, 0, v_head_418_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_io_as_task(v___f_420_, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_head_418_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_array_push(v_b_415_, v___x_423_);
v_as_x27_414_ = v_tail_419_;
v_b_415_ = v___x_424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v_as_x27_426_, lean_object* v_b_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_426_, v_b_427_);
lean_dec(v_as_x27_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg(uint8_t v___y_432_, lean_object* v_as_x27_433_, lean_object* v_b_434_){
_start:
{
if (lean_obj_tag(v_as_x27_433_) == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v_b_434_);
return v___x_436_;
}
else
{
lean_object* v_head_437_; lean_object* v_tail_438_; lean_object* v___x_439_; 
v_head_437_ = lean_ctor_get(v_as_x27_433_, 0);
v_tail_438_ = lean_ctor_get(v_as_x27_433_, 1);
v___x_439_ = lean_box(0);
if (v___y_432_ == 0)
{
goto v___jp_440_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_443_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(v_head_437_);
v___x_444_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_437_, v___y_432_);
v___x_445_ = lean_string_append(v___x_443_, v___x_444_);
lean_dec_ref(v___x_444_);
v___x_446_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1));
v___x_447_ = lean_string_append(v___x_445_, v___x_446_);
v___x_448_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_dec_ref_known(v___x_448_, 1);
goto v___jp_440_;
}
else
{
return v___x_448_;
}
}
v___jp_440_:
{
lean_object* v___x_441_; 
lean_inc(v_head_437_);
v___x_441_ = l_replayFromFresh(v_head_437_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_dec_ref_known(v___x_441_, 1);
v_as_x27_433_ = v_tail_438_;
v_b_434_ = v___x_439_;
goto _start;
}
else
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(lean_object* v___y_449_, lean_object* v_as_x27_450_, lean_object* v_b_451_, lean_object* v___y_452_){
_start:
{
uint8_t v___y_5391__boxed_453_; lean_object* v_res_454_; 
v___y_5391__boxed_453_ = lean_unbox(v___y_449_);
v_res_454_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_5391__boxed_453_, v_as_x27_450_, v_b_451_);
lean_dec(v_as_x27_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = l_List_reverse___redArg(v_x_457_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v_head_461_; lean_object* v_tail_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_476_; 
v_head_461_ = lean_ctor_get(v_x_456_, 0);
v_tail_462_ = lean_ctor_get(v_x_456_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_x_456_);
if (v_isSharedCheck_476_ == 0)
{
v___x_464_ = v_x_456_;
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_tail_462_);
lean_inc(v_head_461_);
lean_dec(v_x_456_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
lean_inc(v_head_461_);
v___x_466_ = l_String_toName(v_head_461_);
v___x_467_ = l_Lean_Name_isAnonymous(v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_469_; 
lean_dec(v_head_461_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_x_457_);
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_x_457_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_x_456_ = v_tail_462_;
v_x_457_ = v___x_469_;
goto _start;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v___x_466_);
lean_del_object(v___x_464_);
lean_dec(v_tail_462_);
lean_dec(v_x_457_);
v___x_472_ = ((lean_object*)(l_List_mapM_loop___at___00main_spec__6___closed__0));
v___x_473_ = lean_string_append(v___x_472_, v_head_461_);
lean_dec(v_head_461_);
v___x_474_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00main_spec__6___boxed(lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_List_mapM_loop___at___00main_spec__6(v_x_477_, v_x_478_);
return v_res_480_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0(void){
_start:
{
lean_object* v___x_481_; lean_object* v___f_482_; 
v___x_481_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_482_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_482_, 0, v___x_481_);
return v___f_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v_val_484_, lean_object* v_a_485_, lean_object* v_fst_486_, lean_object* v_as_487_, size_t v_sz_488_, size_t v_i_489_, lean_object* v_b_490_){
_start:
{
lean_object* v_a_493_; uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_lt(v_i_489_, v_sz_488_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v_fst_486_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_b_490_);
return v___x_498_;
}
else
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_array_uget_borrowed(v_as_487_, v_i_489_);
lean_inc(v_a_499_);
v___x_500_ = l_Lean_searchModuleNameOfFileName(v_a_499_, v_val_484_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___y_503_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
if (lean_obj_tag(v_a_501_) == 1)
{
lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_524_; 
v_fst_506_ = lean_ctor_get(v_b_490_, 0);
v_snd_507_ = lean_ctor_get(v_b_490_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_b_490_);
if (v_isSharedCheck_524_ == 0)
{
v___x_509_ = v_b_490_;
v_isShared_510_ = v_isSharedCheck_524_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v_b_490_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_524_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_val_511_; lean_object* v___f_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_val_511_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_a_501_, 1);
v___f_520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
lean_inc(v_fst_486_);
v___x_522_ = l_List_elem___redArg(v___f_520_, v___x_521_, v_fst_486_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; 
v___x_523_ = l_Lean_Name_isPrefixOf(v_a_485_, v_val_511_);
if (v___x_523_ == 0)
{
goto v___jp_515_;
}
else
{
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
goto v___jp_512_;
}
}
else
{
goto v___jp_515_;
}
v___jp_512_:
{
uint8_t v___x_513_; 
v___x_513_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v_val_511_, v_fst_506_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_514_, 0, v_val_511_);
lean_ctor_set(v___x_514_, 1, v_fst_506_);
v___y_503_ = v___x_514_;
goto v___jp_502_;
}
else
{
lean_dec(v_val_511_);
v___y_503_ = v_fst_506_;
goto v___jp_502_;
}
}
v___jp_515_:
{
uint8_t v___x_516_; 
v___x_516_ = lean_name_eq(v_a_485_, v_val_511_);
if (v___x_516_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_val_511_);
if (v_isShared_510_ == 0)
{
v___x_518_ = v___x_509_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_fst_506_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_snd_507_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
v_a_493_ = v___x_518_;
goto v___jp_492_;
}
}
else
{
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
goto v___jp_512_;
}
}
}
}
else
{
lean_object* v_fst_525_; lean_object* v_snd_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_501_);
v_fst_525_ = lean_ctor_get(v_b_490_, 0);
v_snd_526_ = lean_ctor_get(v_b_490_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_b_490_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v_b_490_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_snd_526_);
lean_inc(v_fst_525_);
lean_dec(v_b_490_);
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
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_fst_525_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_snd_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
v_a_493_ = v___x_531_;
goto v___jp_492_;
}
}
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_box(v___x_497_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___y_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v_a_493_ = v___x_505_;
goto v___jp_492_;
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_b_490_);
lean_dec(v_fst_486_);
v_a_534_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_500_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_500_);
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
v___jp_492_:
{
size_t v___x_494_; size_t v___x_495_; 
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_489_, v___x_494_);
v_i_489_ = v___x_495_;
v_b_490_ = v_a_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v_val_542_, lean_object* v_a_543_, lean_object* v_fst_544_, lean_object* v_as_545_, lean_object* v_sz_546_, lean_object* v_i_547_, lean_object* v_b_548_, lean_object* v___y_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_546_);
lean_dec(v_sz_546_);
v_i_boxed_551_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_val_542_, v_a_543_, v_fst_544_, v_as_545_, v_sz_boxed_550_, v_i_boxed_551_, v_b_548_);
lean_dec_ref(v_as_545_);
lean_dec(v_a_543_);
lean_dec(v_val_542_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_val_555_, lean_object* v_fst_556_, lean_object* v_as_x27_557_, lean_object* v_b_558_){
_start:
{
if (lean_obj_tag(v_as_x27_557_) == 0)
{
lean_object* v___x_560_; 
lean_dec(v_fst_556_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_b_558_);
return v___x_560_;
}
else
{
lean_object* v_head_561_; lean_object* v_tail_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_head_561_ = lean_ctor_get(v_as_x27_557_, 0);
v_tail_562_ = lean_ctor_get(v_as_x27_557_, 1);
v___x_563_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0));
v___x_564_ = l_Lean_SearchPath_findAllWithExt(v_val_555_, v___x_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; size_t v_sz_569_; size_t v___x_570_; lean_object* v___x_571_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = 0;
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_b_558_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v_sz_569_ = lean_array_size(v_a_565_);
v___x_570_ = ((size_t)0ULL);
lean_inc(v_fst_556_);
v___x_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_val_555_, v_head_561_, v_fst_556_, v_a_565_, v_sz_569_, v___x_570_, v___x_568_);
lean_dec(v_a_565_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_588_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_588_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_588_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_588_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_snd_576_; uint8_t v___x_577_; 
v_snd_576_ = lean_ctor_get(v_a_572_, 1);
v___x_577_ = lean_unbox(v_snd_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
lean_dec(v_a_572_);
lean_dec(v_fst_556_);
v___x_578_ = 1;
v___x_579_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1));
lean_inc(v_head_561_);
v___x_580_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_561_, v___x_578_);
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 0, v___x_582_);
v___x_584_ = v___x_574_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v_fst_586_; 
lean_del_object(v___x_574_);
v_fst_586_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_fst_586_);
lean_dec(v_a_572_);
v_as_x27_557_ = v_tail_562_;
v_b_558_ = v_fst_586_;
goto _start;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_fst_556_);
v_a_589_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_571_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_571_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v_b_558_);
lean_dec(v_fst_556_);
v_a_597_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_564_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_564_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_val_605_, lean_object* v_fst_606_, lean_object* v_as_x27_607_, lean_object* v_b_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_val_605_, v_fst_606_, v_as_x27_607_, v_b_608_);
lean_dec(v_as_x27_607_);
lean_dec(v_val_605_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(uint8_t v___y_612_, lean_object* v_as_613_, size_t v_sz_614_, size_t v_i_615_, lean_object* v_b_616_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_b_616_);
return v___x_619_;
}
else
{
lean_object* v_a_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_623_; 
v_a_620_ = lean_array_uget_borrowed(v_as_613_, v_i_615_);
v_fst_621_ = lean_ctor_get(v_a_620_, 0);
v_snd_622_ = lean_ctor_get(v_a_620_, 1);
v___x_623_ = lean_box(0);
if (v___y_612_ == 0)
{
goto v___jp_624_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0));
lean_inc(v_fst_621_);
v___x_643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_621_, v___y_612_);
v___x_644_ = lean_string_append(v___x_642_, v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_644_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_dec_ref_known(v___x_645_, 1);
goto v___jp_624_;
}
else
{
return v___x_645_;
}
}
v___jp_624_:
{
lean_object* v___x_625_; 
lean_inc(v_snd_622_);
v___x_625_ = lean_task_get_own(v_snd_622_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0));
lean_inc(v_fst_621_);
v___x_628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_621_, v___x_618_);
v___x_629_ = lean_string_append(v___x_627_, v___x_628_);
lean_dec_ref(v___x_628_);
v___x_630_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_630_, 0);
lean_dec(v_unused_638_);
v___x_632_ = v___x_630_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_dec(v___x_630_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
lean_ctor_set(v___x_632_, 0, v_a_626_);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_626_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_dec(v_a_626_);
return v___x_630_;
}
}
else
{
size_t v___x_639_; size_t v___x_640_; 
lean_dec(v___x_625_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_add(v_i_615_, v___x_639_);
v_i_615_ = v___x_640_;
v_b_616_ = v___x_623_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___boxed(lean_object* v___y_646_, lean_object* v_as_647_, lean_object* v_sz_648_, lean_object* v_i_649_, lean_object* v_b_650_, lean_object* v___y_651_){
_start:
{
uint8_t v___y_5687__boxed_652_; size_t v_sz_boxed_653_; size_t v_i_boxed_654_; lean_object* v_res_655_; 
v___y_5687__boxed_652_ = lean_unbox(v___y_646_);
v_sz_boxed_653_ = lean_unbox_usize(v_sz_648_);
lean_dec(v_sz_648_);
v_i_boxed_654_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_5687__boxed_652_, v_as_647_, v_sz_boxed_653_, v_i_boxed_654_, v_b_650_);
lean_dec_ref(v_as_647_);
return v_res_655_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_664_; lean_object* v___x_665_; 
v___x_664_ = 0;
v___x_665_ = lean_box_uint32(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_666_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_main___closed__0));
v___x_672_ = l_Lean_findSysroot(v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = lean_box(0);
v___x_675_ = l_Lean_initSearchPath(v_a_673_, v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_fst_678_; lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref_known(v___x_675_, 1);
v___x_676_ = ((lean_object*)(l_main___closed__1));
v___x_677_ = l_List_partition_loop___at___00main_spec__0(v_args_666_, v___x_676_);
v_fst_678_ = lean_ctor_get(v___x_677_, 0);
v_snd_679_ = lean_ctor_get(v___x_677_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_777_ == 0)
{
v___x_681_ = v___x_677_;
v_isShared_682_ = v_isSharedCheck_777_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_inc(v_fst_678_);
lean_dec(v___x_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_777_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___f_683_; uint8_t v___y_685_; lean_object* v_targets_686_; uint8_t v___y_749_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___f_683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_773_ = ((lean_object*)(l_main___closed__4));
lean_inc(v_fst_678_);
v___x_774_ = l_List_elem___redArg(v___f_683_, v___x_773_, v_fst_678_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_main___closed__5));
lean_inc(v_fst_678_);
v___x_776_ = l_List_elem___redArg(v___f_683_, v___x_775_, v_fst_678_);
v___y_749_ = v___x_776_;
goto v___jp_748_;
}
else
{
v___y_749_ = v___x_774_;
goto v___jp_748_;
}
v___jp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = l_Lean_searchPathRef;
v___x_688_ = lean_st_ref_get(v___x_687_);
lean_inc(v_fst_678_);
v___x_689_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_688_, v_fst_678_, v_targets_686_, v___x_674_);
lean_dec(v_targets_686_);
lean_dec(v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_739_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_739_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_739_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_739_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
v___x_695_ = l_List_elem___redArg(v___f_683_, v___x_694_, v_fst_678_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_del_object(v___x_692_);
v___x_696_ = ((lean_object*)(l_main___closed__2));
v___x_697_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_a_690_, v___x_696_);
lean_dec(v_a_690_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; size_t v_sz_700_; size_t v___x_701_; lean_object* v___x_702_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = lean_box(0);
v_sz_700_ = lean_array_size(v_a_698_);
v___x_701_ = ((size_t)0ULL);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_685_, v_a_698_, v_sz_700_, v___x_701_, v___x_699_);
lean_dec(v_a_698_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec_ref_known(v___x_702_, 1);
goto v___jp_668_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
v_a_711_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_697_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_697_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = l_List_lengthTR___redArg(v_a_690_);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_dec_eq(v___x_719_, v___x_720_);
lean_dec(v___x_719_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_722_ = ((lean_object*)(l_main___closed__3));
v___x_723_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_690_);
v___x_724_ = lean_string_append(v___x_722_, v___x_723_);
lean_dec_ref(v___x_723_);
v___x_725_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 0, v___x_725_);
v___x_727_ = v___x_692_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_del_object(v___x_692_);
v___x_729_ = lean_box(0);
v___x_730_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_685_, v_a_690_, v___x_729_);
lean_dec(v_a_690_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_dec_ref_known(v___x_730_, 1);
goto v___jp_668_;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_fst_678_);
v_a_740_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_689_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_689_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
v___jp_748_:
{
if (lean_obj_tag(v_snd_679_) == 0)
{
lean_object* v___x_750_; 
v___x_750_ = l_getCurrentModule();
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
if (v_isShared_682_ == 0)
{
lean_ctor_set_tag(v___x_681_, 1);
lean_ctor_set(v___x_681_, 1, v___x_674_);
lean_ctor_set(v___x_681_, 0, v_a_751_);
v___x_753_ = v___x_681_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_674_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
v___y_685_ = v___y_749_;
v_targets_686_ = v___x_753_;
goto v___jp_684_;
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_del_object(v___x_681_);
lean_dec(v_fst_678_);
v_a_755_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_750_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v___x_763_; 
lean_del_object(v___x_681_);
v___x_763_ = l_List_mapM_loop___at___00main_spec__6(v_snd_679_, v___x_674_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___y_685_ = v___y_749_;
v_targets_686_ = v_a_764_;
goto v___jp_684_;
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_fst_678_);
v_a_765_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_763_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v_args_666_);
v_a_778_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_675_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_675_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_args_666_);
v_a_786_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_672_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_672_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
v___jp_668_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = l_main___boxed__const__1;
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = _lean_main(v_args_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_val_797_, lean_object* v_fst_798_, lean_object* v_as_799_, lean_object* v_as_x27_800_, lean_object* v_b_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_val_797_, v_fst_798_, v_as_x27_800_, v_b_801_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_val_805_, lean_object* v_fst_806_, lean_object* v_as_807_, lean_object* v_as_x27_808_, lean_object* v_b_809_, lean_object* v_a_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_List_forIn_x27_loop___at___00main_spec__2(v_val_805_, v_fst_806_, v_as_807_, v_as_x27_808_, v_b_809_, v_a_810_);
lean_dec(v_as_x27_808_);
lean_dec(v_as_807_);
lean_dec(v_val_805_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_813_, lean_object* v_as_x27_814_, lean_object* v_b_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_814_, v_b_815_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_819_, lean_object* v_as_x27_820_, lean_object* v_b_821_, lean_object* v_a_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_819_, v_as_x27_820_, v_b_821_, v_a_822_);
lean_dec(v_as_x27_820_);
lean_dec(v_as_819_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5(uint8_t v___y_825_, lean_object* v_as_826_, lean_object* v_as_x27_827_, lean_object* v_b_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_825_, v_as_x27_827_, v_b_828_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___boxed(lean_object* v___y_832_, lean_object* v_as_833_, lean_object* v_as_x27_834_, lean_object* v_b_835_, lean_object* v_a_836_, lean_object* v___y_837_){
_start:
{
uint8_t v___y_6062__boxed_838_; lean_object* v_res_839_; 
v___y_6062__boxed_838_ = lean_unbox(v___y_832_);
v_res_839_ = l_List_forIn_x27_loop___at___00main_spec__5(v___y_6062__boxed_838_, v_as_833_, v_as_x27_834_, v_b_835_, v_a_836_);
lean_dec(v_as_x27_834_);
lean_dec(v_as_833_);
return v_res_839_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanChecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
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
