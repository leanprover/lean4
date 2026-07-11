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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Environment_replay(lean_object*, lean_object*);
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
uint8_t v___x_69_; lean_object* v___y_71_; lean_object* v___y_72_; lean_object* v___y_73_; uint8_t v___y_74_; lean_object* v___y_75_; uint8_t v___y_76_; lean_object* v___y_77_; uint8_t v___y_78_; lean_object* v_fnames_139_; 
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
v_imports_81_ = lean_ctor_get(v___y_72_, 0);
lean_inc_ref(v_imports_81_);
lean_dec_ref(v___y_72_);
lean_inc(v___y_71_);
v___x_82_ = l_Lean_importModulesCore(v_imports_81_, v___y_74_, v___y_71_, v___y_78_, v___y_76_, v___x_80_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; uint32_t v___x_85_; lean_object* v___x_86_; 
lean_dec_ref_known(v___x_82_, 1);
v___x_83_ = lean_st_ref_get(v___x_80_);
lean_dec(v___x_80_);
v___x_84_ = l_Lean_Options_empty;
v___x_85_ = 0;
v___x_86_ = l_Lean_finalizeImport(v___x_83_, v_imports_81_, v___x_84_, v___x_85_, v___y_76_, v___y_76_, v___y_74_, v___x_69_, v___y_76_);
lean_dec(v___x_83_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_fst_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_128_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_86_, 1);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_sub(v___y_77_, v___x_88_);
lean_dec(v___y_77_);
v___x_90_ = lean_array_fget(v___y_73_, v___x_89_);
lean_dec(v___x_89_);
lean_dec_ref(v___y_73_);
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
lean_inc(v___y_75_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_75_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_array_get_size(v_constants_96_);
v___x_100_ = l_Array_toSubarray___redArg(v_constants_96_, v___y_75_, v___x_99_);
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
lean_dec_ref_known(v___x_105_, 1);
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
lean_dec_ref_known(v___x_108_, 1);
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
lean_dec(v___y_75_);
lean_dec_ref(v___y_73_);
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
lean_dec_ref(v___y_73_);
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
v___y_72_ = v_fst_149_;
v___y_73_ = v_a_141_;
v___y_74_ = v___x_150_;
v___y_75_ = v___x_146_;
v___y_76_ = v___x_147_;
v___y_77_ = v___x_145_;
v___y_78_ = v___x_69_;
goto v___jp_70_;
}
else
{
v___y_71_ = v___x_151_;
v___y_72_ = v_fst_149_;
v___y_73_ = v_a_141_;
v___y_74_ = v___x_150_;
v___y_75_ = v___x_146_;
v___y_76_ = v___x_147_;
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
v___x_205_ = l_Lean_mkEmptyEnvironment(v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; lean_object* v_map_u2081_208_; lean_object* v___x_209_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
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
lean_dec_ref_known(v_a_258_, 1);
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
lean_dec_ref_known(v___x_410_, 1);
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
lean_dec_ref_known(v___x_403_, 1);
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
uint8_t v___y_5246__boxed_415_; lean_object* v_res_416_; 
v___y_5246__boxed_415_ = lean_unbox(v___y_411_);
v_res_416_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_5246__boxed_415_, v_as_x27_412_, v_b_413_);
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
lean_dec_ref_known(v___x_436_, 1);
if (lean_obj_tag(v_a_437_) == 1)
{
lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_461_; 
v_fst_442_ = lean_ctor_get(v_b_426_, 0);
v_snd_443_ = lean_ctor_get(v_b_426_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_b_426_);
if (v_isSharedCheck_461_ == 0)
{
v___x_445_ = v_b_426_;
v_isShared_446_ = v_isSharedCheck_461_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snd_443_);
lean_inc(v_fst_442_);
lean_dec(v_b_426_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_461_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_val_447_; lean_object* v___f_456_; lean_object* v___x_457_; uint8_t v___x_458_; uint8_t v___x_459_; 
v_val_447_ = lean_ctor_get(v_a_437_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_a_437_, 1);
v___f_456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
lean_inc(v_fst_422_);
v___x_458_ = l_List_elem___redArg(v___f_456_, v___x_457_, v_fst_422_);
v___x_459_ = lean_bool_not(v___x_458_);
if (v___x_459_ == 0)
{
goto v___jp_451_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_Name_isPrefixOf(v_a_421_, v_val_447_);
if (v___x_460_ == 0)
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
lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_437_);
v_fst_462_ = lean_ctor_get(v_b_426_, 0);
v_snd_463_ = lean_ctor_get(v_b_426_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_b_426_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v_b_426_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_snd_463_);
lean_inc(v_fst_462_);
lean_dec(v_b_426_);
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
v_a_429_ = v___x_468_;
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
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_b_426_);
lean_dec(v_fst_422_);
v_a_471_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_436_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_436_);
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
lean_object* v_fst_513_; lean_object* v_snd_514_; uint8_t v___x_515_; uint8_t v___x_516_; 
v_fst_513_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_fst_513_);
v_snd_514_ = lean_ctor_get(v_a_509_, 1);
lean_inc(v_snd_514_);
lean_dec(v_a_509_);
v___x_515_ = lean_unbox(v_snd_514_);
lean_dec(v_snd_514_);
v___x_516_ = lean_bool_not(v___x_515_);
if (v___x_516_ == 0)
{
lean_del_object(v___x_511_);
v_as_x27_494_ = v_tail_499_;
v_b_495_ = v_fst_513_;
goto _start;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec(v_fst_513_);
lean_dec(v_fst_493_);
v___x_518_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1));
lean_inc(v_head_498_);
v___x_519_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_498_, v___x_516_);
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 1);
lean_ctor_set(v___x_511_, 0, v___x_521_);
v___x_523_ = v___x_511_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
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
uint8_t v___y_5496__boxed_589_; size_t v_sz_boxed_590_; size_t v_i_boxed_591_; lean_object* v_res_592_; 
v___y_5496__boxed_589_ = lean_unbox(v___y_583_);
v_sz_boxed_590_ = lean_unbox_usize(v_sz_585_);
lean_dec(v_sz_585_);
v_i_boxed_591_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_5496__boxed_589_, v_as_584_, v_sz_boxed_590_, v_i_boxed_591_, v_b_587_);
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
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref_known(v___x_612_, 1);
v___x_613_ = ((lean_object*)(l_main___closed__1));
v___x_614_ = l_List_partition_loop___at___00main_spec__0(v_args_603_, v___x_613_);
v_fst_615_ = lean_ctor_get(v___x_614_, 0);
v_snd_616_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_715_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_715_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_715_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___f_620_; uint8_t v___y_622_; lean_object* v_targets_623_; uint8_t v___y_687_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___f_620_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
v___x_711_ = ((lean_object*)(l_main___closed__4));
lean_inc(v_fst_615_);
v___x_712_ = l_List_elem___redArg(v___f_620_, v___x_711_, v_fst_615_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = ((lean_object*)(l_main___closed__5));
lean_inc(v_fst_615_);
v___x_714_ = l_List_elem___redArg(v___f_620_, v___x_713_, v_fst_615_);
v___y_687_ = v___x_714_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___x_712_;
goto v___jp_686_;
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
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_677_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_677_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_677_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_677_;
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
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; uint8_t v___x_659_; 
v___x_656_ = l_List_lengthTR___redArg(v_a_627_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_dec_eq(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_bool_not(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_del_object(v___x_629_);
v___x_660_ = lean_box(0);
v___x_661_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_622_, v_a_627_, v___x_660_);
lean_dec(v_a_627_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec_ref_known(v___x_661_, 1);
goto v___jp_605_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_670_ = ((lean_object*)(l_main___closed__3));
v___x_671_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_627_);
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 1);
lean_ctor_set(v___x_629_, 0, v___x_673_);
v___x_675_ = v___x_629_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_fst_615_);
v_a_678_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_626_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_626_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
v___jp_686_:
{
if (lean_obj_tag(v_snd_616_) == 0)
{
lean_object* v___x_688_; 
v___x_688_ = l_getCurrentModule();
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 1);
lean_ctor_set(v___x_618_, 1, v___x_611_);
lean_ctor_set(v___x_618_, 0, v_a_689_);
v___x_691_ = v___x_618_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_611_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v___y_622_ = v___y_687_;
v_targets_623_ = v___x_691_;
goto v___jp_621_;
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_del_object(v___x_618_);
lean_dec(v_fst_615_);
v_a_693_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_688_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_688_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v___x_701_; 
lean_del_object(v___x_618_);
v___x_701_ = l_List_mapM_loop___at___00main_spec__6(v_snd_616_, v___x_611_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___y_622_ = v___y_687_;
v_targets_623_ = v_a_702_;
goto v___jp_621_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_fst_615_);
v_a_703_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_701_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_701_);
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
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_args_603_);
v_a_716_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_612_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_612_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_args_603_);
v_a_724_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_609_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_609_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
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
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = _lean_main(v_args_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_val_735_, lean_object* v_fst_736_, lean_object* v_as_737_, lean_object* v_as_x27_738_, lean_object* v_b_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_val_735_, v_fst_736_, v_as_x27_738_, v_b_739_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_val_743_, lean_object* v_fst_744_, lean_object* v_as_745_, lean_object* v_as_x27_746_, lean_object* v_b_747_, lean_object* v_a_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_List_forIn_x27_loop___at___00main_spec__2(v_val_743_, v_fst_744_, v_as_745_, v_as_x27_746_, v_b_747_, v_a_748_);
lean_dec(v_as_x27_746_);
lean_dec(v_as_745_);
lean_dec(v_val_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_751_, lean_object* v_as_x27_752_, lean_object* v_b_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_752_, v_b_753_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_757_, lean_object* v_as_x27_758_, lean_object* v_b_759_, lean_object* v_a_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_757_, v_as_x27_758_, v_b_759_, v_a_760_);
lean_dec(v_as_x27_758_);
lean_dec(v_as_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5(uint8_t v___y_763_, lean_object* v_as_764_, lean_object* v_as_x27_765_, lean_object* v_b_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(v___y_763_, v_as_x27_765_, v_b_766_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__5___boxed(lean_object* v___y_770_, lean_object* v_as_771_, lean_object* v_as_x27_772_, lean_object* v_b_773_, lean_object* v_a_774_, lean_object* v___y_775_){
_start:
{
uint8_t v___y_5873__boxed_776_; lean_object* v_res_777_; 
v___y_5873__boxed_776_ = lean_unbox(v___y_770_);
v_res_777_ = l_List_forIn_x27_loop___at___00main_spec__5(v___y_5873__boxed_776_, v_as_771_, v_as_x27_772_, v_b_773_, v_a_774_);
lean_dec(v_as_x27_772_);
lean_dec(v_as_771_);
return v_res_777_;
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
