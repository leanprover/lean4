// Lean compiler output
// Module: Lake.Build.Executable
// Imports: public import Lake.Config.FacetConfig import Lake.Build.Job.Register import Lake.Build.Target.Fetch import Lake.Build.Common import Lake.Build.Infos
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
lean_object* l_Lake_LeanExe_exeOnlyLinkArgs(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
uint8_t lean_strict_and(uint8_t, uint8_t);
lean_object* l_Lake_buildLeanExeSync(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
extern lean_object* l_Lake_LeanExe_exeFacet;
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
extern lean_object* l_Lake_LeanExe_defaultFacet;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object*);
extern lean_object* l_Lake_Module_linkInfoNoExportFacet;
extern lean_object* l_Lake_Module_keyword;
extern lean_object* l_Lake_Module_linkInfoExportFacet;
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___boxed(lean_object*);
static const lean_array_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "LeanExe.exeOnlyLinkArgs: "};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3;
static lean_once_cell_t l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ":exe"};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanExe_exeFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanExe_exeFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanExe_exeFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_LeanExe_exeFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanExe_exeFacetConfig___closed__1 = (const lean_object*)&l_Lake_LeanExe_exeFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_LeanExe_exeFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_exeFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeFacetConfig;
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanExe_defaultFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanExe_defaultFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanExe_defaultFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_LeanExe_defaultFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_defaultFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanExe_defaultFacetConfig;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_LeanExe_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_initFacetConfigs___closed__0;
static lean_once_cell_t l_Lake_LeanExe_initFacetConfigs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_initFacetConfigs___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanExe_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, uint64_t v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint64_t v___x_7_; uint64_t v___x_8_; uint64_t v___x_9_; uint64_t v___x_10_; size_t v___x_11_; size_t v___x_12_; 
v___x_6_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_7_ = l_Lake_Hash_nil;
v___x_8_ = lean_string_hash(v___x_6_);
v___x_9_ = lean_uint64_mix_hash(v___x_7_, v___x_8_);
v___x_10_ = lean_uint64_mix_hash(v_b_4_, v___x_9_);
v___x_11_ = ((size_t)1ULL);
v___x_12_ = lean_usize_add(v_i_2_, v___x_11_);
v_i_2_ = v___x_12_;
v_b_4_ = v___x_10_;
goto _start;
}
else
{
return v_b_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1___boxed(lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_, lean_object* v_b_17_){
_start:
{
size_t v_i_boxed_18_; size_t v_stop_boxed_19_; uint64_t v_b_boxed_20_; uint64_t v_res_21_; lean_object* v_r_22_; 
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_19_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_b_boxed_20_ = lean_unbox_uint64(v_b_17_);
lean_dec_ref(v_b_17_);
v_res_21_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v_as_14_, v_i_boxed_18_, v_stop_boxed_19_, v_b_boxed_20_);
lean_dec_ref(v_as_14_);
v_r_22_ = lean_box_uint64(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
return v_x_24_;
}
else
{
lean_object* v_head_26_; lean_object* v_tail_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_head_26_ = lean_ctor_get(v_x_25_, 0);
v_tail_27_ = lean_ctor_get(v_x_25_, 1);
v___x_28_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___closed__0));
v___x_29_ = lean_string_append(v_x_24_, v___x_28_);
v___x_30_ = lean_string_append(v___x_29_, v_head_26_);
v_x_24_ = v___x_30_;
v_x_25_ = v_tail_27_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___boxed(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(v_x_32_, v_x_33_);
lean_dec(v_x_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(lean_object* v_x_38_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v___x_39_; 
v___x_39_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__0));
return v___x_39_;
}
else
{
lean_object* v_tail_40_; 
v_tail_40_ = lean_ctor_get(v_x_38_, 1);
if (lean_obj_tag(v_tail_40_) == 0)
{
lean_object* v_head_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_head_41_ = lean_ctor_get(v_x_38_, 0);
v___x_42_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__1));
v___x_43_ = lean_string_append(v___x_42_, v_head_41_);
v___x_44_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__2));
v___x_45_ = lean_string_append(v___x_43_, v___x_44_);
return v___x_45_;
}
else
{
lean_object* v_head_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint32_t v___x_50_; lean_object* v___x_51_; 
v_head_46_ = lean_ctor_get(v_x_38_, 0);
v___x_47_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__1));
v___x_48_ = lean_string_append(v___x_47_, v_head_46_);
v___x_49_ = l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(v___x_48_, v_tail_40_);
v___x_50_ = 93;
v___x_51_ = lean_string_push(v___x_49_, v___x_50_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___boxed(lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(v_x_52_);
lean_dec(v_x_52_);
return v_res_53_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4(void){
_start:
{
uint32_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = 0;
v___x_61_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3);
v___x_62_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set_uint32(v___x_62_, sizeof(void*)*1, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(lean_object* v_self_63_, lean_object* v_pkg_64_, lean_object* v_exeName_65_, uint8_t v_supportInterpreter_66_, lean_object* v_info_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_args_75_; lean_object* v_objs_76_; lean_object* v_libs_77_; lean_object* v___x_78_; lean_object* v_args_79_; uint64_t v___y_81_; uint64_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_args_75_ = lean_ctor_get(v_info_67_, 0);
lean_inc_ref(v_args_75_);
v_objs_76_ = lean_ctor_get(v_info_67_, 1);
lean_inc_ref(v_objs_76_);
v_libs_77_ = lean_ctor_get(v_info_67_, 2);
lean_inc_ref(v_libs_77_);
lean_dec_ref(v_info_67_);
v___x_78_ = l_Lake_LeanExe_exeOnlyLinkArgs(v_self_63_);
lean_inc_ref(v___x_78_);
v_args_79_ = l_Array_append___redArg(v___x_78_, v_args_75_);
lean_dec_ref(v_args_75_);
v___x_119_ = l_Lake_Hash_nil;
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_get_size(v___x_78_);
v___x_122_ = lean_nat_dec_lt(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
v___y_81_ = v___x_119_;
goto v___jp_80_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_le(v___x_121_, v___x_121_);
if (v___x_123_ == 0)
{
if (v___x_122_ == 0)
{
v___y_81_ = v___x_119_;
goto v___jp_80_;
}
else
{
size_t v___x_124_; size_t v___x_125_; uint64_t v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_121_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___x_78_, v___x_124_, v___x_125_, v___x_119_);
v___y_81_ = v___x_126_;
goto v___jp_80_;
}
}
else
{
size_t v___x_127_; size_t v___x_128_; uint64_t v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_121_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___x_78_, v___x_127_, v___x_128_, v___x_119_);
v___y_81_ = v___x_129_;
goto v___jp_80_;
}
}
v___jp_80_:
{
lean_object* v_config_82_; lean_object* v_log_83_; uint8_t v_action_84_; uint8_t v_wantsRebuild_85_; lean_object* v_trace_86_; lean_object* v_buildTime_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_118_; 
v_config_82_ = lean_ctor_get(v_pkg_64_, 6);
lean_inc_ref(v_config_82_);
v_log_83_ = lean_ctor_get(v___y_73_, 0);
v_action_84_ = lean_ctor_get_uint8(v___y_73_, sizeof(void*)*3);
v_wantsRebuild_85_ = lean_ctor_get_uint8(v___y_73_, sizeof(void*)*3 + 1);
v_trace_86_ = lean_ctor_get(v___y_73_, 1);
v_buildTime_87_ = lean_ctor_get(v___y_73_, 2);
v_isSharedCheck_118_ = !lean_is_exclusive(v___y_73_);
if (v_isSharedCheck_118_ == 0)
{
v___x_89_ = v___y_73_;
v_isShared_90_ = v_isSharedCheck_118_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_buildTime_87_);
lean_inc(v_trace_86_);
lean_inc(v_log_83_);
lean_dec(v___y_73_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_118_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_dir_91_; lean_object* v_buildDir_92_; lean_object* v_binDir_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v_dir_91_ = lean_ctor_get(v_pkg_64_, 4);
lean_inc_ref(v_dir_91_);
lean_dec_ref(v_pkg_64_);
v_buildDir_92_ = lean_ctor_get(v_config_82_, 5);
lean_inc_ref(v_buildDir_92_);
v_binDir_93_ = lean_ctor_get(v_config_82_, 8);
lean_inc_ref(v_binDir_93_);
lean_dec_ref(v_config_82_);
v___x_94_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0));
v___x_95_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1));
v___x_96_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2));
v___x_97_ = lean_array_to_list(v___x_78_);
v___x_98_ = l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(v___x_97_);
lean_dec(v___x_97_);
v___x_99_ = lean_string_append(v___x_96_, v___x_98_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_string_append(v___x_95_, v___x_99_);
lean_dec_ref(v___x_99_);
v___x_101_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4);
v___x_102_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_94_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
lean_ctor_set_uint64(v___x_102_, sizeof(void*)*3, v___y_81_);
v___x_103_ = l_Lake_BuildTrace_mix(v_trace_86_, v___x_102_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_103_);
v___x_105_ = v___x_89_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_log_83_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_buildTime_87_);
lean_ctor_set_uint8(v_reuseFailAlloc_117_, sizeof(void*)*3, v_action_84_);
lean_ctor_set_uint8(v_reuseFailAlloc_117_, sizeof(void*)*3 + 1, v_wantsRebuild_85_);
v___x_105_ = v_reuseFailAlloc_117_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_106_ = l_System_FilePath_normalize(v_buildDir_92_);
v___x_107_ = l_Lake_joinRelative(v_dir_91_, v___x_106_);
v___x_108_ = l_System_FilePath_normalize(v_binDir_93_);
v___x_109_ = l_Lake_joinRelative(v___x_107_, v___x_108_);
v___x_110_ = l_System_FilePath_exeExtension;
v___x_111_ = l_System_FilePath_addExtension(v_exeName_65_, v___x_110_);
v___x_112_ = l_Lake_joinRelative(v___x_109_, v___x_111_);
v___x_113_ = l_System_Platform_isWindows;
v___x_114_ = lean_strict_and(v___x_113_, v_supportInterpreter_66_);
v___x_115_ = lean_box(0);
v___x_116_ = l_Lake_buildLeanExeSync(v___x_112_, v_objs_76_, v_libs_77_, v_args_79_, v___x_114_, v___x_115_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___x_105_);
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(lean_object* v_self_130_, lean_object* v_pkg_131_, lean_object* v_exeName_132_, lean_object* v_supportInterpreter_133_, lean_object* v_info_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
uint8_t v_supportInterpreter_boxed_142_; lean_object* v_res_143_; 
v_supportInterpreter_boxed_142_ = lean_unbox(v_supportInterpreter_133_);
v_res_143_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(v_self_130_, v_pkg_131_, v_exeName_132_, v_supportInterpreter_boxed_142_, v_info_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v_self_130_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__0));
v___x_146_ = l_Lake_BuildTrace_nil(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(lean_object* v___x_147_, lean_object* v___f_148_, lean_object* v_infoJob_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = 0;
v___x_159_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1);
v___x_160_ = l_Lake_Job_mapM___redArg(v___x_147_, v_infoJob_149_, v___f_148_, v___x_157_, v___x_158_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___y_155_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed(lean_object* v___x_162_, lean_object* v___f_163_, lean_object* v_infoJob_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(v___x_162_, v___f_163_, v_infoJob_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec(v___y_167_);
lean_dec(v___y_166_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(uint8_t v_supportInterpreter_173_, lean_object* v_pkg_174_, lean_object* v_config_175_, lean_object* v_name_176_, lean_object* v_root_177_, lean_object* v___x_178_, lean_object* v___f_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
if (v_supportInterpreter_173_ == 0)
{
lean_object* v_keyName_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_keyName_187_ = lean_ctor_get(v_pkg_174_, 2);
lean_inc(v_keyName_187_);
v___x_188_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_175_);
v___x_189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_189_, 0, v_pkg_174_);
lean_ctor_set(v___x_189_, 1, v_name_176_);
lean_ctor_set(v___x_189_, 2, v___x_188_);
lean_inc(v_root_177_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_root_177_);
v___x_191_ = l_Lake_Module_linkInfoNoExportFacet;
v___x_192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_192_, 0, v_keyName_187_);
lean_ctor_set(v___x_192_, 1, v_root_177_);
v___x_193_ = l_Lake_Module_keyword;
v___x_194_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
lean_ctor_set(v___x_194_, 2, v___x_190_);
lean_ctor_set(v___x_194_, 3, v___x_191_);
lean_inc_ref(v___y_180_);
lean_inc_ref(v___y_184_);
lean_inc(v___y_183_);
lean_inc(v___y_182_);
lean_inc(v___x_178_);
v___x_195_ = lean_apply_7(v___y_180_, v___x_194_, v___x_178_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, lean_box(0));
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v___x_198_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
v_a_197_ = lean_ctor_get(v___x_195_, 1);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_195_, 2);
lean_inc_ref(v___y_184_);
lean_inc(v___y_183_);
lean_inc(v___y_182_);
v___x_198_ = lean_apply_8(v___f_179_, v_a_196_, v___y_180_, v___x_178_, v___y_182_, v___y_183_, v___y_184_, v_a_197_, lean_box(0));
return v___x_198_;
}
else
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v___y_180_);
lean_dec_ref(v___f_179_);
lean_dec(v___x_178_);
v_a_199_ = lean_ctor_get(v___x_195_, 0);
v_a_200_ = lean_ctor_get(v___x_195_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_195_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_inc(v_a_199_);
lean_dec(v___x_195_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_keyName_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_keyName_208_ = lean_ctor_get(v_pkg_174_, 2);
lean_inc(v_keyName_208_);
v___x_209_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_175_);
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v_pkg_174_);
lean_ctor_set(v___x_210_, 1, v_name_176_);
lean_ctor_set(v___x_210_, 2, v___x_209_);
lean_inc(v_root_177_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_root_177_);
v___x_212_ = l_Lake_Module_linkInfoExportFacet;
v___x_213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_213_, 0, v_keyName_208_);
lean_ctor_set(v___x_213_, 1, v_root_177_);
v___x_214_ = l_Lake_Module_keyword;
v___x_215_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___x_211_);
lean_ctor_set(v___x_215_, 3, v___x_212_);
lean_inc_ref(v___y_180_);
lean_inc_ref(v___y_184_);
lean_inc(v___y_183_);
lean_inc(v___y_182_);
lean_inc(v___x_178_);
v___x_216_ = lean_apply_7(v___y_180_, v___x_215_, v___x_178_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, lean_box(0));
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_219_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
v_a_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_216_, 2);
lean_inc_ref(v___y_184_);
lean_inc(v___y_183_);
lean_inc(v___y_182_);
v___x_219_ = lean_apply_8(v___f_179_, v_a_217_, v___y_180_, v___x_178_, v___y_182_, v___y_183_, v___y_184_, v_a_218_, lean_box(0));
return v___x_219_;
}
else
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v___y_180_);
lean_dec_ref(v___f_179_);
lean_dec(v___x_178_);
v_a_220_ = lean_ctor_get(v___x_216_, 0);
v_a_221_ = lean_ctor_get(v___x_216_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_216_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_inc(v_a_220_);
lean_dec(v___x_216_);
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
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_220_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_a_221_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed(lean_object* v_supportInterpreter_229_, lean_object* v_pkg_230_, lean_object* v_config_231_, lean_object* v_name_232_, lean_object* v_root_233_, lean_object* v___x_234_, lean_object* v___f_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
uint8_t v_supportInterpreter_boxed_243_; lean_object* v_res_244_; 
v_supportInterpreter_boxed_243_ = lean_unbox(v_supportInterpreter_229_);
v_res_244_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(v_supportInterpreter_boxed_243_, v_pkg_230_, v_config_231_, v_name_232_, v_root_233_, v___x_234_, v___f_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
lean_dec(v___y_237_);
lean_dec(v_config_231_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object* v_self_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_config_254_; lean_object* v_pkg_255_; lean_object* v_name_256_; lean_object* v_root_257_; lean_object* v_exeName_258_; uint8_t v_supportInterpreter_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___f_266_; lean_object* v___x_267_; 
v_config_254_ = lean_ctor_get(v_self_246_, 2);
lean_inc(v_config_254_);
v_pkg_255_ = lean_ctor_get(v_self_246_, 0);
lean_inc_ref_n(v_pkg_255_, 3);
v_name_256_ = lean_ctor_get(v_self_246_, 1);
lean_inc_n(v_name_256_, 2);
v_root_257_ = lean_ctor_get(v_config_254_, 2);
lean_inc(v_root_257_);
v_exeName_258_ = lean_ctor_get(v_config_254_, 3);
v_supportInterpreter_259_ = lean_ctor_get_uint8(v_config_254_, sizeof(void*)*7);
v___x_260_ = lean_box(v_supportInterpreter_259_);
lean_inc_ref(v_exeName_258_);
v___f_261_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed), 12, 4);
lean_closure_set(v___f_261_, 0, v_self_246_);
lean_closure_set(v___f_261_, 1, v_pkg_255_);
lean_closure_set(v___f_261_, 2, v_exeName_258_);
lean_closure_set(v___f_261_, 3, v___x_260_);
v___x_262_ = l_Lake_instDataKindFilePath;
v___f_263_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed), 10, 2);
lean_closure_set(v___f_263_, 0, v___x_262_);
lean_closure_set(v___f_263_, 1, v___f_261_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_pkg_255_);
v___x_265_ = lean_box(v_supportInterpreter_259_);
v___f_266_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed), 14, 7);
lean_closure_set(v___f_266_, 0, v___x_265_);
lean_closure_set(v___f_266_, 1, v_pkg_255_);
lean_closure_set(v___f_266_, 2, v_config_254_);
lean_closure_set(v___f_266_, 3, v_name_256_);
lean_closure_set(v___f_266_, 4, v_root_257_);
lean_closure_set(v___f_266_, 5, v___x_264_);
lean_closure_set(v___f_266_, 6, v___f_263_);
v___x_267_ = l_Lake_ensureJob___redArg(v___x_262_, v___f_266_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_297_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_a_269_ = lean_ctor_get(v___x_267_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_297_ == 0)
{
v___x_271_ = v___x_267_;
v_isShared_272_ = v_isSharedCheck_297_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_297_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v_task_273_; lean_object* v_kind_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_295_; 
v_task_273_ = lean_ctor_get(v_a_268_, 0);
v_kind_274_ = lean_ctor_get(v_a_268_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_268_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_a_268_, 2);
lean_dec(v_unused_296_);
v___x_276_ = v_a_268_;
v_isShared_277_ = v_isSharedCheck_295_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_kind_274_);
lean_inc(v_task_273_);
lean_dec(v_a_268_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_295_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_registeredJobs_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v_job_286_; 
v_registeredJobs_278_ = lean_ctor_get(v_a_251_, 3);
v___x_279_ = lean_st_ref_take(v_registeredJobs_278_);
v___x_280_ = 1;
v___x_281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_256_, v___x_280_);
v___x_282_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0));
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
v___x_284_ = 0;
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 2, v___x_283_);
v_job_286_ = v___x_276_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_task_273_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_kind_274_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v___x_283_);
v_job_286_ = v_reuseFailAlloc_294_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
lean_ctor_set_uint8(v_job_286_, sizeof(void*)*3, v___x_284_);
lean_inc_ref(v_job_286_);
v___x_287_ = l_Lake_Job_toOpaque___redArg(v_job_286_);
v___x_288_ = lean_array_push(v___x_279_, v___x_287_);
v___x_289_ = lean_st_ref_set(v_registeredJobs_278_, v___x_288_);
v___x_290_ = l_Lake_Job_renew___redArg(v_job_286_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_290_);
v___x_292_ = v___x_271_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_a_269_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_dec(v_name_256_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object* v_self_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(v_self_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec(v_a_301_);
lean_dec(v_a_300_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t v_fmt_307_, lean_object* v_a_308_){
_start:
{
if (v_fmt_307_ == 0)
{
return v_a_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = l_Lake_mkRelPathString(v_a_308_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = l_Lean_Json_compress(v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object* v_fmt_312_, lean_object* v_a_313_){
_start:
{
uint8_t v_fmt_boxed_314_; lean_object* v_res_315_; 
v_fmt_boxed_314_ = lean_unbox(v_fmt_312_);
v_res_315_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(v_fmt_boxed_314_, v_a_313_);
return v_res_315_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___f_318_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_319_ = 1;
v___x_320_ = l_Lake_instDataKindFilePath;
v___x_321_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__1));
v___x_322_ = l_Lake_LeanExe_keyword;
v___x_323_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_320_);
lean_ctor_set(v___x_323_, 3, v___f_318_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*4, v___x_319_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*4 + 1, v___x_319_);
return v___x_323_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_Lake_LeanExe_exeFacetConfig___closed__2, &l_Lake_LeanExe_exeFacetConfig___closed__2_once, _init_l_Lake_LeanExe_exeFacetConfig___closed__2);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object* v_lib_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_pkg_333_; lean_object* v_name_334_; lean_object* v_keyName_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_pkg_333_ = lean_ctor_get(v_lib_325_, 0);
v_name_334_ = lean_ctor_get(v_lib_325_, 1);
v_keyName_335_ = lean_ctor_get(v_pkg_333_, 2);
v___x_336_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_334_);
lean_inc(v_keyName_335_);
v___x_337_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_337_, 0, v_keyName_335_);
lean_ctor_set(v___x_337_, 1, v_name_334_);
v___x_338_ = l_Lake_LeanExe_keyword;
v___x_339_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_ctor_set(v___x_339_, 2, v_lib_325_);
lean_ctor_set(v___x_339_, 3, v___x_336_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc(v_a_328_);
lean_inc(v_a_327_);
v___x_340_ = lean_apply_7(v_a_326_, v___x_339_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, lean_box(0));
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object* v_lib_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(v_lib_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec(v_a_344_);
lean_dec(v_a_343_);
return v_res_349_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_351_; lean_object* v___f_352_; uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_351_ = 0;
v___f_352_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_353_ = 1;
v___x_354_ = l_Lake_instDataKindFilePath;
v___x_355_ = ((lean_object*)(l_Lake_LeanExe_defaultFacetConfig___closed__0));
v___x_356_ = l_Lake_LeanExe_keyword;
v___x_357_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
lean_ctor_set(v___x_357_, 2, v___x_354_);
lean_ctor_set(v___x_357_, 3, v___f_352_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*4, v___x_353_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*4 + 1, v___x_351_);
return v___x_357_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig(void){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lake_LeanExe_defaultFacetConfig___closed__1, &l_Lake_LeanExe_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanExe_defaultFacetConfig___closed__1);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object* v_k_359_, lean_object* v_v_360_, lean_object* v_t_361_){
_start:
{
if (lean_obj_tag(v_t_361_) == 0)
{
lean_object* v_size_362_; lean_object* v_k_363_; lean_object* v_v_364_; lean_object* v_l_365_; lean_object* v_r_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_646_; 
v_size_362_ = lean_ctor_get(v_t_361_, 0);
v_k_363_ = lean_ctor_get(v_t_361_, 1);
v_v_364_ = lean_ctor_get(v_t_361_, 2);
v_l_365_ = lean_ctor_get(v_t_361_, 3);
v_r_366_ = lean_ctor_get(v_t_361_, 4);
v_isSharedCheck_646_ = !lean_is_exclusive(v_t_361_);
if (v_isSharedCheck_646_ == 0)
{
v___x_368_ = v_t_361_;
v_isShared_369_ = v_isSharedCheck_646_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_r_366_);
lean_inc(v_l_365_);
lean_inc(v_v_364_);
lean_inc(v_k_363_);
lean_inc(v_size_362_);
lean_dec(v_t_361_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_646_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___x_370_; 
v___x_370_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_359_, v_k_363_);
switch(v___x_370_)
{
case 0:
{
lean_object* v_impl_371_; lean_object* v___x_372_; 
lean_dec(v_size_362_);
v_impl_371_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_359_, v_v_360_, v_l_365_);
v___x_372_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_366_) == 0)
{
lean_object* v_size_373_; lean_object* v_size_374_; lean_object* v_k_375_; lean_object* v_v_376_; lean_object* v_l_377_; lean_object* v_r_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_size_373_ = lean_ctor_get(v_r_366_, 0);
v_size_374_ = lean_ctor_get(v_impl_371_, 0);
lean_inc(v_size_374_);
v_k_375_ = lean_ctor_get(v_impl_371_, 1);
lean_inc(v_k_375_);
v_v_376_ = lean_ctor_get(v_impl_371_, 2);
lean_inc(v_v_376_);
v_l_377_ = lean_ctor_get(v_impl_371_, 3);
lean_inc(v_l_377_);
v_r_378_ = lean_ctor_get(v_impl_371_, 4);
lean_inc(v_r_378_);
v___x_379_ = lean_unsigned_to_nat(3u);
v___x_380_ = lean_nat_mul(v___x_379_, v_size_373_);
v___x_381_ = lean_nat_dec_lt(v___x_380_, v_size_374_);
lean_dec(v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec(v_r_378_);
lean_dec(v_l_377_);
lean_dec(v_v_376_);
lean_dec(v_k_375_);
v___x_382_ = lean_nat_add(v___x_372_, v_size_374_);
lean_dec(v_size_374_);
v___x_383_ = lean_nat_add(v___x_382_, v_size_373_);
lean_dec(v___x_382_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 3, v_impl_371_);
lean_ctor_set(v___x_368_, 0, v___x_383_);
v___x_385_ = v___x_368_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_impl_371_);
lean_ctor_set(v_reuseFailAlloc_386_, 4, v_r_366_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_452_; 
v_isSharedCheck_452_ = !lean_is_exclusive(v_impl_371_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; lean_object* v_unused_457_; 
v_unused_453_ = lean_ctor_get(v_impl_371_, 4);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_impl_371_, 3);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_impl_371_, 2);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_impl_371_, 1);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_impl_371_, 0);
lean_dec(v_unused_457_);
v___x_388_ = v_impl_371_;
v_isShared_389_ = v_isSharedCheck_452_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_impl_371_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_452_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_size_390_; lean_object* v_size_391_; lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v_l_394_; lean_object* v_r_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_size_390_ = lean_ctor_get(v_l_377_, 0);
v_size_391_ = lean_ctor_get(v_r_378_, 0);
v_k_392_ = lean_ctor_get(v_r_378_, 1);
v_v_393_ = lean_ctor_get(v_r_378_, 2);
v_l_394_ = lean_ctor_get(v_r_378_, 3);
v_r_395_ = lean_ctor_get(v_r_378_, 4);
v___x_396_ = lean_unsigned_to_nat(2u);
v___x_397_ = lean_nat_mul(v___x_396_, v_size_390_);
v___x_398_ = lean_nat_dec_lt(v_size_391_, v___x_397_);
lean_dec(v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_427_; 
lean_inc(v_r_395_);
lean_inc(v_l_394_);
lean_inc(v_v_393_);
lean_inc(v_k_392_);
v_isSharedCheck_427_ = !lean_is_exclusive(v_r_378_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; 
v_unused_428_ = lean_ctor_get(v_r_378_, 4);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_r_378_, 3);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_r_378_, 2);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_r_378_, 1);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_r_378_, 0);
lean_dec(v_unused_432_);
v___x_400_ = v_r_378_;
v_isShared_401_ = v_isSharedCheck_427_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_r_378_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_427_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___x_415_; lean_object* v___y_417_; 
v___x_402_ = lean_nat_add(v___x_372_, v_size_374_);
lean_dec(v_size_374_);
v___x_403_ = lean_nat_add(v___x_402_, v_size_373_);
lean_dec(v___x_402_);
v___x_415_ = lean_nat_add(v___x_372_, v_size_390_);
if (lean_obj_tag(v_l_394_) == 0)
{
lean_object* v_size_425_; 
v_size_425_ = lean_ctor_get(v_l_394_, 0);
lean_inc(v_size_425_);
v___y_417_ = v_size_425_;
goto v___jp_416_;
}
else
{
lean_object* v___x_426_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___y_417_ = v___x_426_;
goto v___jp_416_;
}
v___jp_404_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_nat_add(v___y_405_, v___y_407_);
lean_dec(v___y_407_);
lean_dec(v___y_405_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 4, v_r_366_);
lean_ctor_set(v___x_400_, 3, v_r_395_);
lean_ctor_set(v___x_400_, 2, v_v_364_);
lean_ctor_set(v___x_400_, 1, v_k_363_);
lean_ctor_set(v___x_400_, 0, v___x_408_);
v___x_410_ = v___x_400_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_r_395_);
lean_ctor_set(v_reuseFailAlloc_414_, 4, v_r_366_);
v___x_410_ = v_reuseFailAlloc_414_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v___x_410_);
lean_ctor_set(v___x_388_, 3, v___y_406_);
lean_ctor_set(v___x_388_, 2, v_v_393_);
lean_ctor_set(v___x_388_, 1, v_k_392_);
lean_ctor_set(v___x_388_, 0, v___x_403_);
v___x_412_ = v___x_388_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_k_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_v_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v___y_406_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
v___jp_416_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_nat_add(v___x_415_, v___y_417_);
lean_dec(v___y_417_);
lean_dec(v___x_415_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v_l_394_);
lean_ctor_set(v___x_368_, 3, v_l_377_);
lean_ctor_set(v___x_368_, 2, v_v_376_);
lean_ctor_set(v___x_368_, 1, v_k_375_);
lean_ctor_set(v___x_368_, 0, v___x_418_);
v___x_420_ = v___x_368_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_k_375_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_v_376_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_l_377_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_l_394_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; 
v___x_421_ = lean_nat_add(v___x_372_, v_size_373_);
if (lean_obj_tag(v_r_395_) == 0)
{
lean_object* v_size_422_; 
v_size_422_ = lean_ctor_get(v_r_395_, 0);
lean_inc(v_size_422_);
v___y_405_ = v___x_421_;
v___y_406_ = v___x_420_;
v___y_407_ = v_size_422_;
goto v___jp_404_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v___y_405_ = v___x_421_;
v___y_406_ = v___x_420_;
v___y_407_ = v___x_423_;
goto v___jp_404_;
}
}
}
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
lean_del_object(v___x_368_);
v___x_433_ = lean_nat_add(v___x_372_, v_size_374_);
lean_dec(v_size_374_);
v___x_434_ = lean_nat_add(v___x_433_, v_size_373_);
lean_dec(v___x_433_);
v___x_435_ = lean_nat_add(v___x_372_, v_size_373_);
v___x_436_ = lean_nat_add(v___x_435_, v_size_391_);
lean_dec(v___x_435_);
lean_inc_ref(v_r_366_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v_r_366_);
lean_ctor_set(v___x_388_, 3, v_r_378_);
lean_ctor_set(v___x_388_, 2, v_v_364_);
lean_ctor_set(v___x_388_, 1, v_k_363_);
lean_ctor_set(v___x_388_, 0, v___x_436_);
v___x_438_ = v___x_388_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_r_378_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_r_366_);
v___x_438_ = v_reuseFailAlloc_451_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_isSharedCheck_445_ = !lean_is_exclusive(v_r_366_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_446_ = lean_ctor_get(v_r_366_, 4);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_r_366_, 3);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_r_366_, 2);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_r_366_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_r_366_, 0);
lean_dec(v_unused_450_);
v___x_440_ = v_r_366_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_r_366_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 4, v___x_438_);
lean_ctor_set(v___x_440_, 3, v_l_377_);
lean_ctor_set(v___x_440_, 2, v_v_376_);
lean_ctor_set(v___x_440_, 1, v_k_375_);
lean_ctor_set(v___x_440_, 0, v___x_434_);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_k_375_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_v_376_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_l_377_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v___x_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_458_; 
v_l_458_ = lean_ctor_get(v_impl_371_, 3);
lean_inc(v_l_458_);
if (lean_obj_tag(v_l_458_) == 0)
{
lean_object* v_r_459_; lean_object* v_k_460_; lean_object* v_v_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_472_; 
v_r_459_ = lean_ctor_get(v_impl_371_, 4);
v_k_460_ = lean_ctor_get(v_impl_371_, 1);
v_v_461_ = lean_ctor_get(v_impl_371_, 2);
v_isSharedCheck_472_ = !lean_is_exclusive(v_impl_371_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; 
v_unused_473_ = lean_ctor_get(v_impl_371_, 3);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_impl_371_, 0);
lean_dec(v_unused_474_);
v___x_463_ = v_impl_371_;
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_r_459_);
lean_inc(v_v_461_);
lean_inc(v_k_460_);
lean_dec(v_impl_371_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_459_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 3, v_r_459_);
lean_ctor_set(v___x_463_, 2, v_v_364_);
lean_ctor_set(v___x_463_, 1, v_k_363_);
lean_ctor_set(v___x_463_, 0, v___x_372_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_r_459_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_r_459_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v___x_467_);
lean_ctor_set(v___x_368_, 3, v_l_458_);
lean_ctor_set(v___x_368_, 2, v_v_461_);
lean_ctor_set(v___x_368_, 1, v_k_460_);
lean_ctor_set(v___x_368_, 0, v___x_465_);
v___x_469_ = v___x_368_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_v_461_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_l_458_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_r_475_; 
v_r_475_ = lean_ctor_get(v_impl_371_, 4);
lean_inc(v_r_475_);
if (lean_obj_tag(v_r_475_) == 0)
{
lean_object* v_k_476_; lean_object* v_v_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_500_; 
v_k_476_ = lean_ctor_get(v_impl_371_, 1);
v_v_477_ = lean_ctor_get(v_impl_371_, 2);
v_isSharedCheck_500_ = !lean_is_exclusive(v_impl_371_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_501_ = lean_ctor_get(v_impl_371_, 4);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_impl_371_, 3);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_impl_371_, 0);
lean_dec(v_unused_503_);
v___x_479_ = v_impl_371_;
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_v_477_);
lean_inc(v_k_476_);
lean_dec(v_impl_371_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_k_481_; lean_object* v_v_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_496_; 
v_k_481_ = lean_ctor_get(v_r_475_, 1);
v_v_482_ = lean_ctor_get(v_r_475_, 2);
v_isSharedCheck_496_ = !lean_is_exclusive(v_r_475_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_497_ = lean_ctor_get(v_r_475_, 4);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_r_475_, 3);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_r_475_, 0);
lean_dec(v_unused_499_);
v___x_484_ = v_r_475_;
v_isShared_485_ = v_isSharedCheck_496_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_v_482_);
lean_inc(v_k_481_);
lean_dec(v_r_475_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_496_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_unsigned_to_nat(3u);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 4, v_l_458_);
lean_ctor_set(v___x_484_, 3, v_l_458_);
lean_ctor_set(v___x_484_, 2, v_v_477_);
lean_ctor_set(v___x_484_, 1, v_k_476_);
lean_ctor_set(v___x_484_, 0, v___x_372_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_k_476_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_v_477_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_l_458_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_l_458_);
v___x_488_ = v_reuseFailAlloc_495_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_l_458_);
lean_ctor_set(v___x_479_, 2, v_v_364_);
lean_ctor_set(v___x_479_, 1, v_k_363_);
lean_ctor_set(v___x_479_, 0, v___x_372_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_l_458_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_l_458_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v___x_490_);
lean_ctor_set(v___x_368_, 3, v___x_488_);
lean_ctor_set(v___x_368_, 2, v_v_482_);
lean_ctor_set(v___x_368_, 1, v_k_481_);
lean_ctor_set(v___x_368_, 0, v___x_486_);
v___x_492_ = v___x_368_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_v_482_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_unsigned_to_nat(2u);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v_r_475_);
lean_ctor_set(v___x_368_, 3, v_impl_371_);
lean_ctor_set(v___x_368_, 0, v___x_504_);
v___x_506_ = v___x_368_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_impl_371_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_r_475_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
case 1:
{
lean_object* v___x_509_; 
lean_dec(v_v_364_);
lean_dec(v_k_363_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 2, v_v_360_);
lean_ctor_set(v___x_368_, 1, v_k_359_);
v___x_509_ = v___x_368_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_size_362_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_l_365_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_r_366_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
default: 
{
lean_object* v_impl_511_; lean_object* v___x_512_; 
lean_dec(v_size_362_);
v_impl_511_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_359_, v_v_360_, v_r_366_);
v___x_512_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_365_) == 0)
{
lean_object* v_size_513_; lean_object* v_size_514_; lean_object* v_k_515_; lean_object* v_v_516_; lean_object* v_l_517_; lean_object* v_r_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_size_513_ = lean_ctor_get(v_l_365_, 0);
v_size_514_ = lean_ctor_get(v_impl_511_, 0);
lean_inc(v_size_514_);
v_k_515_ = lean_ctor_get(v_impl_511_, 1);
lean_inc(v_k_515_);
v_v_516_ = lean_ctor_get(v_impl_511_, 2);
lean_inc(v_v_516_);
v_l_517_ = lean_ctor_get(v_impl_511_, 3);
lean_inc(v_l_517_);
v_r_518_ = lean_ctor_get(v_impl_511_, 4);
lean_inc(v_r_518_);
v___x_519_ = lean_unsigned_to_nat(3u);
v___x_520_ = lean_nat_mul(v___x_519_, v_size_513_);
v___x_521_ = lean_nat_dec_lt(v___x_520_, v_size_514_);
lean_dec(v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec(v_r_518_);
lean_dec(v_l_517_);
lean_dec(v_v_516_);
lean_dec(v_k_515_);
v___x_522_ = lean_nat_add(v___x_512_, v_size_513_);
v___x_523_ = lean_nat_add(v___x_522_, v_size_514_);
lean_dec(v_size_514_);
lean_dec(v___x_522_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v_impl_511_);
lean_ctor_set(v___x_368_, 0, v___x_523_);
v___x_525_ = v___x_368_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_l_365_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v_impl_511_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v_impl_511_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; 
v_unused_591_ = lean_ctor_get(v_impl_511_, 4);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_impl_511_, 3);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_impl_511_, 2);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_impl_511_, 1);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_impl_511_, 0);
lean_dec(v_unused_595_);
v___x_528_ = v_impl_511_;
v_isShared_529_ = v_isSharedCheck_590_;
goto v_resetjp_527_;
}
else
{
lean_dec(v_impl_511_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_590_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_size_530_; lean_object* v_k_531_; lean_object* v_v_532_; lean_object* v_l_533_; lean_object* v_r_534_; lean_object* v_size_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_size_530_ = lean_ctor_get(v_l_517_, 0);
v_k_531_ = lean_ctor_get(v_l_517_, 1);
v_v_532_ = lean_ctor_get(v_l_517_, 2);
v_l_533_ = lean_ctor_get(v_l_517_, 3);
v_r_534_ = lean_ctor_get(v_l_517_, 4);
v_size_535_ = lean_ctor_get(v_r_518_, 0);
v___x_536_ = lean_unsigned_to_nat(2u);
v___x_537_ = lean_nat_mul(v___x_536_, v_size_535_);
v___x_538_ = lean_nat_dec_lt(v_size_530_, v___x_537_);
lean_dec(v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_566_; 
lean_inc(v_r_534_);
lean_inc(v_l_533_);
lean_inc(v_v_532_);
lean_inc(v_k_531_);
v_isSharedCheck_566_ = !lean_is_exclusive(v_l_517_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; lean_object* v_unused_571_; 
v_unused_567_ = lean_ctor_get(v_l_517_, 4);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_l_517_, 3);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_l_517_, 2);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_l_517_, 1);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_l_517_, 0);
lean_dec(v_unused_571_);
v___x_540_ = v_l_517_;
v_isShared_541_ = v_isSharedCheck_566_;
goto v_resetjp_539_;
}
else
{
lean_dec(v_l_517_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_566_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_556_; 
v___x_542_ = lean_nat_add(v___x_512_, v_size_513_);
v___x_543_ = lean_nat_add(v___x_542_, v_size_514_);
lean_dec(v_size_514_);
if (lean_obj_tag(v_l_533_) == 0)
{
lean_object* v_size_564_; 
v_size_564_ = lean_ctor_get(v_l_533_, 0);
lean_inc(v_size_564_);
v___y_556_ = v_size_564_;
goto v___jp_555_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___y_556_ = v___x_565_;
goto v___jp_555_;
}
v___jp_544_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_nat_add(v___y_545_, v___y_547_);
lean_dec(v___y_547_);
lean_dec(v___y_545_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 4, v_r_518_);
lean_ctor_set(v___x_540_, 3, v_r_534_);
lean_ctor_set(v___x_540_, 2, v_v_516_);
lean_ctor_set(v___x_540_, 1, v_k_515_);
lean_ctor_set(v___x_540_, 0, v___x_548_);
v___x_550_ = v___x_540_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_k_515_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_v_516_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_r_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_r_518_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 4, v___x_550_);
lean_ctor_set(v___x_528_, 3, v___y_546_);
lean_ctor_set(v___x_528_, 2, v_v_532_);
lean_ctor_set(v___x_528_, 1, v_k_531_);
lean_ctor_set(v___x_528_, 0, v___x_543_);
v___x_552_ = v___x_528_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_531_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_v_532_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v___y_546_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
v___jp_555_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_nat_add(v___x_542_, v___y_556_);
lean_dec(v___y_556_);
lean_dec(v___x_542_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v_l_533_);
lean_ctor_set(v___x_368_, 0, v___x_557_);
v___x_559_ = v___x_368_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_l_365_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_l_533_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_nat_add(v___x_512_, v_size_535_);
if (lean_obj_tag(v_r_534_) == 0)
{
lean_object* v_size_561_; 
v_size_561_ = lean_ctor_get(v_r_534_, 0);
lean_inc(v_size_561_);
v___y_545_ = v___x_560_;
v___y_546_ = v___x_559_;
v___y_547_ = v_size_561_;
goto v___jp_544_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v___y_545_ = v___x_560_;
v___y_546_ = v___x_559_;
v___y_547_ = v___x_562_;
goto v___jp_544_;
}
}
}
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
lean_del_object(v___x_368_);
v___x_572_ = lean_nat_add(v___x_512_, v_size_513_);
v___x_573_ = lean_nat_add(v___x_572_, v_size_514_);
lean_dec(v_size_514_);
v___x_574_ = lean_nat_add(v___x_572_, v_size_530_);
lean_dec(v___x_572_);
lean_inc_ref(v_l_365_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 4, v_l_517_);
lean_ctor_set(v___x_528_, 3, v_l_365_);
lean_ctor_set(v___x_528_, 2, v_v_364_);
lean_ctor_set(v___x_528_, 1, v_k_363_);
lean_ctor_set(v___x_528_, 0, v___x_574_);
v___x_576_ = v___x_528_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_l_365_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_l_517_);
v___x_576_ = v_reuseFailAlloc_589_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
v_isSharedCheck_583_ = !lean_is_exclusive(v_l_365_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_584_ = lean_ctor_get(v_l_365_, 4);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_l_365_, 3);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_l_365_, 2);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_l_365_, 1);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_l_365_, 0);
lean_dec(v_unused_588_);
v___x_578_ = v_l_365_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_dec(v_l_365_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 4, v_r_518_);
lean_ctor_set(v___x_578_, 3, v___x_576_);
lean_ctor_set(v___x_578_, 2, v_v_516_);
lean_ctor_set(v___x_578_, 1, v_k_515_);
lean_ctor_set(v___x_578_, 0, v___x_573_);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_k_515_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_v_516_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v_r_518_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_596_; 
v_l_596_ = lean_ctor_get(v_impl_511_, 3);
lean_inc(v_l_596_);
if (lean_obj_tag(v_l_596_) == 0)
{
lean_object* v_r_597_; lean_object* v_k_598_; lean_object* v_v_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_622_; 
v_r_597_ = lean_ctor_get(v_impl_511_, 4);
v_k_598_ = lean_ctor_get(v_impl_511_, 1);
v_v_599_ = lean_ctor_get(v_impl_511_, 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v_impl_511_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_623_ = lean_ctor_get(v_impl_511_, 3);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_impl_511_, 0);
lean_dec(v_unused_624_);
v___x_601_ = v_impl_511_;
v_isShared_602_ = v_isSharedCheck_622_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_r_597_);
lean_inc(v_v_599_);
lean_inc(v_k_598_);
lean_dec(v_impl_511_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_622_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_k_603_; lean_object* v_v_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_618_; 
v_k_603_ = lean_ctor_get(v_l_596_, 1);
v_v_604_ = lean_ctor_get(v_l_596_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_l_596_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_619_ = lean_ctor_get(v_l_596_, 4);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_l_596_, 3);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_l_596_, 0);
lean_dec(v_unused_621_);
v___x_606_ = v_l_596_;
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_v_604_);
lean_inc(v_k_603_);
lean_dec(v_l_596_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_597_, 2);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 4, v_r_597_);
lean_ctor_set(v___x_606_, 3, v_r_597_);
lean_ctor_set(v___x_606_, 2, v_v_364_);
lean_ctor_set(v___x_606_, 1, v_k_363_);
lean_ctor_set(v___x_606_, 0, v___x_512_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_r_597_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_r_597_);
v___x_610_ = v_reuseFailAlloc_617_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
lean_inc(v_r_597_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 3, v_r_597_);
lean_ctor_set(v___x_601_, 0, v___x_512_);
v___x_612_ = v___x_601_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_v_599_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_r_597_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_r_597_);
v___x_612_ = v_reuseFailAlloc_616_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v___x_612_);
lean_ctor_set(v___x_368_, 3, v___x_610_);
lean_ctor_set(v___x_368_, 2, v_v_604_);
lean_ctor_set(v___x_368_, 1, v_k_603_);
lean_ctor_set(v___x_368_, 0, v___x_608_);
v___x_614_ = v___x_368_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_604_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
else
{
lean_object* v_r_625_; 
v_r_625_ = lean_ctor_get(v_impl_511_, 4);
lean_inc(v_r_625_);
if (lean_obj_tag(v_r_625_) == 0)
{
lean_object* v_k_626_; lean_object* v_v_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_638_; 
v_k_626_ = lean_ctor_get(v_impl_511_, 1);
v_v_627_ = lean_ctor_get(v_impl_511_, 2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_impl_511_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_639_ = lean_ctor_get(v_impl_511_, 4);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_impl_511_, 3);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_impl_511_, 0);
lean_dec(v_unused_641_);
v___x_629_ = v_impl_511_;
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_v_627_);
lean_inc(v_k_626_);
lean_dec(v_impl_511_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_unsigned_to_nat(3u);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 4, v_l_596_);
lean_ctor_set(v___x_629_, 2, v_v_364_);
lean_ctor_set(v___x_629_, 1, v_k_363_);
lean_ctor_set(v___x_629_, 0, v___x_512_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_l_596_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_l_596_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v_r_625_);
lean_ctor_set(v___x_368_, 3, v___x_633_);
lean_ctor_set(v___x_368_, 2, v_v_627_);
lean_ctor_set(v___x_368_, 1, v_k_626_);
lean_ctor_set(v___x_368_, 0, v___x_631_);
v___x_635_ = v___x_368_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_r_625_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(2u);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 4, v_impl_511_);
lean_ctor_set(v___x_368_, 3, v_r_625_);
lean_ctor_set(v___x_368_, 0, v___x_642_);
v___x_644_ = v___x_368_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_r_625_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v_impl_511_);
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
}
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v_k_359_);
lean_ctor_set(v___x_648_, 2, v_v_360_);
lean_ctor_set(v___x_648_, 3, v_t_361_);
lean_ctor_set(v___x_648_, 4, v_t_361_);
return v___x_648_;
}
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = lean_box(1);
v___x_650_ = l_Lake_LeanExe_defaultFacetConfig;
v___x_651_ = l_Lake_LeanExe_defaultFacet;
v___x_652_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_651_, v___x_650_, v___x_649_);
return v___x_652_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__0, &l_Lake_LeanExe_initFacetConfigs___closed__0_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__0);
v___x_654_ = l_Lake_LeanExe_exeFacetConfig;
v___x_655_ = l_Lake_LeanExe_exeFacet;
v___x_656_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_655_, v___x_654_, v___x_653_);
return v___x_656_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__1, &l_Lake_LeanExe_initFacetConfigs___closed__1_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__1);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object* v_00_u03b2_658_, lean_object* v_k_659_, lean_object* v_v_660_, lean_object* v_t_661_, lean_object* v_hl_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_659_, v_v_660_, v_t_661_);
return v___x_663_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Executable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LeanExe_exeFacetConfig = _init_l_Lake_LeanExe_exeFacetConfig();
lean_mark_persistent(l_Lake_LeanExe_exeFacetConfig);
l_Lake_LeanExe_defaultFacetConfig = _init_l_Lake_LeanExe_defaultFacetConfig();
lean_mark_persistent(l_Lake_LeanExe_defaultFacetConfig);
l_Lake_LeanExe_initFacetConfigs = _init_l_Lake_LeanExe_initFacetConfigs();
lean_mark_persistent(l_Lake_LeanExe_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Executable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* initialize_Lake_Build_Common(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Executable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Target_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Executable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Executable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Executable(builtin);
}
#ifdef __cplusplus
}
#endif
