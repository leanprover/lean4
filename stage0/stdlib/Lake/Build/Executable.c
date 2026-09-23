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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object*);
extern lean_object* l_Lake_Module_linkInfoNoExportFacet;
extern lean_object* l_Lake_Module_keyword;
extern lean_object* l_Lake_Module_linkInfoExportFacet;
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v_args_75_; lean_object* v_objs_76_; lean_object* v_libs_77_; lean_object* v___x_78_; lean_object* v_args_79_; uint64_t v___y_81_; uint64_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
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
v___x_120_ = l_Lake_Hash_nil;
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_array_get_size(v___x_78_);
v___x_123_ = lean_nat_dec_lt(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
v___y_81_ = v___x_120_;
goto v___jp_80_;
}
else
{
size_t v___x_124_; size_t v___x_125_; uint64_t v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_122_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___x_78_, v___x_124_, v___x_125_, v___x_120_);
v___y_81_ = v___x_126_;
goto v___jp_80_;
}
v___jp_80_:
{
lean_object* v_config_82_; lean_object* v_log_83_; uint8_t v_action_84_; uint8_t v_wantsRebuild_85_; uint8_t v_canceled_86_; lean_object* v_trace_87_; lean_object* v_buildTime_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_119_; 
v_config_82_ = lean_ctor_get(v_pkg_64_, 6);
lean_inc_ref(v_config_82_);
v_log_83_ = lean_ctor_get(v___y_73_, 0);
v_action_84_ = lean_ctor_get_uint8(v___y_73_, sizeof(void*)*3);
v_wantsRebuild_85_ = lean_ctor_get_uint8(v___y_73_, sizeof(void*)*3 + 1);
v_canceled_86_ = lean_ctor_get_uint8(v___y_73_, sizeof(void*)*3 + 2);
v_trace_87_ = lean_ctor_get(v___y_73_, 1);
v_buildTime_88_ = lean_ctor_get(v___y_73_, 2);
v_isSharedCheck_119_ = !lean_is_exclusive(v___y_73_);
if (v_isSharedCheck_119_ == 0)
{
v___x_90_ = v___y_73_;
v_isShared_91_ = v_isSharedCheck_119_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_buildTime_88_);
lean_inc(v_trace_87_);
lean_inc(v_log_83_);
lean_dec(v___y_73_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_119_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_dir_92_; lean_object* v_buildDir_93_; lean_object* v_binDir_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v_dir_92_ = lean_ctor_get(v_pkg_64_, 4);
lean_inc_ref(v_dir_92_);
lean_dec_ref(v_pkg_64_);
v_buildDir_93_ = lean_ctor_get(v_config_82_, 5);
lean_inc_ref(v_buildDir_93_);
v_binDir_94_ = lean_ctor_get(v_config_82_, 8);
lean_inc_ref(v_binDir_94_);
lean_dec_ref(v_config_82_);
v___x_95_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0));
v___x_96_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1));
v___x_97_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2));
v___x_98_ = lean_array_to_list(v___x_78_);
v___x_99_ = l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(v___x_98_);
lean_dec(v___x_98_);
v___x_100_ = lean_string_append(v___x_97_, v___x_99_);
lean_dec_ref(v___x_99_);
v___x_101_ = lean_string_append(v___x_96_, v___x_100_);
lean_dec_ref(v___x_100_);
v___x_102_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4);
v___x_103_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_95_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_ctor_set_uint64(v___x_103_, sizeof(void*)*3, v___y_81_);
v___x_104_ = l_Lake_BuildTrace_mix(v_trace_87_, v___x_103_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_104_);
v___x_106_ = v___x_90_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_log_83_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_buildTime_88_);
lean_ctor_set_uint8(v_reuseFailAlloc_118_, sizeof(void*)*3, v_action_84_);
lean_ctor_set_uint8(v_reuseFailAlloc_118_, sizeof(void*)*3 + 1, v_wantsRebuild_85_);
lean_ctor_set_uint8(v_reuseFailAlloc_118_, sizeof(void*)*3 + 2, v_canceled_86_);
v___x_106_ = v_reuseFailAlloc_118_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_107_ = l_System_FilePath_normalize(v_buildDir_93_);
v___x_108_ = l_Lake_joinRelative(v_dir_92_, v___x_107_);
v___x_109_ = l_System_FilePath_normalize(v_binDir_94_);
v___x_110_ = l_Lake_joinRelative(v___x_108_, v___x_109_);
v___x_111_ = l_System_FilePath_exeExtension;
v___x_112_ = l_System_FilePath_addExtension(v_exeName_65_, v___x_111_);
v___x_113_ = l_Lake_joinRelative(v___x_110_, v___x_112_);
v___x_114_ = l_System_Platform_isWindows;
v___x_115_ = lean_strict_and(v___x_114_, v_supportInterpreter_66_);
v___x_116_ = lean_box(0);
v___x_117_ = l_Lake_buildLeanExeSync(v___x_113_, v_objs_76_, v_libs_77_, v_args_79_, v___x_115_, v___x_116_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___x_106_);
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(lean_object* v_self_127_, lean_object* v_pkg_128_, lean_object* v_exeName_129_, lean_object* v_supportInterpreter_130_, lean_object* v_info_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
uint8_t v_supportInterpreter_boxed_139_; lean_object* v_res_140_; 
v_supportInterpreter_boxed_139_ = lean_unbox(v_supportInterpreter_130_);
v_res_140_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(v_self_127_, v_pkg_128_, v_exeName_129_, v_supportInterpreter_boxed_139_, v_info_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v_self_127_);
return v_res_140_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__0));
v___x_143_ = l_Lake_BuildTrace_nil(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(lean_object* v___x_144_, lean_object* v___f_145_, lean_object* v_infoJob_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = 0;
v___x_156_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1);
v___x_157_ = l_Lake_Job_mapM___redArg(v___x_144_, v_infoJob_146_, v___f_145_, v___x_154_, v___x_155_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___y_152_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed(lean_object* v___x_159_, lean_object* v___f_160_, lean_object* v_infoJob_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(v___x_159_, v___f_160_, v_infoJob_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec(v___y_164_);
lean_dec(v___y_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(uint8_t v_supportInterpreter_170_, lean_object* v_pkg_171_, lean_object* v_config_172_, lean_object* v_name_173_, lean_object* v_root_174_, lean_object* v___x_175_, lean_object* v___f_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
if (v_supportInterpreter_170_ == 0)
{
lean_object* v_keyName_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_keyName_184_ = lean_ctor_get(v_pkg_171_, 2);
lean_inc(v_keyName_184_);
v___x_185_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_172_);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v_pkg_171_);
lean_ctor_set(v___x_186_, 1, v_name_173_);
lean_ctor_set(v___x_186_, 2, v___x_185_);
lean_inc(v_root_174_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_root_174_);
v___x_188_ = l_Lake_Module_linkInfoNoExportFacet;
v___x_189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_189_, 0, v_keyName_184_);
lean_ctor_set(v___x_189_, 1, v_root_174_);
v___x_190_ = l_Lake_Module_keyword;
v___x_191_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
lean_ctor_set(v___x_191_, 2, v___x_187_);
lean_ctor_set(v___x_191_, 3, v___x_188_);
lean_inc_ref(v___y_177_);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc(v___y_179_);
lean_inc(v___x_175_);
v___x_192_ = lean_apply_7(v___y_177_, v___x_191_, v___x_175_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, lean_box(0));
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v_a_194_; lean_object* v___x_195_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
v_a_194_ = lean_ctor_get(v___x_192_, 1);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_192_, 2);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc(v___y_179_);
v___x_195_ = lean_apply_8(v___f_176_, v_a_193_, v___y_177_, v___x_175_, v___y_179_, v___y_180_, v___y_181_, v_a_194_, lean_box(0));
return v___x_195_;
}
else
{
lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v___y_177_);
lean_dec_ref(v___f_176_);
lean_dec(v___x_175_);
v_a_196_ = lean_ctor_get(v___x_192_, 0);
v_a_197_ = lean_ctor_get(v___x_192_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_192_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_inc(v_a_196_);
lean_dec(v___x_192_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_196_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_keyName_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_keyName_205_ = lean_ctor_get(v_pkg_171_, 2);
lean_inc(v_keyName_205_);
v___x_206_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_172_);
v___x_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_207_, 0, v_pkg_171_);
lean_ctor_set(v___x_207_, 1, v_name_173_);
lean_ctor_set(v___x_207_, 2, v___x_206_);
lean_inc(v_root_174_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_root_174_);
v___x_209_ = l_Lake_Module_linkInfoExportFacet;
v___x_210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_210_, 0, v_keyName_205_);
lean_ctor_set(v___x_210_, 1, v_root_174_);
v___x_211_ = l_Lake_Module_keyword;
v___x_212_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
lean_ctor_set(v___x_212_, 2, v___x_208_);
lean_ctor_set(v___x_212_, 3, v___x_209_);
lean_inc_ref(v___y_177_);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc(v___y_179_);
lean_inc(v___x_175_);
v___x_213_ = lean_apply_7(v___y_177_, v___x_212_, v___x_175_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
v_a_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_213_, 2);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc(v___y_179_);
v___x_216_ = lean_apply_8(v___f_176_, v_a_214_, v___y_177_, v___x_175_, v___y_179_, v___y_180_, v___y_181_, v_a_215_, lean_box(0));
return v___x_216_;
}
else
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v___y_177_);
lean_dec_ref(v___f_176_);
lean_dec(v___x_175_);
v_a_217_ = lean_ctor_get(v___x_213_, 0);
v_a_218_ = lean_ctor_get(v___x_213_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_213_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_inc(v_a_217_);
lean_dec(v___x_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_217_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed(lean_object* v_supportInterpreter_226_, lean_object* v_pkg_227_, lean_object* v_config_228_, lean_object* v_name_229_, lean_object* v_root_230_, lean_object* v___x_231_, lean_object* v___f_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_supportInterpreter_boxed_240_; lean_object* v_res_241_; 
v_supportInterpreter_boxed_240_ = lean_unbox(v_supportInterpreter_226_);
v_res_241_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(v_supportInterpreter_boxed_240_, v_pkg_227_, v_config_228_, v_name_229_, v_root_230_, v___x_231_, v___f_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec(v___y_235_);
lean_dec(v___y_234_);
lean_dec(v_config_228_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object* v_self_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_config_251_; lean_object* v_pkg_252_; lean_object* v_name_253_; lean_object* v_root_254_; lean_object* v_exeName_255_; uint8_t v_supportInterpreter_256_; lean_object* v___x_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___f_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___f_267_; uint8_t v___x_268_; lean_object* v___x_269_; 
v_config_251_ = lean_ctor_get(v_self_243_, 2);
lean_inc(v_config_251_);
v_pkg_252_ = lean_ctor_get(v_self_243_, 0);
lean_inc_ref_n(v_pkg_252_, 3);
v_name_253_ = lean_ctor_get(v_self_243_, 1);
lean_inc_n(v_name_253_, 2);
v_root_254_ = lean_ctor_get(v_config_251_, 2);
lean_inc(v_root_254_);
v_exeName_255_ = lean_ctor_get(v_config_251_, 3);
v_supportInterpreter_256_ = lean_ctor_get_uint8(v_config_251_, sizeof(void*)*7);
v___x_257_ = lean_box(v_supportInterpreter_256_);
lean_inc_ref(v_exeName_255_);
v___f_258_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed), 12, 4);
lean_closure_set(v___f_258_, 0, v_self_243_);
lean_closure_set(v___f_258_, 1, v_pkg_252_);
lean_closure_set(v___f_258_, 2, v_exeName_255_);
lean_closure_set(v___f_258_, 3, v___x_257_);
v___x_259_ = l_Lake_instDataKindFilePath;
v___f_260_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed), 10, 2);
lean_closure_set(v___f_260_, 0, v___x_259_);
lean_closure_set(v___f_260_, 1, v___f_258_);
v___x_261_ = 1;
v___x_262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_253_, v___x_261_);
v___x_263_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0));
v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_pkg_252_);
v___x_266_ = lean_box(v_supportInterpreter_256_);
v___f_267_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed), 14, 7);
lean_closure_set(v___f_267_, 0, v___x_266_);
lean_closure_set(v___f_267_, 1, v_pkg_252_);
lean_closure_set(v___f_267_, 2, v_config_251_);
lean_closure_set(v___f_267_, 3, v_name_253_);
lean_closure_set(v___f_267_, 4, v_root_254_);
lean_closure_set(v___f_267_, 5, v___x_265_);
lean_closure_set(v___f_267_, 6, v___f_260_);
v___x_268_ = 0;
v___x_269_ = l_Lake_ensureJob___redArg(v___x_259_, v___f_267_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_294_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_a_271_ = lean_ctor_get(v___x_269_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_294_ == 0)
{
v___x_273_ = v___x_269_;
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_task_275_; lean_object* v_kind_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_292_; 
v_task_275_ = lean_ctor_get(v_a_270_, 0);
v_kind_276_ = lean_ctor_get(v_a_270_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_a_270_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_a_270_, 2);
lean_dec(v_unused_293_);
v___x_278_ = v_a_270_;
v_isShared_279_ = v_isSharedCheck_292_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_kind_276_);
lean_inc(v_task_275_);
lean_dec(v_a_270_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_292_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_registeredJobs_280_; lean_object* v_job_282_; 
v_registeredJobs_280_ = lean_ctor_get(v_a_248_, 4);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 2, v___x_264_);
v_job_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_task_275_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_kind_276_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v___x_264_);
v_job_282_ = v_reuseFailAlloc_291_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
lean_ctor_set_uint8(v_job_282_, sizeof(void*)*3, v___x_268_);
v___x_283_ = lean_st_ref_take(v_registeredJobs_280_);
lean_inc_ref(v_job_282_);
v___x_284_ = l_Lake_Job_toOpaque___redArg(v_job_282_);
v___x_285_ = lean_array_push(v___x_283_, v___x_284_);
v___x_286_ = lean_st_ref_put(v_registeredJobs_280_, v___x_285_);
v___x_287_ = l_Lake_Job_renew___redArg(v_job_282_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_287_);
v___x_289_ = v___x_273_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_a_271_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_264_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object* v_self_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(v_self_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec(v_a_298_);
lean_dec(v_a_297_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t v_fmt_304_, lean_object* v_a_305_){
_start:
{
if (v_fmt_304_ == 0)
{
return v_a_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = l_Lake_mkRelPathString(v_a_305_);
v___x_307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = l_Lean_Json_compress(v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object* v_fmt_309_, lean_object* v_a_310_){
_start:
{
uint8_t v_fmt_boxed_311_; lean_object* v_res_312_; 
v_fmt_boxed_311_ = lean_unbox(v_fmt_309_);
v_res_312_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(v_fmt_boxed_311_, v_a_310_);
return v_res_312_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___f_315_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_316_ = 1;
v___x_317_ = l_Lake_instDataKindFilePath;
v___x_318_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__1));
v___x_319_ = l_Lake_LeanExe_keyword;
v___x_320_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_317_);
lean_ctor_set(v___x_320_, 3, v___f_315_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*4, v___x_316_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*4 + 1, v___x_316_);
return v___x_320_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig(void){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lake_LeanExe_exeFacetConfig___closed__2, &l_Lake_LeanExe_exeFacetConfig___closed__2_once, _init_l_Lake_LeanExe_exeFacetConfig___closed__2);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object* v_lib_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_pkg_330_; lean_object* v_name_331_; lean_object* v_keyName_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_pkg_330_ = lean_ctor_get(v_lib_322_, 0);
v_name_331_ = lean_ctor_get(v_lib_322_, 1);
v_keyName_332_ = lean_ctor_get(v_pkg_330_, 2);
v___x_333_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_331_);
lean_inc(v_keyName_332_);
v___x_334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_334_, 0, v_keyName_332_);
lean_ctor_set(v___x_334_, 1, v_name_331_);
v___x_335_ = l_Lake_LeanExe_keyword;
v___x_336_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
lean_ctor_set(v___x_336_, 2, v_lib_322_);
lean_ctor_set(v___x_336_, 3, v___x_333_);
lean_inc_ref(v_a_327_);
lean_inc(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
v___x_337_ = lean_apply_7(v_a_323_, v___x_336_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object* v_lib_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(v_lib_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec(v_a_341_);
lean_dec(v_a_340_);
return v_res_346_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_348_; lean_object* v___f_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_348_ = 0;
v___f_349_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_350_ = 1;
v___x_351_ = l_Lake_instDataKindFilePath;
v___x_352_ = ((lean_object*)(l_Lake_LeanExe_defaultFacetConfig___closed__0));
v___x_353_ = l_Lake_LeanExe_keyword;
v___x_354_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
lean_ctor_set(v___x_354_, 2, v___x_351_);
lean_ctor_set(v___x_354_, 3, v___f_349_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*4, v___x_350_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*4 + 1, v___x_348_);
return v___x_354_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l_Lake_LeanExe_defaultFacetConfig___closed__1, &l_Lake_LeanExe_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanExe_defaultFacetConfig___closed__1);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object* v_k_356_, lean_object* v_v_357_, lean_object* v_t_358_){
_start:
{
if (lean_obj_tag(v_t_358_) == 0)
{
lean_object* v_size_359_; lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v_l_362_; lean_object* v_r_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_643_; 
v_size_359_ = lean_ctor_get(v_t_358_, 0);
v_k_360_ = lean_ctor_get(v_t_358_, 1);
v_v_361_ = lean_ctor_get(v_t_358_, 2);
v_l_362_ = lean_ctor_get(v_t_358_, 3);
v_r_363_ = lean_ctor_get(v_t_358_, 4);
v_isSharedCheck_643_ = !lean_is_exclusive(v_t_358_);
if (v_isSharedCheck_643_ == 0)
{
v___x_365_ = v_t_358_;
v_isShared_366_ = v_isSharedCheck_643_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_r_363_);
lean_inc(v_l_362_);
lean_inc(v_v_361_);
lean_inc(v_k_360_);
lean_inc(v_size_359_);
lean_dec(v_t_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_643_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
uint8_t v___x_367_; 
v___x_367_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_356_, v_k_360_);
switch(v___x_367_)
{
case 0:
{
lean_object* v_impl_368_; lean_object* v___x_369_; 
lean_dec(v_size_359_);
v_impl_368_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_356_, v_v_357_, v_l_362_);
v___x_369_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_363_) == 0)
{
lean_object* v_size_370_; lean_object* v_size_371_; lean_object* v_k_372_; lean_object* v_v_373_; lean_object* v_l_374_; lean_object* v_r_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_size_370_ = lean_ctor_get(v_r_363_, 0);
v_size_371_ = lean_ctor_get(v_impl_368_, 0);
lean_inc(v_size_371_);
v_k_372_ = lean_ctor_get(v_impl_368_, 1);
lean_inc(v_k_372_);
v_v_373_ = lean_ctor_get(v_impl_368_, 2);
lean_inc(v_v_373_);
v_l_374_ = lean_ctor_get(v_impl_368_, 3);
lean_inc(v_l_374_);
v_r_375_ = lean_ctor_get(v_impl_368_, 4);
lean_inc(v_r_375_);
v___x_376_ = lean_unsigned_to_nat(3u);
v___x_377_ = lean_nat_mul(v___x_376_, v_size_370_);
v___x_378_ = lean_nat_dec_lt(v___x_377_, v_size_371_);
lean_dec(v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec(v_r_375_);
lean_dec(v_l_374_);
lean_dec(v_v_373_);
lean_dec(v_k_372_);
v___x_379_ = lean_nat_add(v___x_369_, v_size_371_);
lean_dec(v_size_371_);
v___x_380_ = lean_nat_add(v___x_379_, v_size_370_);
lean_dec(v___x_379_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 3, v_impl_368_);
lean_ctor_set(v___x_365_, 0, v___x_380_);
v___x_382_ = v___x_365_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_impl_368_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_r_363_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v_impl_368_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_450_ = lean_ctor_get(v_impl_368_, 4);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_impl_368_, 3);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_impl_368_, 2);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_impl_368_, 1);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_impl_368_, 0);
lean_dec(v_unused_454_);
v___x_385_ = v_impl_368_;
v_isShared_386_ = v_isSharedCheck_449_;
goto v_resetjp_384_;
}
else
{
lean_dec(v_impl_368_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_449_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_size_387_; lean_object* v_size_388_; lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_l_391_; lean_object* v_r_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_size_387_ = lean_ctor_get(v_l_374_, 0);
v_size_388_ = lean_ctor_get(v_r_375_, 0);
v_k_389_ = lean_ctor_get(v_r_375_, 1);
v_v_390_ = lean_ctor_get(v_r_375_, 2);
v_l_391_ = lean_ctor_get(v_r_375_, 3);
v_r_392_ = lean_ctor_get(v_r_375_, 4);
v___x_393_ = lean_unsigned_to_nat(2u);
v___x_394_ = lean_nat_mul(v___x_393_, v_size_387_);
v___x_395_ = lean_nat_dec_lt(v_size_388_, v___x_394_);
lean_dec(v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_424_; 
lean_inc(v_r_392_);
lean_inc(v_l_391_);
lean_inc(v_v_390_);
lean_inc(v_k_389_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_r_375_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; lean_object* v_unused_427_; lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_425_ = lean_ctor_get(v_r_375_, 4);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_r_375_, 3);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_r_375_, 2);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_r_375_, 1);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_r_375_, 0);
lean_dec(v_unused_429_);
v___x_397_ = v_r_375_;
v_isShared_398_ = v_isSharedCheck_424_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_r_375_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_424_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___x_412_; lean_object* v___y_414_; 
v___x_399_ = lean_nat_add(v___x_369_, v_size_371_);
lean_dec(v_size_371_);
v___x_400_ = lean_nat_add(v___x_399_, v_size_370_);
lean_dec(v___x_399_);
v___x_412_ = lean_nat_add(v___x_369_, v_size_387_);
if (lean_obj_tag(v_l_391_) == 0)
{
lean_object* v_size_422_; 
v_size_422_ = lean_ctor_get(v_l_391_, 0);
lean_inc(v_size_422_);
v___y_414_ = v_size_422_;
goto v___jp_413_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v___y_414_ = v___x_423_;
goto v___jp_413_;
}
v___jp_401_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_nat_add(v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec(v___y_403_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 4, v_r_363_);
lean_ctor_set(v___x_397_, 3, v_r_392_);
lean_ctor_set(v___x_397_, 2, v_v_361_);
lean_ctor_set(v___x_397_, 1, v_k_360_);
lean_ctor_set(v___x_397_, 0, v___x_405_);
v___x_407_ = v___x_397_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_r_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_r_363_);
v___x_407_ = v_reuseFailAlloc_411_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 4, v___x_407_);
lean_ctor_set(v___x_385_, 3, v___y_402_);
lean_ctor_set(v___x_385_, 2, v_v_390_);
lean_ctor_set(v___x_385_, 1, v_k_389_);
lean_ctor_set(v___x_385_, 0, v___x_400_);
v___x_409_ = v___x_385_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_389_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_390_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v___y_402_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
v___jp_413_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_nat_add(v___x_412_, v___y_414_);
lean_dec(v___y_414_);
lean_dec(v___x_412_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_l_391_);
lean_ctor_set(v___x_365_, 3, v_l_374_);
lean_ctor_set(v___x_365_, 2, v_v_373_);
lean_ctor_set(v___x_365_, 1, v_k_372_);
lean_ctor_set(v___x_365_, 0, v___x_415_);
v___x_417_ = v___x_365_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_k_372_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_v_373_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_l_374_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v_l_391_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; 
v___x_418_ = lean_nat_add(v___x_369_, v_size_370_);
if (lean_obj_tag(v_r_392_) == 0)
{
lean_object* v_size_419_; 
v_size_419_ = lean_ctor_get(v_r_392_, 0);
lean_inc(v_size_419_);
v___y_402_ = v___x_417_;
v___y_403_ = v___x_418_;
v___y_404_ = v_size_419_;
goto v___jp_401_;
}
else
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___y_402_ = v___x_417_;
v___y_403_ = v___x_418_;
v___y_404_ = v___x_420_;
goto v___jp_401_;
}
}
}
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
lean_del_object(v___x_365_);
v___x_430_ = lean_nat_add(v___x_369_, v_size_371_);
lean_dec(v_size_371_);
v___x_431_ = lean_nat_add(v___x_430_, v_size_370_);
lean_dec(v___x_430_);
v___x_432_ = lean_nat_add(v___x_369_, v_size_370_);
v___x_433_ = lean_nat_add(v___x_432_, v_size_388_);
lean_dec(v___x_432_);
lean_inc_ref(v_r_363_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 4, v_r_363_);
lean_ctor_set(v___x_385_, 3, v_r_375_);
lean_ctor_set(v___x_385_, 2, v_v_361_);
lean_ctor_set(v___x_385_, 1, v_k_360_);
lean_ctor_set(v___x_385_, 0, v___x_433_);
v___x_435_ = v___x_385_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_r_375_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_r_363_);
v___x_435_ = v_reuseFailAlloc_448_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_isSharedCheck_442_ = !lean_is_exclusive(v_r_363_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; 
v_unused_443_ = lean_ctor_get(v_r_363_, 4);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_r_363_, 3);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_r_363_, 2);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_r_363_, 1);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_r_363_, 0);
lean_dec(v_unused_447_);
v___x_437_ = v_r_363_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_r_363_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 4, v___x_435_);
lean_ctor_set(v___x_437_, 3, v_l_374_);
lean_ctor_set(v___x_437_, 2, v_v_373_);
lean_ctor_set(v___x_437_, 1, v_k_372_);
lean_ctor_set(v___x_437_, 0, v___x_431_);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_k_372_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_v_373_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_l_374_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v___x_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_455_; 
v_l_455_ = lean_ctor_get(v_impl_368_, 3);
lean_inc(v_l_455_);
if (lean_obj_tag(v_l_455_) == 0)
{
lean_object* v_r_456_; lean_object* v_k_457_; lean_object* v_v_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_469_; 
v_r_456_ = lean_ctor_get(v_impl_368_, 4);
v_k_457_ = lean_ctor_get(v_impl_368_, 1);
v_v_458_ = lean_ctor_get(v_impl_368_, 2);
v_isSharedCheck_469_ = !lean_is_exclusive(v_impl_368_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_470_ = lean_ctor_get(v_impl_368_, 3);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_impl_368_, 0);
lean_dec(v_unused_471_);
v___x_460_ = v_impl_368_;
v_isShared_461_ = v_isSharedCheck_469_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_r_456_);
lean_inc(v_v_458_);
lean_inc(v_k_457_);
lean_dec(v_impl_368_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_469_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_456_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 3, v_r_456_);
lean_ctor_set(v___x_460_, 2, v_v_361_);
lean_ctor_set(v___x_460_, 1, v_k_360_);
lean_ctor_set(v___x_460_, 0, v___x_369_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_r_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_r_456_);
v___x_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_466_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v___x_464_);
lean_ctor_set(v___x_365_, 3, v_l_455_);
lean_ctor_set(v___x_365_, 2, v_v_458_);
lean_ctor_set(v___x_365_, 1, v_k_457_);
lean_ctor_set(v___x_365_, 0, v___x_462_);
v___x_466_ = v___x_365_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_k_457_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_v_458_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_r_472_; 
v_r_472_ = lean_ctor_get(v_impl_368_, 4);
lean_inc(v_r_472_);
if (lean_obj_tag(v_r_472_) == 0)
{
lean_object* v_k_473_; lean_object* v_v_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_497_; 
v_k_473_ = lean_ctor_get(v_impl_368_, 1);
v_v_474_ = lean_ctor_get(v_impl_368_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v_impl_368_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; lean_object* v_unused_500_; 
v_unused_498_ = lean_ctor_get(v_impl_368_, 4);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_impl_368_, 3);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_impl_368_, 0);
lean_dec(v_unused_500_);
v___x_476_ = v_impl_368_;
v_isShared_477_ = v_isSharedCheck_497_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_v_474_);
lean_inc(v_k_473_);
lean_dec(v_impl_368_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_497_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_k_478_; lean_object* v_v_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_493_; 
v_k_478_ = lean_ctor_get(v_r_472_, 1);
v_v_479_ = lean_ctor_get(v_r_472_, 2);
v_isSharedCheck_493_ = !lean_is_exclusive(v_r_472_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_494_ = lean_ctor_get(v_r_472_, 4);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_r_472_, 3);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_r_472_, 0);
lean_dec(v_unused_496_);
v___x_481_ = v_r_472_;
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_v_479_);
lean_inc(v_k_478_);
lean_dec(v_r_472_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = lean_unsigned_to_nat(3u);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 4, v_l_455_);
lean_ctor_set(v___x_481_, 3, v_l_455_);
lean_ctor_set(v___x_481_, 2, v_v_474_);
lean_ctor_set(v___x_481_, 1, v_k_473_);
lean_ctor_set(v___x_481_, 0, v___x_369_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_k_473_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_v_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_l_455_);
v___x_485_ = v_reuseFailAlloc_492_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_l_455_);
lean_ctor_set(v___x_476_, 2, v_v_361_);
lean_ctor_set(v___x_476_, 1, v_k_360_);
lean_ctor_set(v___x_476_, 0, v___x_369_);
v___x_487_ = v___x_476_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_l_455_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_l_455_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v___x_487_);
lean_ctor_set(v___x_365_, 3, v___x_485_);
lean_ctor_set(v___x_365_, 2, v_v_479_);
lean_ctor_set(v___x_365_, 1, v_k_478_);
lean_ctor_set(v___x_365_, 0, v___x_483_);
v___x_489_ = v___x_365_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(2u);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_r_472_);
lean_ctor_set(v___x_365_, 3, v_impl_368_);
lean_ctor_set(v___x_365_, 0, v___x_501_);
v___x_503_ = v___x_365_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_impl_368_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v_r_472_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
case 1:
{
lean_object* v___x_506_; 
lean_dec(v_v_361_);
lean_dec(v_k_360_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 2, v_v_357_);
lean_ctor_set(v___x_365_, 1, v_k_356_);
v___x_506_ = v___x_365_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_size_359_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_k_356_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_v_357_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_l_362_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_r_363_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
default: 
{
lean_object* v_impl_508_; lean_object* v___x_509_; 
lean_dec(v_size_359_);
v_impl_508_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_356_, v_v_357_, v_r_363_);
v___x_509_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_362_) == 0)
{
lean_object* v_size_510_; lean_object* v_size_511_; lean_object* v_k_512_; lean_object* v_v_513_; lean_object* v_l_514_; lean_object* v_r_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_size_510_ = lean_ctor_get(v_l_362_, 0);
v_size_511_ = lean_ctor_get(v_impl_508_, 0);
lean_inc(v_size_511_);
v_k_512_ = lean_ctor_get(v_impl_508_, 1);
lean_inc(v_k_512_);
v_v_513_ = lean_ctor_get(v_impl_508_, 2);
lean_inc(v_v_513_);
v_l_514_ = lean_ctor_get(v_impl_508_, 3);
lean_inc(v_l_514_);
v_r_515_ = lean_ctor_get(v_impl_508_, 4);
lean_inc(v_r_515_);
v___x_516_ = lean_unsigned_to_nat(3u);
v___x_517_ = lean_nat_mul(v___x_516_, v_size_510_);
v___x_518_ = lean_nat_dec_lt(v___x_517_, v_size_511_);
lean_dec(v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_r_515_);
lean_dec(v_l_514_);
lean_dec(v_v_513_);
lean_dec(v_k_512_);
v___x_519_ = lean_nat_add(v___x_509_, v_size_510_);
v___x_520_ = lean_nat_add(v___x_519_, v_size_511_);
lean_dec(v_size_511_);
lean_dec(v___x_519_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_impl_508_);
lean_ctor_set(v___x_365_, 0, v___x_520_);
v___x_522_ = v___x_365_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_l_362_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_impl_508_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v_impl_508_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; 
v_unused_588_ = lean_ctor_get(v_impl_508_, 4);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_impl_508_, 3);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_impl_508_, 2);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_impl_508_, 1);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_impl_508_, 0);
lean_dec(v_unused_592_);
v___x_525_ = v_impl_508_;
v_isShared_526_ = v_isSharedCheck_587_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_impl_508_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_587_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_size_527_; lean_object* v_k_528_; lean_object* v_v_529_; lean_object* v_l_530_; lean_object* v_r_531_; lean_object* v_size_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_size_527_ = lean_ctor_get(v_l_514_, 0);
v_k_528_ = lean_ctor_get(v_l_514_, 1);
v_v_529_ = lean_ctor_get(v_l_514_, 2);
v_l_530_ = lean_ctor_get(v_l_514_, 3);
v_r_531_ = lean_ctor_get(v_l_514_, 4);
v_size_532_ = lean_ctor_get(v_r_515_, 0);
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = lean_nat_mul(v___x_533_, v_size_532_);
v___x_535_ = lean_nat_dec_lt(v_size_527_, v___x_534_);
lean_dec(v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_563_; 
lean_inc(v_r_531_);
lean_inc(v_l_530_);
lean_inc(v_v_529_);
lean_inc(v_k_528_);
v_isSharedCheck_563_ = !lean_is_exclusive(v_l_514_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_564_ = lean_ctor_get(v_l_514_, 4);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_l_514_, 3);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_514_, 2);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_514_, 1);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_l_514_, 0);
lean_dec(v_unused_568_);
v___x_537_ = v_l_514_;
v_isShared_538_ = v_isSharedCheck_563_;
goto v_resetjp_536_;
}
else
{
lean_dec(v_l_514_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_563_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_553_; 
v___x_539_ = lean_nat_add(v___x_509_, v_size_510_);
v___x_540_ = lean_nat_add(v___x_539_, v_size_511_);
lean_dec(v_size_511_);
if (lean_obj_tag(v_l_530_) == 0)
{
lean_object* v_size_561_; 
v_size_561_ = lean_ctor_get(v_l_530_, 0);
lean_inc(v_size_561_);
v___y_553_ = v_size_561_;
goto v___jp_552_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v___y_553_ = v___x_562_;
goto v___jp_552_;
}
v___jp_541_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_nat_add(v___y_542_, v___y_544_);
lean_dec(v___y_544_);
lean_dec(v___y_542_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 4, v_r_515_);
lean_ctor_set(v___x_537_, 3, v_r_531_);
lean_ctor_set(v___x_537_, 2, v_v_513_);
lean_ctor_set(v___x_537_, 1, v_k_512_);
lean_ctor_set(v___x_537_, 0, v___x_545_);
v___x_547_ = v___x_537_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_k_512_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_v_513_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_r_531_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_r_515_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 4, v___x_547_);
lean_ctor_set(v___x_525_, 3, v___y_543_);
lean_ctor_set(v___x_525_, 2, v_v_529_);
lean_ctor_set(v___x_525_, 1, v_k_528_);
lean_ctor_set(v___x_525_, 0, v___x_540_);
v___x_549_ = v___x_525_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v___y_543_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
v___jp_552_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_nat_add(v___x_539_, v___y_553_);
lean_dec(v___y_553_);
lean_dec(v___x_539_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_l_530_);
lean_ctor_set(v___x_365_, 0, v___x_554_);
v___x_556_ = v___x_365_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_l_362_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_l_530_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; 
v___x_557_ = lean_nat_add(v___x_509_, v_size_532_);
if (lean_obj_tag(v_r_531_) == 0)
{
lean_object* v_size_558_; 
v_size_558_ = lean_ctor_get(v_r_531_, 0);
lean_inc(v_size_558_);
v___y_542_ = v___x_557_;
v___y_543_ = v___x_556_;
v___y_544_ = v_size_558_;
goto v___jp_541_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___y_542_ = v___x_557_;
v___y_543_ = v___x_556_;
v___y_544_ = v___x_559_;
goto v___jp_541_;
}
}
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_del_object(v___x_365_);
v___x_569_ = lean_nat_add(v___x_509_, v_size_510_);
v___x_570_ = lean_nat_add(v___x_569_, v_size_511_);
lean_dec(v_size_511_);
v___x_571_ = lean_nat_add(v___x_569_, v_size_527_);
lean_dec(v___x_569_);
lean_inc_ref(v_l_362_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 4, v_l_514_);
lean_ctor_set(v___x_525_, 3, v_l_362_);
lean_ctor_set(v___x_525_, 2, v_v_361_);
lean_ctor_set(v___x_525_, 1, v_k_360_);
lean_ctor_set(v___x_525_, 0, v___x_571_);
v___x_573_ = v___x_525_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_l_362_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_l_514_);
v___x_573_ = v_reuseFailAlloc_586_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_isSharedCheck_580_ = !lean_is_exclusive(v_l_362_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; 
v_unused_581_ = lean_ctor_get(v_l_362_, 4);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_l_362_, 3);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_l_362_, 2);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_l_362_, 1);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_l_362_, 0);
lean_dec(v_unused_585_);
v___x_575_ = v_l_362_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_dec(v_l_362_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 4, v_r_515_);
lean_ctor_set(v___x_575_, 3, v___x_573_);
lean_ctor_set(v___x_575_, 2, v_v_513_);
lean_ctor_set(v___x_575_, 1, v_k_512_);
lean_ctor_set(v___x_575_, 0, v___x_570_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_k_512_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_v_513_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_r_515_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_593_; 
v_l_593_ = lean_ctor_get(v_impl_508_, 3);
lean_inc(v_l_593_);
if (lean_obj_tag(v_l_593_) == 0)
{
lean_object* v_r_594_; lean_object* v_k_595_; lean_object* v_v_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_619_; 
v_r_594_ = lean_ctor_get(v_impl_508_, 4);
v_k_595_ = lean_ctor_get(v_impl_508_, 1);
v_v_596_ = lean_ctor_get(v_impl_508_, 2);
v_isSharedCheck_619_ = !lean_is_exclusive(v_impl_508_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_620_ = lean_ctor_get(v_impl_508_, 3);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_impl_508_, 0);
lean_dec(v_unused_621_);
v___x_598_ = v_impl_508_;
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_r_594_);
lean_inc(v_v_596_);
lean_inc(v_k_595_);
lean_dec(v_impl_508_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_k_600_; lean_object* v_v_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_615_; 
v_k_600_ = lean_ctor_get(v_l_593_, 1);
v_v_601_ = lean_ctor_get(v_l_593_, 2);
v_isSharedCheck_615_ = !lean_is_exclusive(v_l_593_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; lean_object* v_unused_617_; lean_object* v_unused_618_; 
v_unused_616_ = lean_ctor_get(v_l_593_, 4);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_l_593_, 3);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_l_593_, 0);
lean_dec(v_unused_618_);
v___x_603_ = v_l_593_;
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_v_601_);
lean_inc(v_k_600_);
lean_dec(v_l_593_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_594_, 2);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 4, v_r_594_);
lean_ctor_set(v___x_603_, 3, v_r_594_);
lean_ctor_set(v___x_603_, 2, v_v_361_);
lean_ctor_set(v___x_603_, 1, v_k_360_);
lean_ctor_set(v___x_603_, 0, v___x_509_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_r_594_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_r_594_);
v___x_607_ = v_reuseFailAlloc_614_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
lean_inc(v_r_594_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 3, v_r_594_);
lean_ctor_set(v___x_598_, 0, v___x_509_);
v___x_609_ = v___x_598_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_596_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_r_594_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_r_594_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v___x_609_);
lean_ctor_set(v___x_365_, 3, v___x_607_);
lean_ctor_set(v___x_365_, 2, v_v_601_);
lean_ctor_set(v___x_365_, 1, v_k_600_);
lean_ctor_set(v___x_365_, 0, v___x_605_);
v___x_611_ = v___x_365_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_600_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_601_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
else
{
lean_object* v_r_622_; 
v_r_622_ = lean_ctor_get(v_impl_508_, 4);
lean_inc(v_r_622_);
if (lean_obj_tag(v_r_622_) == 0)
{
lean_object* v_k_623_; lean_object* v_v_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_635_; 
v_k_623_ = lean_ctor_get(v_impl_508_, 1);
v_v_624_ = lean_ctor_get(v_impl_508_, 2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_impl_508_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_636_ = lean_ctor_get(v_impl_508_, 4);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_impl_508_, 3);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_impl_508_, 0);
lean_dec(v_unused_638_);
v___x_626_ = v_impl_508_;
v_isShared_627_ = v_isSharedCheck_635_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_v_624_);
lean_inc(v_k_623_);
lean_dec(v_impl_508_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_635_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(3u);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v_l_593_);
lean_ctor_set(v___x_626_, 2, v_v_361_);
lean_ctor_set(v___x_626_, 1, v_k_360_);
lean_ctor_set(v___x_626_, 0, v___x_509_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_l_593_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_l_593_);
v___x_630_ = v_reuseFailAlloc_634_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_r_622_);
lean_ctor_set(v___x_365_, 3, v___x_630_);
lean_ctor_set(v___x_365_, 2, v_v_624_);
lean_ctor_set(v___x_365_, 1, v_k_623_);
lean_ctor_set(v___x_365_, 0, v___x_628_);
v___x_632_ = v___x_365_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_k_623_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_v_624_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_r_622_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_unsigned_to_nat(2u);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_impl_508_);
lean_ctor_set(v___x_365_, 3, v_r_622_);
lean_ctor_set(v___x_365_, 0, v___x_639_);
v___x_641_ = v___x_365_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_r_622_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v_impl_508_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
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
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_k_356_);
lean_ctor_set(v___x_645_, 2, v_v_357_);
lean_ctor_set(v___x_645_, 3, v_t_358_);
lean_ctor_set(v___x_645_, 4, v_t_358_);
return v___x_645_;
}
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = lean_box(1);
v___x_647_ = l_Lake_LeanExe_defaultFacetConfig;
v___x_648_ = l_Lake_LeanExe_defaultFacet;
v___x_649_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_648_, v___x_647_, v___x_646_);
return v___x_649_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__0, &l_Lake_LeanExe_initFacetConfigs___closed__0_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__0);
v___x_651_ = l_Lake_LeanExe_exeFacetConfig;
v___x_652_ = l_Lake_LeanExe_exeFacet;
v___x_653_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_652_, v___x_651_, v___x_650_);
return v___x_653_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__1, &l_Lake_LeanExe_initFacetConfigs___closed__1_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__1);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object* v_00_u03b2_655_, lean_object* v_k_656_, lean_object* v_v_657_, lean_object* v_t_658_, lean_object* v_hl_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_656_, v_v_657_, v_t_658_);
return v___x_660_;
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
