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
lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object*);
extern lean_object* l_Lake_Module_linkInfoNoExportFacet;
extern lean_object* l_Lake_Module_keyword;
extern lean_object* l_Lake_Module_linkInfoExportFacet;
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
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
size_t v___x_123_; size_t v___x_124_; uint64_t v___x_125_; 
v___x_123_ = ((size_t)0ULL);
v___x_124_ = lean_usize_of_nat(v___x_121_);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___x_78_, v___x_123_, v___x_124_, v___x_119_);
v___y_81_ = v___x_125_;
goto v___jp_80_;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(lean_object* v_self_126_, lean_object* v_pkg_127_, lean_object* v_exeName_128_, lean_object* v_supportInterpreter_129_, lean_object* v_info_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
uint8_t v_supportInterpreter_boxed_138_; lean_object* v_res_139_; 
v_supportInterpreter_boxed_138_ = lean_unbox(v_supportInterpreter_129_);
v_res_139_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(v_self_126_, v_pkg_127_, v_exeName_128_, v_supportInterpreter_boxed_138_, v_info_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v_self_126_);
return v_res_139_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__0));
v___x_142_ = l_Lake_BuildTrace_nil(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(lean_object* v___x_143_, lean_object* v___f_144_, lean_object* v_infoJob_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = 0;
v___x_155_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1);
v___x_156_ = l_Lake_Job_mapM___redArg(v___x_143_, v_infoJob_145_, v___f_144_, v___x_153_, v___x_154_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___y_151_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed(lean_object* v___x_158_, lean_object* v___f_159_, lean_object* v_infoJob_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(v___x_158_, v___f_159_, v_infoJob_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec(v___y_163_);
lean_dec(v___y_162_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(uint8_t v_supportInterpreter_169_, lean_object* v_pkg_170_, lean_object* v_config_171_, lean_object* v_name_172_, lean_object* v_root_173_, lean_object* v___x_174_, lean_object* v___f_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
if (v_supportInterpreter_169_ == 0)
{
lean_object* v_keyName_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_keyName_183_ = lean_ctor_get(v_pkg_170_, 2);
lean_inc(v_keyName_183_);
v___x_184_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_171_);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v_pkg_170_);
lean_ctor_set(v___x_185_, 1, v_name_172_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
lean_inc(v_root_173_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_root_173_);
v___x_187_ = l_Lake_Module_linkInfoNoExportFacet;
v___x_188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_188_, 0, v_keyName_183_);
lean_ctor_set(v___x_188_, 1, v_root_173_);
v___x_189_ = l_Lake_Module_keyword;
v___x_190_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
lean_ctor_set(v___x_190_, 2, v___x_186_);
lean_ctor_set(v___x_190_, 3, v___x_187_);
lean_inc_ref(v___y_176_);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc(v___y_178_);
lean_inc(v___x_174_);
v___x_191_ = lean_apply_7(v___y_176_, v___x_190_, v___x_174_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, lean_box(0));
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v_a_193_; lean_object* v___x_194_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
v_a_193_ = lean_ctor_get(v___x_191_, 1);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_191_, 2);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc(v___y_178_);
v___x_194_ = lean_apply_8(v___f_175_, v_a_192_, v___y_176_, v___x_174_, v___y_178_, v___y_179_, v___y_180_, v_a_193_, lean_box(0));
return v___x_194_;
}
else
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v___y_176_);
lean_dec_ref(v___f_175_);
lean_dec(v___x_174_);
v_a_195_ = lean_ctor_get(v___x_191_, 0);
v_a_196_ = lean_ctor_get(v___x_191_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_191_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_inc(v_a_195_);
lean_dec(v___x_191_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_195_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_keyName_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_keyName_204_ = lean_ctor_get(v_pkg_170_, 2);
lean_inc(v_keyName_204_);
v___x_205_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_171_);
v___x_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_206_, 0, v_pkg_170_);
lean_ctor_set(v___x_206_, 1, v_name_172_);
lean_ctor_set(v___x_206_, 2, v___x_205_);
lean_inc(v_root_173_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_root_173_);
v___x_208_ = l_Lake_Module_linkInfoExportFacet;
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v_keyName_204_);
lean_ctor_set(v___x_209_, 1, v_root_173_);
v___x_210_ = l_Lake_Module_keyword;
v___x_211_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_ctor_set(v___x_211_, 2, v___x_207_);
lean_ctor_set(v___x_211_, 3, v___x_208_);
lean_inc_ref(v___y_176_);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc(v___y_178_);
lean_inc(v___x_174_);
v___x_212_ = lean_apply_7(v___y_176_, v___x_211_, v___x_174_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
v_a_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_212_, 2);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc(v___y_178_);
v___x_215_ = lean_apply_8(v___f_175_, v_a_213_, v___y_176_, v___x_174_, v___y_178_, v___y_179_, v___y_180_, v_a_214_, lean_box(0));
return v___x_215_;
}
else
{
lean_object* v_a_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v___y_176_);
lean_dec_ref(v___f_175_);
lean_dec(v___x_174_);
v_a_216_ = lean_ctor_get(v___x_212_, 0);
v_a_217_ = lean_ctor_get(v___x_212_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_212_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_inc(v_a_216_);
lean_dec(v___x_212_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_216_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed(lean_object* v_supportInterpreter_225_, lean_object* v_pkg_226_, lean_object* v_config_227_, lean_object* v_name_228_, lean_object* v_root_229_, lean_object* v___x_230_, lean_object* v___f_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
uint8_t v_supportInterpreter_boxed_239_; lean_object* v_res_240_; 
v_supportInterpreter_boxed_239_ = lean_unbox(v_supportInterpreter_225_);
v_res_240_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(v_supportInterpreter_boxed_239_, v_pkg_226_, v_config_227_, v_name_228_, v_root_229_, v___x_230_, v___f_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec(v___y_234_);
lean_dec(v___y_233_);
lean_dec(v_config_227_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object* v_self_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_config_250_; lean_object* v_pkg_251_; lean_object* v_name_252_; lean_object* v_root_253_; lean_object* v_exeName_254_; uint8_t v_supportInterpreter_255_; lean_object* v___x_256_; lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v_config_250_ = lean_ctor_get(v_self_242_, 2);
lean_inc(v_config_250_);
v_pkg_251_ = lean_ctor_get(v_self_242_, 0);
lean_inc_ref_n(v_pkg_251_, 3);
v_name_252_ = lean_ctor_get(v_self_242_, 1);
lean_inc_n(v_name_252_, 2);
v_root_253_ = lean_ctor_get(v_config_250_, 2);
lean_inc(v_root_253_);
v_exeName_254_ = lean_ctor_get(v_config_250_, 3);
v_supportInterpreter_255_ = lean_ctor_get_uint8(v_config_250_, sizeof(void*)*7);
v___x_256_ = lean_box(v_supportInterpreter_255_);
lean_inc_ref(v_exeName_254_);
v___f_257_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed), 12, 4);
lean_closure_set(v___f_257_, 0, v_self_242_);
lean_closure_set(v___f_257_, 1, v_pkg_251_);
lean_closure_set(v___f_257_, 2, v_exeName_254_);
lean_closure_set(v___f_257_, 3, v___x_256_);
v___x_258_ = l_Lake_instDataKindFilePath;
v___f_259_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed), 10, 2);
lean_closure_set(v___f_259_, 0, v___x_258_);
lean_closure_set(v___f_259_, 1, v___f_257_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_pkg_251_);
v___x_261_ = lean_box(v_supportInterpreter_255_);
v___f_262_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed), 14, 7);
lean_closure_set(v___f_262_, 0, v___x_261_);
lean_closure_set(v___f_262_, 1, v_pkg_251_);
lean_closure_set(v___f_262_, 2, v_config_250_);
lean_closure_set(v___f_262_, 3, v_name_252_);
lean_closure_set(v___f_262_, 4, v_root_253_);
lean_closure_set(v___f_262_, 5, v___x_260_);
lean_closure_set(v___f_262_, 6, v___f_259_);
v___x_263_ = l_Lake_ensureJob___redArg(v___x_258_, v___f_262_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_293_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_a_265_ = lean_ctor_get(v___x_263_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_293_ == 0)
{
v___x_267_ = v___x_263_;
v_isShared_268_ = v_isSharedCheck_293_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_293_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_task_269_; lean_object* v_kind_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_291_; 
v_task_269_ = lean_ctor_get(v_a_264_, 0);
v_kind_270_ = lean_ctor_get(v_a_264_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_a_264_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v_a_264_, 2);
lean_dec(v_unused_292_);
v___x_272_ = v_a_264_;
v_isShared_273_ = v_isSharedCheck_291_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_kind_270_);
lean_inc(v_task_269_);
lean_dec(v_a_264_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_291_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_registeredJobs_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v_job_282_; 
v_registeredJobs_274_ = lean_ctor_get(v_a_247_, 4);
v___x_275_ = lean_st_ref_take(v_registeredJobs_274_);
v___x_276_ = 1;
v___x_277_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_252_, v___x_276_);
v___x_278_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0));
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
v___x_280_ = 0;
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 2, v___x_279_);
v_job_282_ = v___x_272_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_task_269_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_kind_270_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_279_);
v_job_282_ = v_reuseFailAlloc_290_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
lean_ctor_set_uint8(v_job_282_, sizeof(void*)*3, v___x_280_);
lean_inc_ref(v_job_282_);
v___x_283_ = l_Lake_Job_toOpaque___redArg(v_job_282_);
v___x_284_ = lean_array_push(v___x_275_, v___x_283_);
v___x_285_ = lean_st_ref_put(v_registeredJobs_274_, v___x_284_);
v___x_286_ = l_Lake_Job_renew___redArg(v_job_282_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_286_);
v___x_288_ = v___x_267_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_a_265_);
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
}
else
{
lean_dec(v_name_252_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object* v_self_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(v_self_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec(v_a_297_);
lean_dec(v_a_296_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t v_fmt_303_, lean_object* v_a_304_){
_start:
{
if (v_fmt_303_ == 0)
{
return v_a_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = l_Lake_mkRelPathString(v_a_304_);
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = l_Lean_Json_compress(v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object* v_fmt_308_, lean_object* v_a_309_){
_start:
{
uint8_t v_fmt_boxed_310_; lean_object* v_res_311_; 
v_fmt_boxed_310_ = lean_unbox(v_fmt_308_);
v_res_311_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(v_fmt_boxed_310_, v_a_309_);
return v_res_311_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___f_314_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_315_ = 1;
v___x_316_ = l_Lake_instDataKindFilePath;
v___x_317_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__1));
v___x_318_ = l_Lake_LeanExe_keyword;
v___x_319_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_316_);
lean_ctor_set(v___x_319_, 3, v___f_314_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*4, v___x_315_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*4 + 1, v___x_315_);
return v___x_319_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Lake_LeanExe_exeFacetConfig___closed__2, &l_Lake_LeanExe_exeFacetConfig___closed__2_once, _init_l_Lake_LeanExe_exeFacetConfig___closed__2);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object* v_lib_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_pkg_329_; lean_object* v_name_330_; lean_object* v_keyName_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_pkg_329_ = lean_ctor_get(v_lib_321_, 0);
v_name_330_ = lean_ctor_get(v_lib_321_, 1);
v_keyName_331_ = lean_ctor_get(v_pkg_329_, 2);
v___x_332_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_330_);
lean_inc(v_keyName_331_);
v___x_333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_333_, 0, v_keyName_331_);
lean_ctor_set(v___x_333_, 1, v_name_330_);
v___x_334_ = l_Lake_LeanExe_keyword;
v___x_335_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_ctor_set(v___x_335_, 2, v_lib_321_);
lean_ctor_set(v___x_335_, 3, v___x_332_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
lean_inc(v_a_323_);
v___x_336_ = lean_apply_7(v_a_322_, v___x_335_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, lean_box(0));
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object* v_lib_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(v_lib_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec(v_a_340_);
lean_dec(v_a_339_);
return v_res_345_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_347_; lean_object* v___f_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_347_ = 0;
v___f_348_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_349_ = 1;
v___x_350_ = l_Lake_instDataKindFilePath;
v___x_351_ = ((lean_object*)(l_Lake_LeanExe_defaultFacetConfig___closed__0));
v___x_352_ = l_Lake_LeanExe_keyword;
v___x_353_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
lean_ctor_set(v___x_353_, 3, v___f_348_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*4, v___x_349_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*4 + 1, v___x_347_);
return v___x_353_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Lake_LeanExe_defaultFacetConfig___closed__1, &l_Lake_LeanExe_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanExe_defaultFacetConfig___closed__1);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object* v_k_355_, lean_object* v_v_356_, lean_object* v_t_357_){
_start:
{
if (lean_obj_tag(v_t_357_) == 0)
{
lean_object* v_size_358_; lean_object* v_k_359_; lean_object* v_v_360_; lean_object* v_l_361_; lean_object* v_r_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_642_; 
v_size_358_ = lean_ctor_get(v_t_357_, 0);
v_k_359_ = lean_ctor_get(v_t_357_, 1);
v_v_360_ = lean_ctor_get(v_t_357_, 2);
v_l_361_ = lean_ctor_get(v_t_357_, 3);
v_r_362_ = lean_ctor_get(v_t_357_, 4);
v_isSharedCheck_642_ = !lean_is_exclusive(v_t_357_);
if (v_isSharedCheck_642_ == 0)
{
v___x_364_ = v_t_357_;
v_isShared_365_ = v_isSharedCheck_642_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_r_362_);
lean_inc(v_l_361_);
lean_inc(v_v_360_);
lean_inc(v_k_359_);
lean_inc(v_size_358_);
lean_dec(v_t_357_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_642_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___x_366_; 
v___x_366_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_355_, v_k_359_);
switch(v___x_366_)
{
case 0:
{
lean_object* v_impl_367_; lean_object* v___x_368_; 
lean_dec(v_size_358_);
v_impl_367_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_355_, v_v_356_, v_l_361_);
v___x_368_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_362_) == 0)
{
lean_object* v_size_369_; lean_object* v_size_370_; lean_object* v_k_371_; lean_object* v_v_372_; lean_object* v_l_373_; lean_object* v_r_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_size_369_ = lean_ctor_get(v_r_362_, 0);
v_size_370_ = lean_ctor_get(v_impl_367_, 0);
lean_inc(v_size_370_);
v_k_371_ = lean_ctor_get(v_impl_367_, 1);
lean_inc(v_k_371_);
v_v_372_ = lean_ctor_get(v_impl_367_, 2);
lean_inc(v_v_372_);
v_l_373_ = lean_ctor_get(v_impl_367_, 3);
lean_inc(v_l_373_);
v_r_374_ = lean_ctor_get(v_impl_367_, 4);
lean_inc(v_r_374_);
v___x_375_ = lean_unsigned_to_nat(3u);
v___x_376_ = lean_nat_mul(v___x_375_, v_size_369_);
v___x_377_ = lean_nat_dec_lt(v___x_376_, v_size_370_);
lean_dec(v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec(v_r_374_);
lean_dec(v_l_373_);
lean_dec(v_v_372_);
lean_dec(v_k_371_);
v___x_378_ = lean_nat_add(v___x_368_, v_size_370_);
lean_dec(v_size_370_);
v___x_379_ = lean_nat_add(v___x_378_, v_size_369_);
lean_dec(v___x_378_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 3, v_impl_367_);
lean_ctor_set(v___x_364_, 0, v___x_379_);
v___x_381_ = v___x_364_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_impl_367_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v_r_362_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_448_; 
v_isSharedCheck_448_ = !lean_is_exclusive(v_impl_367_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; 
v_unused_449_ = lean_ctor_get(v_impl_367_, 4);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_impl_367_, 3);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_impl_367_, 2);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_impl_367_, 1);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_impl_367_, 0);
lean_dec(v_unused_453_);
v___x_384_ = v_impl_367_;
v_isShared_385_ = v_isSharedCheck_448_;
goto v_resetjp_383_;
}
else
{
lean_dec(v_impl_367_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_448_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_size_386_; lean_object* v_size_387_; lean_object* v_k_388_; lean_object* v_v_389_; lean_object* v_l_390_; lean_object* v_r_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_size_386_ = lean_ctor_get(v_l_373_, 0);
v_size_387_ = lean_ctor_get(v_r_374_, 0);
v_k_388_ = lean_ctor_get(v_r_374_, 1);
v_v_389_ = lean_ctor_get(v_r_374_, 2);
v_l_390_ = lean_ctor_get(v_r_374_, 3);
v_r_391_ = lean_ctor_get(v_r_374_, 4);
v___x_392_ = lean_unsigned_to_nat(2u);
v___x_393_ = lean_nat_mul(v___x_392_, v_size_386_);
v___x_394_ = lean_nat_dec_lt(v_size_387_, v___x_393_);
lean_dec(v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_423_; 
lean_inc(v_r_391_);
lean_inc(v_l_390_);
lean_inc(v_v_389_);
lean_inc(v_k_388_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_r_374_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; lean_object* v_unused_426_; lean_object* v_unused_427_; lean_object* v_unused_428_; 
v_unused_424_ = lean_ctor_get(v_r_374_, 4);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_r_374_, 3);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_r_374_, 2);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_r_374_, 1);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_r_374_, 0);
lean_dec(v_unused_428_);
v___x_396_ = v_r_374_;
v_isShared_397_ = v_isSharedCheck_423_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_r_374_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_423_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___x_411_; lean_object* v___y_413_; 
v___x_398_ = lean_nat_add(v___x_368_, v_size_370_);
lean_dec(v_size_370_);
v___x_399_ = lean_nat_add(v___x_398_, v_size_369_);
lean_dec(v___x_398_);
v___x_411_ = lean_nat_add(v___x_368_, v_size_386_);
if (lean_obj_tag(v_l_390_) == 0)
{
lean_object* v_size_421_; 
v_size_421_ = lean_ctor_get(v_l_390_, 0);
lean_inc(v_size_421_);
v___y_413_ = v_size_421_;
goto v___jp_412_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___y_413_ = v___x_422_;
goto v___jp_412_;
}
v___jp_400_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_nat_add(v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec(v___y_402_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 4, v_r_362_);
lean_ctor_set(v___x_396_, 3, v_r_391_);
lean_ctor_set(v___x_396_, 2, v_v_360_);
lean_ctor_set(v___x_396_, 1, v_k_359_);
lean_ctor_set(v___x_396_, 0, v___x_404_);
v___x_406_ = v___x_396_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_r_391_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_r_362_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v___x_406_);
lean_ctor_set(v___x_384_, 3, v___y_401_);
lean_ctor_set(v___x_384_, 2, v_v_389_);
lean_ctor_set(v___x_384_, 1, v_k_388_);
lean_ctor_set(v___x_384_, 0, v___x_399_);
v___x_408_ = v___x_384_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_388_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_389_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v___y_401_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_nat_add(v___x_411_, v___y_413_);
lean_dec(v___y_413_);
lean_dec(v___x_411_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_l_390_);
lean_ctor_set(v___x_364_, 3, v_l_373_);
lean_ctor_set(v___x_364_, 2, v_v_372_);
lean_ctor_set(v___x_364_, 1, v_k_371_);
lean_ctor_set(v___x_364_, 0, v___x_414_);
v___x_416_ = v___x_364_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_k_371_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_v_372_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_l_373_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_l_390_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; 
v___x_417_ = lean_nat_add(v___x_368_, v_size_369_);
if (lean_obj_tag(v_r_391_) == 0)
{
lean_object* v_size_418_; 
v_size_418_ = lean_ctor_get(v_r_391_, 0);
lean_inc(v_size_418_);
v___y_401_ = v___x_416_;
v___y_402_ = v___x_417_;
v___y_403_ = v_size_418_;
goto v___jp_400_;
}
else
{
lean_object* v___x_419_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___y_401_ = v___x_416_;
v___y_402_ = v___x_417_;
v___y_403_ = v___x_419_;
goto v___jp_400_;
}
}
}
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
lean_del_object(v___x_364_);
v___x_429_ = lean_nat_add(v___x_368_, v_size_370_);
lean_dec(v_size_370_);
v___x_430_ = lean_nat_add(v___x_429_, v_size_369_);
lean_dec(v___x_429_);
v___x_431_ = lean_nat_add(v___x_368_, v_size_369_);
v___x_432_ = lean_nat_add(v___x_431_, v_size_387_);
lean_dec(v___x_431_);
lean_inc_ref(v_r_362_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v_r_362_);
lean_ctor_set(v___x_384_, 3, v_r_374_);
lean_ctor_set(v___x_384_, 2, v_v_360_);
lean_ctor_set(v___x_384_, 1, v_k_359_);
lean_ctor_set(v___x_384_, 0, v___x_432_);
v___x_434_ = v___x_384_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_r_374_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_r_362_);
v___x_434_ = v_reuseFailAlloc_447_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_isSharedCheck_441_ = !lean_is_exclusive(v_r_362_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_442_ = lean_ctor_get(v_r_362_, 4);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_r_362_, 3);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_r_362_, 2);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_r_362_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_r_362_, 0);
lean_dec(v_unused_446_);
v___x_436_ = v_r_362_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_dec(v_r_362_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 4, v___x_434_);
lean_ctor_set(v___x_436_, 3, v_l_373_);
lean_ctor_set(v___x_436_, 2, v_v_372_);
lean_ctor_set(v___x_436_, 1, v_k_371_);
lean_ctor_set(v___x_436_, 0, v___x_430_);
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_k_371_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_v_372_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_l_373_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v___x_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_454_; 
v_l_454_ = lean_ctor_get(v_impl_367_, 3);
lean_inc(v_l_454_);
if (lean_obj_tag(v_l_454_) == 0)
{
lean_object* v_r_455_; lean_object* v_k_456_; lean_object* v_v_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_468_; 
v_r_455_ = lean_ctor_get(v_impl_367_, 4);
v_k_456_ = lean_ctor_get(v_impl_367_, 1);
v_v_457_ = lean_ctor_get(v_impl_367_, 2);
v_isSharedCheck_468_ = !lean_is_exclusive(v_impl_367_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; 
v_unused_469_ = lean_ctor_get(v_impl_367_, 3);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_impl_367_, 0);
lean_dec(v_unused_470_);
v___x_459_ = v_impl_367_;
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_r_455_);
lean_inc(v_v_457_);
lean_inc(v_k_456_);
lean_dec(v_impl_367_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_455_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 3, v_r_455_);
lean_ctor_set(v___x_459_, 2, v_v_360_);
lean_ctor_set(v___x_459_, 1, v_k_359_);
lean_ctor_set(v___x_459_, 0, v___x_368_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_r_455_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v_r_455_);
v___x_463_ = v_reuseFailAlloc_467_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v___x_463_);
lean_ctor_set(v___x_364_, 3, v_l_454_);
lean_ctor_set(v___x_364_, 2, v_v_457_);
lean_ctor_set(v___x_364_, 1, v_k_456_);
lean_ctor_set(v___x_364_, 0, v___x_461_);
v___x_465_ = v___x_364_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_k_456_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_v_457_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_l_454_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_r_471_; 
v_r_471_ = lean_ctor_get(v_impl_367_, 4);
lean_inc(v_r_471_);
if (lean_obj_tag(v_r_471_) == 0)
{
lean_object* v_k_472_; lean_object* v_v_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_496_; 
v_k_472_ = lean_ctor_get(v_impl_367_, 1);
v_v_473_ = lean_ctor_get(v_impl_367_, 2);
v_isSharedCheck_496_ = !lean_is_exclusive(v_impl_367_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_497_ = lean_ctor_get(v_impl_367_, 4);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_impl_367_, 3);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_impl_367_, 0);
lean_dec(v_unused_499_);
v___x_475_ = v_impl_367_;
v_isShared_476_ = v_isSharedCheck_496_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_v_473_);
lean_inc(v_k_472_);
lean_dec(v_impl_367_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_496_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
v_k_477_ = lean_ctor_get(v_r_471_, 1);
v_v_478_ = lean_ctor_get(v_r_471_, 2);
v_isSharedCheck_492_ = !lean_is_exclusive(v_r_471_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_493_ = lean_ctor_get(v_r_471_, 4);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_r_471_, 3);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_r_471_, 0);
lean_dec(v_unused_495_);
v___x_480_ = v_r_471_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_v_478_);
lean_inc(v_k_477_);
lean_dec(v_r_471_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(3u);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v_l_454_);
lean_ctor_set(v___x_480_, 3, v_l_454_);
lean_ctor_set(v___x_480_, 2, v_v_473_);
lean_ctor_set(v___x_480_, 1, v_k_472_);
lean_ctor_set(v___x_480_, 0, v___x_368_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_472_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_473_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_l_454_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_l_454_);
v___x_484_ = v_reuseFailAlloc_491_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_l_454_);
lean_ctor_set(v___x_475_, 2, v_v_360_);
lean_ctor_set(v___x_475_, 1, v_k_359_);
lean_ctor_set(v___x_475_, 0, v___x_368_);
v___x_486_ = v___x_475_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_l_454_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v_l_454_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v___x_486_);
lean_ctor_set(v___x_364_, 3, v___x_484_);
lean_ctor_set(v___x_364_, 2, v_v_478_);
lean_ctor_set(v___x_364_, 1, v_k_477_);
lean_ctor_set(v___x_364_, 0, v___x_482_);
v___x_488_ = v___x_364_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(2u);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_r_471_);
lean_ctor_set(v___x_364_, 3, v_impl_367_);
lean_ctor_set(v___x_364_, 0, v___x_500_);
v___x_502_ = v___x_364_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_impl_367_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v_r_471_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
case 1:
{
lean_object* v___x_505_; 
lean_dec(v_v_360_);
lean_dec(v_k_359_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 2, v_v_356_);
lean_ctor_set(v___x_364_, 1, v_k_355_);
v___x_505_ = v___x_364_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_size_358_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_k_355_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_v_356_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_l_361_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_r_362_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
default: 
{
lean_object* v_impl_507_; lean_object* v___x_508_; 
lean_dec(v_size_358_);
v_impl_507_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_355_, v_v_356_, v_r_362_);
v___x_508_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_361_) == 0)
{
lean_object* v_size_509_; lean_object* v_size_510_; lean_object* v_k_511_; lean_object* v_v_512_; lean_object* v_l_513_; lean_object* v_r_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_size_509_ = lean_ctor_get(v_l_361_, 0);
v_size_510_ = lean_ctor_get(v_impl_507_, 0);
lean_inc(v_size_510_);
v_k_511_ = lean_ctor_get(v_impl_507_, 1);
lean_inc(v_k_511_);
v_v_512_ = lean_ctor_get(v_impl_507_, 2);
lean_inc(v_v_512_);
v_l_513_ = lean_ctor_get(v_impl_507_, 3);
lean_inc(v_l_513_);
v_r_514_ = lean_ctor_get(v_impl_507_, 4);
lean_inc(v_r_514_);
v___x_515_ = lean_unsigned_to_nat(3u);
v___x_516_ = lean_nat_mul(v___x_515_, v_size_509_);
v___x_517_ = lean_nat_dec_lt(v___x_516_, v_size_510_);
lean_dec(v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec(v_r_514_);
lean_dec(v_l_513_);
lean_dec(v_v_512_);
lean_dec(v_k_511_);
v___x_518_ = lean_nat_add(v___x_508_, v_size_509_);
v___x_519_ = lean_nat_add(v___x_518_, v_size_510_);
lean_dec(v_size_510_);
lean_dec(v___x_518_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_impl_507_);
lean_ctor_set(v___x_364_, 0, v___x_519_);
v___x_521_ = v___x_364_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_l_361_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_impl_507_);
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
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_586_; 
v_isSharedCheck_586_ = !lean_is_exclusive(v_impl_507_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_587_ = lean_ctor_get(v_impl_507_, 4);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_impl_507_, 3);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_impl_507_, 2);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_impl_507_, 1);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_impl_507_, 0);
lean_dec(v_unused_591_);
v___x_524_ = v_impl_507_;
v_isShared_525_ = v_isSharedCheck_586_;
goto v_resetjp_523_;
}
else
{
lean_dec(v_impl_507_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_586_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_size_526_; lean_object* v_k_527_; lean_object* v_v_528_; lean_object* v_l_529_; lean_object* v_r_530_; lean_object* v_size_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_size_526_ = lean_ctor_get(v_l_513_, 0);
v_k_527_ = lean_ctor_get(v_l_513_, 1);
v_v_528_ = lean_ctor_get(v_l_513_, 2);
v_l_529_ = lean_ctor_get(v_l_513_, 3);
v_r_530_ = lean_ctor_get(v_l_513_, 4);
v_size_531_ = lean_ctor_get(v_r_514_, 0);
v___x_532_ = lean_unsigned_to_nat(2u);
v___x_533_ = lean_nat_mul(v___x_532_, v_size_531_);
v___x_534_ = lean_nat_dec_lt(v_size_526_, v___x_533_);
lean_dec(v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_562_; 
lean_inc(v_r_530_);
lean_inc(v_l_529_);
lean_inc(v_v_528_);
lean_inc(v_k_527_);
v_isSharedCheck_562_ = !lean_is_exclusive(v_l_513_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_563_ = lean_ctor_get(v_l_513_, 4);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_l_513_, 3);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_l_513_, 2);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_513_, 1);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_513_, 0);
lean_dec(v_unused_567_);
v___x_536_ = v_l_513_;
v_isShared_537_ = v_isSharedCheck_562_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_l_513_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_562_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_552_; 
v___x_538_ = lean_nat_add(v___x_508_, v_size_509_);
v___x_539_ = lean_nat_add(v___x_538_, v_size_510_);
lean_dec(v_size_510_);
if (lean_obj_tag(v_l_529_) == 0)
{
lean_object* v_size_560_; 
v_size_560_ = lean_ctor_get(v_l_529_, 0);
lean_inc(v_size_560_);
v___y_552_ = v_size_560_;
goto v___jp_551_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___y_552_ = v___x_561_;
goto v___jp_551_;
}
v___jp_540_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_nat_add(v___y_541_, v___y_543_);
lean_dec(v___y_543_);
lean_dec(v___y_541_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v_r_514_);
lean_ctor_set(v___x_536_, 3, v_r_530_);
lean_ctor_set(v___x_536_, 2, v_v_512_);
lean_ctor_set(v___x_536_, 1, v_k_511_);
lean_ctor_set(v___x_536_, 0, v___x_544_);
v___x_546_ = v___x_536_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_k_511_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_v_512_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_r_530_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_r_514_);
v___x_546_ = v_reuseFailAlloc_550_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_548_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v___x_546_);
lean_ctor_set(v___x_524_, 3, v___y_542_);
lean_ctor_set(v___x_524_, 2, v_v_528_);
lean_ctor_set(v___x_524_, 1, v_k_527_);
lean_ctor_set(v___x_524_, 0, v___x_539_);
v___x_548_ = v___x_524_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_k_527_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_v_528_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v___y_542_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_nat_add(v___x_538_, v___y_552_);
lean_dec(v___y_552_);
lean_dec(v___x_538_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_l_529_);
lean_ctor_set(v___x_364_, 0, v___x_553_);
v___x_555_ = v___x_364_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_l_361_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_l_529_);
v___x_555_ = v_reuseFailAlloc_559_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = lean_nat_add(v___x_508_, v_size_531_);
if (lean_obj_tag(v_r_530_) == 0)
{
lean_object* v_size_557_; 
v_size_557_ = lean_ctor_get(v_r_530_, 0);
lean_inc(v_size_557_);
v___y_541_ = v___x_556_;
v___y_542_ = v___x_555_;
v___y_543_ = v_size_557_;
goto v___jp_540_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___y_541_ = v___x_556_;
v___y_542_ = v___x_555_;
v___y_543_ = v___x_558_;
goto v___jp_540_;
}
}
}
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_del_object(v___x_364_);
v___x_568_ = lean_nat_add(v___x_508_, v_size_509_);
v___x_569_ = lean_nat_add(v___x_568_, v_size_510_);
lean_dec(v_size_510_);
v___x_570_ = lean_nat_add(v___x_568_, v_size_526_);
lean_dec(v___x_568_);
lean_inc_ref(v_l_361_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v_l_513_);
lean_ctor_set(v___x_524_, 3, v_l_361_);
lean_ctor_set(v___x_524_, 2, v_v_360_);
lean_ctor_set(v___x_524_, 1, v_k_359_);
lean_ctor_set(v___x_524_, 0, v___x_570_);
v___x_572_ = v___x_524_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_l_361_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_l_513_);
v___x_572_ = v_reuseFailAlloc_585_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_isSharedCheck_579_ = !lean_is_exclusive(v_l_361_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; 
v_unused_580_ = lean_ctor_get(v_l_361_, 4);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_l_361_, 3);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_l_361_, 2);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_l_361_, 1);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_l_361_, 0);
lean_dec(v_unused_584_);
v___x_574_ = v_l_361_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_dec(v_l_361_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 4, v_r_514_);
lean_ctor_set(v___x_574_, 3, v___x_572_);
lean_ctor_set(v___x_574_, 2, v_v_512_);
lean_ctor_set(v___x_574_, 1, v_k_511_);
lean_ctor_set(v___x_574_, 0, v___x_569_);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_k_511_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_v_512_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_r_514_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_592_; 
v_l_592_ = lean_ctor_get(v_impl_507_, 3);
lean_inc(v_l_592_);
if (lean_obj_tag(v_l_592_) == 0)
{
lean_object* v_r_593_; lean_object* v_k_594_; lean_object* v_v_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_618_; 
v_r_593_ = lean_ctor_get(v_impl_507_, 4);
v_k_594_ = lean_ctor_get(v_impl_507_, 1);
v_v_595_ = lean_ctor_get(v_impl_507_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_impl_507_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_619_ = lean_ctor_get(v_impl_507_, 3);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_impl_507_, 0);
lean_dec(v_unused_620_);
v___x_597_ = v_impl_507_;
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_r_593_);
lean_inc(v_v_595_);
lean_inc(v_k_594_);
lean_dec(v_impl_507_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_k_599_; lean_object* v_v_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_614_; 
v_k_599_ = lean_ctor_get(v_l_592_, 1);
v_v_600_ = lean_ctor_get(v_l_592_, 2);
v_isSharedCheck_614_ = !lean_is_exclusive(v_l_592_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; lean_object* v_unused_616_; lean_object* v_unused_617_; 
v_unused_615_ = lean_ctor_get(v_l_592_, 4);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_l_592_, 3);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_l_592_, 0);
lean_dec(v_unused_617_);
v___x_602_ = v_l_592_;
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_v_600_);
lean_inc(v_k_599_);
lean_dec(v_l_592_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_593_, 2);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 4, v_r_593_);
lean_ctor_set(v___x_602_, 3, v_r_593_);
lean_ctor_set(v___x_602_, 2, v_v_360_);
lean_ctor_set(v___x_602_, 1, v_k_359_);
lean_ctor_set(v___x_602_, 0, v___x_508_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_r_593_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_r_593_);
v___x_606_ = v_reuseFailAlloc_613_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
lean_inc(v_r_593_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 3, v_r_593_);
lean_ctor_set(v___x_597_, 0, v___x_508_);
v___x_608_ = v___x_597_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_594_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_595_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_r_593_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_r_593_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v___x_608_);
lean_ctor_set(v___x_364_, 3, v___x_606_);
lean_ctor_set(v___x_364_, 2, v_v_600_);
lean_ctor_set(v___x_364_, 1, v_k_599_);
lean_ctor_set(v___x_364_, 0, v___x_604_);
v___x_610_ = v___x_364_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_599_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_600_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
else
{
lean_object* v_r_621_; 
v_r_621_ = lean_ctor_get(v_impl_507_, 4);
lean_inc(v_r_621_);
if (lean_obj_tag(v_r_621_) == 0)
{
lean_object* v_k_622_; lean_object* v_v_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_634_; 
v_k_622_ = lean_ctor_get(v_impl_507_, 1);
v_v_623_ = lean_ctor_get(v_impl_507_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_impl_507_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; 
v_unused_635_ = lean_ctor_get(v_impl_507_, 4);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_impl_507_, 3);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_impl_507_, 0);
lean_dec(v_unused_637_);
v___x_625_ = v_impl_507_;
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_v_623_);
lean_inc(v_k_622_);
lean_dec(v_impl_507_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(3u);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_l_592_);
lean_ctor_set(v___x_625_, 2, v_v_360_);
lean_ctor_set(v___x_625_, 1, v_k_359_);
lean_ctor_set(v___x_625_, 0, v___x_508_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_l_592_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_l_592_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_r_621_);
lean_ctor_set(v___x_364_, 3, v___x_629_);
lean_ctor_set(v___x_364_, 2, v_v_623_);
lean_ctor_set(v___x_364_, 1, v_k_622_);
lean_ctor_set(v___x_364_, 0, v___x_627_);
v___x_631_ = v___x_364_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_622_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_v_623_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_r_621_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(2u);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_impl_507_);
lean_ctor_set(v___x_364_, 3, v_r_621_);
lean_ctor_set(v___x_364_, 0, v___x_638_);
v___x_640_ = v___x_364_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_r_621_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v_impl_507_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
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
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_k_355_);
lean_ctor_set(v___x_644_, 2, v_v_356_);
lean_ctor_set(v___x_644_, 3, v_t_357_);
lean_ctor_set(v___x_644_, 4, v_t_357_);
return v___x_644_;
}
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_645_ = lean_box(1);
v___x_646_ = l_Lake_LeanExe_defaultFacetConfig;
v___x_647_ = l_Lake_LeanExe_defaultFacet;
v___x_648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_647_, v___x_646_, v___x_645_);
return v___x_648_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__0, &l_Lake_LeanExe_initFacetConfigs___closed__0_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__0);
v___x_650_ = l_Lake_LeanExe_exeFacetConfig;
v___x_651_ = l_Lake_LeanExe_exeFacet;
v___x_652_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_651_, v___x_650_, v___x_649_);
return v___x_652_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs(void){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__1, &l_Lake_LeanExe_initFacetConfigs___closed__1_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__1);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object* v_00_u03b2_654_, lean_object* v_k_655_, lean_object* v_v_656_, lean_object* v_t_657_, lean_object* v_hl_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_655_, v_v_656_, v_t_657_);
return v___x_659_;
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
