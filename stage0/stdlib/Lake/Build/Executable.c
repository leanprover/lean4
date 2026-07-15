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
lean_object* l_Lake_buildLeanExeSync(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_args_75_; lean_object* v_objs_76_; lean_object* v_libs_77_; lean_object* v___x_78_; lean_object* v_args_79_; uint64_t v___y_81_; uint64_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
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
v___x_118_ = l_Lake_Hash_nil;
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_array_get_size(v___x_78_);
v___x_121_ = lean_nat_dec_lt(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
v___y_81_ = v___x_118_;
goto v___jp_80_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_le(v___x_120_, v___x_120_);
if (v___x_122_ == 0)
{
if (v___x_121_ == 0)
{
v___y_81_ = v___x_118_;
goto v___jp_80_;
}
else
{
size_t v___x_123_; size_t v___x_124_; uint64_t v___x_125_; 
v___x_123_ = ((size_t)0ULL);
v___x_124_ = lean_usize_of_nat(v___x_120_);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___x_78_, v___x_123_, v___x_124_, v___x_118_);
v___y_81_ = v___x_125_;
goto v___jp_80_;
}
}
else
{
size_t v___x_126_; size_t v___x_127_; uint64_t v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_120_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___x_78_, v___x_126_, v___x_127_, v___x_118_);
v___y_81_ = v___x_128_;
goto v___jp_80_;
}
}
v___jp_80_:
{
lean_object* v_config_82_; lean_object* v_log_83_; uint8_t v_action_84_; uint8_t v_wantsRebuild_85_; lean_object* v_trace_86_; lean_object* v_buildTime_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_117_; 
v_config_82_ = lean_ctor_get(v_pkg_64_, 6);
lean_inc_ref(v_config_82_);
v_log_83_ = lean_ctor_get(v___y_73_, 0);
v_action_84_ = lean_ctor_get_uint8(v___y_73_, sizeof(void*)*3);
v_wantsRebuild_85_ = lean_ctor_get_uint8(v___y_73_, sizeof(void*)*3 + 1);
v_trace_86_ = lean_ctor_get(v___y_73_, 1);
v_buildTime_87_ = lean_ctor_get(v___y_73_, 2);
v_isSharedCheck_117_ = !lean_is_exclusive(v___y_73_);
if (v_isSharedCheck_117_ == 0)
{
v___x_89_ = v___y_73_;
v_isShared_90_ = v_isSharedCheck_117_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_buildTime_87_);
lean_inc(v_trace_86_);
lean_inc(v_log_83_);
lean_dec(v___y_73_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_117_;
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
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_log_83_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_buildTime_87_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*3, v_action_84_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*3 + 1, v_wantsRebuild_85_);
v___x_105_ = v_reuseFailAlloc_116_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; 
v___x_106_ = l_System_FilePath_normalize(v_buildDir_92_);
v___x_107_ = l_Lake_joinRelative(v_dir_91_, v___x_106_);
v___x_108_ = l_System_FilePath_normalize(v_binDir_93_);
v___x_109_ = l_Lake_joinRelative(v___x_107_, v___x_108_);
v___x_110_ = l_System_FilePath_exeExtension;
v___x_111_ = l_System_FilePath_addExtension(v_exeName_65_, v___x_110_);
v___x_112_ = l_Lake_joinRelative(v___x_109_, v___x_111_);
v___x_113_ = l_System_Platform_isWindows;
v___x_114_ = lean_strict_and(v___x_113_, v_supportInterpreter_66_);
v___x_115_ = l_Lake_buildLeanExeSync(v___x_112_, v_objs_76_, v_libs_77_, v_args_79_, v___x_114_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___x_105_);
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(lean_object* v_self_129_, lean_object* v_pkg_130_, lean_object* v_exeName_131_, lean_object* v_supportInterpreter_132_, lean_object* v_info_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
uint8_t v_supportInterpreter_boxed_141_; lean_object* v_res_142_; 
v_supportInterpreter_boxed_141_ = lean_unbox(v_supportInterpreter_132_);
v_res_142_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(v_self_129_, v_pkg_130_, v_exeName_131_, v_supportInterpreter_boxed_141_, v_info_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v_self_129_);
return v_res_142_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__0));
v___x_145_ = l_Lake_BuildTrace_nil(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(lean_object* v___x_146_, lean_object* v___f_147_, lean_object* v_infoJob_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = 0;
v___x_158_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___closed__1);
v___x_159_ = l_Lake_Job_mapM___redArg(v___x_146_, v_infoJob_148_, v___f_147_, v___x_156_, v___x_157_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___y_154_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed(lean_object* v___x_161_, lean_object* v___f_162_, lean_object* v_infoJob_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(v___x_161_, v___f_162_, v_infoJob_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec(v___y_166_);
lean_dec(v___y_165_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(uint8_t v_supportInterpreter_172_, lean_object* v_pkg_173_, lean_object* v_config_174_, lean_object* v_name_175_, lean_object* v_root_176_, lean_object* v___x_177_, lean_object* v___f_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
if (v_supportInterpreter_172_ == 0)
{
lean_object* v_keyName_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_keyName_186_ = lean_ctor_get(v_pkg_173_, 2);
lean_inc(v_keyName_186_);
v___x_187_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_174_);
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v_pkg_173_);
lean_ctor_set(v___x_188_, 1, v_name_175_);
lean_ctor_set(v___x_188_, 2, v___x_187_);
lean_inc(v_root_176_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_root_176_);
v___x_190_ = l_Lake_Module_linkInfoNoExportFacet;
v___x_191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_191_, 0, v_keyName_186_);
lean_ctor_set(v___x_191_, 1, v_root_176_);
v___x_192_ = l_Lake_Module_keyword;
v___x_193_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_ctor_set(v___x_193_, 2, v___x_189_);
lean_ctor_set(v___x_193_, 3, v___x_190_);
lean_inc_ref(v___y_179_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc(v___y_181_);
lean_inc(v___x_177_);
v___x_194_ = lean_apply_7(v___y_179_, v___x_193_, v___x_177_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, lean_box(0));
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v___x_197_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
v_a_196_ = lean_ctor_get(v___x_194_, 1);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_194_, 2);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc(v___y_181_);
v___x_197_ = lean_apply_8(v___f_178_, v_a_195_, v___y_179_, v___x_177_, v___y_181_, v___y_182_, v___y_183_, v_a_196_, lean_box(0));
return v___x_197_;
}
else
{
lean_object* v_a_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v___y_179_);
lean_dec_ref(v___f_178_);
lean_dec(v___x_177_);
v_a_198_ = lean_ctor_get(v___x_194_, 0);
v_a_199_ = lean_ctor_get(v___x_194_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_194_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_inc(v_a_198_);
lean_dec(v___x_194_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_198_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_keyName_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_keyName_207_ = lean_ctor_get(v_pkg_173_, 2);
lean_inc(v_keyName_207_);
v___x_208_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_174_);
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v_pkg_173_);
lean_ctor_set(v___x_209_, 1, v_name_175_);
lean_ctor_set(v___x_209_, 2, v___x_208_);
lean_inc(v_root_176_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_root_176_);
v___x_211_ = l_Lake_Module_linkInfoExportFacet;
v___x_212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_212_, 0, v_keyName_207_);
lean_ctor_set(v___x_212_, 1, v_root_176_);
v___x_213_ = l_Lake_Module_keyword;
v___x_214_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
lean_ctor_set(v___x_214_, 2, v___x_210_);
lean_ctor_set(v___x_214_, 3, v___x_211_);
lean_inc_ref(v___y_179_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc(v___y_181_);
lean_inc(v___x_177_);
v___x_215_ = lean_apply_7(v___y_179_, v___x_214_, v___x_177_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, lean_box(0));
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
v_a_217_ = lean_ctor_get(v___x_215_, 1);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_215_, 2);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc(v___y_181_);
v___x_218_ = lean_apply_8(v___f_178_, v_a_216_, v___y_179_, v___x_177_, v___y_181_, v___y_182_, v___y_183_, v_a_217_, lean_box(0));
return v___x_218_;
}
else
{
lean_object* v_a_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec_ref(v___y_179_);
lean_dec_ref(v___f_178_);
lean_dec(v___x_177_);
v_a_219_ = lean_ctor_get(v___x_215_, 0);
v_a_220_ = lean_ctor_get(v___x_215_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_215_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_inc(v_a_219_);
lean_dec(v___x_215_);
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
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_219_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_a_220_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed(lean_object* v_supportInterpreter_228_, lean_object* v_pkg_229_, lean_object* v_config_230_, lean_object* v_name_231_, lean_object* v_root_232_, lean_object* v___x_233_, lean_object* v___f_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
uint8_t v_supportInterpreter_boxed_242_; lean_object* v_res_243_; 
v_supportInterpreter_boxed_242_ = lean_unbox(v_supportInterpreter_228_);
v_res_243_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(v_supportInterpreter_boxed_242_, v_pkg_229_, v_config_230_, v_name_231_, v_root_232_, v___x_233_, v___f_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec(v___y_237_);
lean_dec(v___y_236_);
lean_dec(v_config_230_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object* v_self_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_config_253_; lean_object* v_pkg_254_; lean_object* v_name_255_; lean_object* v_root_256_; lean_object* v_exeName_257_; uint8_t v_supportInterpreter_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___f_265_; lean_object* v___x_266_; 
v_config_253_ = lean_ctor_get(v_self_245_, 2);
lean_inc(v_config_253_);
v_pkg_254_ = lean_ctor_get(v_self_245_, 0);
lean_inc_ref_n(v_pkg_254_, 3);
v_name_255_ = lean_ctor_get(v_self_245_, 1);
lean_inc_n(v_name_255_, 2);
v_root_256_ = lean_ctor_get(v_config_253_, 2);
lean_inc(v_root_256_);
v_exeName_257_ = lean_ctor_get(v_config_253_, 3);
v_supportInterpreter_258_ = lean_ctor_get_uint8(v_config_253_, sizeof(void*)*7);
v___x_259_ = lean_box(v_supportInterpreter_258_);
lean_inc_ref(v_exeName_257_);
v___f_260_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed), 12, 4);
lean_closure_set(v___f_260_, 0, v_self_245_);
lean_closure_set(v___f_260_, 1, v_pkg_254_);
lean_closure_set(v___f_260_, 2, v_exeName_257_);
lean_closure_set(v___f_260_, 3, v___x_259_);
v___x_261_ = l_Lake_instDataKindFilePath;
v___f_262_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed), 10, 2);
lean_closure_set(v___f_262_, 0, v___x_261_);
lean_closure_set(v___f_262_, 1, v___f_260_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_pkg_254_);
v___x_264_ = lean_box(v_supportInterpreter_258_);
v___f_265_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed), 14, 7);
lean_closure_set(v___f_265_, 0, v___x_264_);
lean_closure_set(v___f_265_, 1, v_pkg_254_);
lean_closure_set(v___f_265_, 2, v_config_253_);
lean_closure_set(v___f_265_, 3, v_name_255_);
lean_closure_set(v___f_265_, 4, v_root_256_);
lean_closure_set(v___f_265_, 5, v___x_263_);
lean_closure_set(v___f_265_, 6, v___f_262_);
v___x_266_ = l_Lake_ensureJob___redArg(v___x_261_, v___f_265_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_296_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_a_268_ = lean_ctor_get(v___x_266_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_296_ == 0)
{
v___x_270_ = v___x_266_;
v_isShared_271_ = v_isSharedCheck_296_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_296_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_task_272_; lean_object* v_kind_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_294_; 
v_task_272_ = lean_ctor_get(v_a_267_, 0);
v_kind_273_ = lean_ctor_get(v_a_267_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_a_267_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_a_267_, 2);
lean_dec(v_unused_295_);
v___x_275_ = v_a_267_;
v_isShared_276_ = v_isSharedCheck_294_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_kind_273_);
lean_inc(v_task_272_);
lean_dec(v_a_267_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_294_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_registeredJobs_277_; lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v_job_285_; 
v_registeredJobs_277_ = lean_ctor_get(v_a_250_, 3);
v___x_278_ = lean_st_ref_take(v_registeredJobs_277_);
v___x_279_ = 1;
v___x_280_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_255_, v___x_279_);
v___x_281_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0));
v___x_282_ = lean_string_append(v___x_280_, v___x_281_);
v___x_283_ = 0;
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 2, v___x_282_);
v_job_285_ = v___x_275_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_task_272_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_kind_273_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v___x_282_);
v_job_285_ = v_reuseFailAlloc_293_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
lean_ctor_set_uint8(v_job_285_, sizeof(void*)*3, v___x_283_);
lean_inc_ref(v_job_285_);
v___x_286_ = l_Lake_Job_toOpaque___redArg(v_job_285_);
v___x_287_ = lean_array_push(v___x_278_, v___x_286_);
v___x_288_ = lean_st_ref_set(v_registeredJobs_277_, v___x_287_);
v___x_289_ = l_Lake_Job_renew___redArg(v_job_285_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_289_);
v___x_291_ = v___x_270_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_a_268_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
else
{
lean_dec(v_name_255_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object* v_self_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(v_self_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec(v_a_300_);
lean_dec(v_a_299_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t v_fmt_306_, lean_object* v_a_307_){
_start:
{
if (v_fmt_306_ == 0)
{
return v_a_307_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = l_Lake_mkRelPathString(v_a_307_);
v___x_309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
v___x_310_ = l_Lean_Json_compress(v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object* v_fmt_311_, lean_object* v_a_312_){
_start:
{
uint8_t v_fmt_boxed_313_; lean_object* v_res_314_; 
v_fmt_boxed_313_ = lean_unbox(v_fmt_311_);
v_res_314_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(v_fmt_boxed_313_, v_a_312_);
return v_res_314_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___f_317_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_318_ = 1;
v___x_319_ = l_Lake_instDataKindFilePath;
v___x_320_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__1));
v___x_321_ = l_Lake_LeanExe_keyword;
v___x_322_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_319_);
lean_ctor_set(v___x_322_, 3, v___f_317_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*4, v___x_318_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*4 + 1, v___x_318_);
return v___x_322_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_once(&l_Lake_LeanExe_exeFacetConfig___closed__2, &l_Lake_LeanExe_exeFacetConfig___closed__2_once, _init_l_Lake_LeanExe_exeFacetConfig___closed__2);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object* v_lib_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_pkg_332_; lean_object* v_name_333_; lean_object* v_keyName_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_pkg_332_ = lean_ctor_get(v_lib_324_, 0);
v_name_333_ = lean_ctor_get(v_lib_324_, 1);
v_keyName_334_ = lean_ctor_get(v_pkg_332_, 2);
v___x_335_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_333_);
lean_inc(v_keyName_334_);
v___x_336_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_336_, 0, v_keyName_334_);
lean_ctor_set(v___x_336_, 1, v_name_333_);
v___x_337_ = l_Lake_LeanExe_keyword;
v___x_338_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v_lib_324_);
lean_ctor_set(v___x_338_, 3, v___x_335_);
lean_inc_ref(v_a_329_);
lean_inc(v_a_328_);
lean_inc(v_a_327_);
lean_inc(v_a_326_);
v___x_339_ = lean_apply_7(v_a_325_, v___x_338_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, lean_box(0));
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object* v_lib_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(v_lib_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec(v_a_343_);
lean_dec(v_a_342_);
return v_res_348_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_350_; lean_object* v___f_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_350_ = 0;
v___f_351_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_352_ = 1;
v___x_353_ = l_Lake_instDataKindFilePath;
v___x_354_ = ((lean_object*)(l_Lake_LeanExe_defaultFacetConfig___closed__0));
v___x_355_ = l_Lake_LeanExe_keyword;
v___x_356_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_353_);
lean_ctor_set(v___x_356_, 3, v___f_351_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*4, v___x_352_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*4 + 1, v___x_350_);
return v___x_356_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig(void){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lake_LeanExe_defaultFacetConfig___closed__1, &l_Lake_LeanExe_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanExe_defaultFacetConfig___closed__1);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object* v_k_358_, lean_object* v_v_359_, lean_object* v_t_360_){
_start:
{
if (lean_obj_tag(v_t_360_) == 0)
{
lean_object* v_size_361_; lean_object* v_k_362_; lean_object* v_v_363_; lean_object* v_l_364_; lean_object* v_r_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_645_; 
v_size_361_ = lean_ctor_get(v_t_360_, 0);
v_k_362_ = lean_ctor_get(v_t_360_, 1);
v_v_363_ = lean_ctor_get(v_t_360_, 2);
v_l_364_ = lean_ctor_get(v_t_360_, 3);
v_r_365_ = lean_ctor_get(v_t_360_, 4);
v_isSharedCheck_645_ = !lean_is_exclusive(v_t_360_);
if (v_isSharedCheck_645_ == 0)
{
v___x_367_ = v_t_360_;
v_isShared_368_ = v_isSharedCheck_645_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_r_365_);
lean_inc(v_l_364_);
lean_inc(v_v_363_);
lean_inc(v_k_362_);
lean_inc(v_size_361_);
lean_dec(v_t_360_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_645_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___x_369_; 
v___x_369_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_358_, v_k_362_);
switch(v___x_369_)
{
case 0:
{
lean_object* v_impl_370_; lean_object* v___x_371_; 
lean_dec(v_size_361_);
v_impl_370_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_358_, v_v_359_, v_l_364_);
v___x_371_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_365_) == 0)
{
lean_object* v_size_372_; lean_object* v_size_373_; lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v_l_376_; lean_object* v_r_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_size_372_ = lean_ctor_get(v_r_365_, 0);
v_size_373_ = lean_ctor_get(v_impl_370_, 0);
lean_inc(v_size_373_);
v_k_374_ = lean_ctor_get(v_impl_370_, 1);
lean_inc(v_k_374_);
v_v_375_ = lean_ctor_get(v_impl_370_, 2);
lean_inc(v_v_375_);
v_l_376_ = lean_ctor_get(v_impl_370_, 3);
lean_inc(v_l_376_);
v_r_377_ = lean_ctor_get(v_impl_370_, 4);
lean_inc(v_r_377_);
v___x_378_ = lean_unsigned_to_nat(3u);
v___x_379_ = lean_nat_mul(v___x_378_, v_size_372_);
v___x_380_ = lean_nat_dec_lt(v___x_379_, v_size_373_);
lean_dec(v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
lean_dec(v_r_377_);
lean_dec(v_l_376_);
lean_dec(v_v_375_);
lean_dec(v_k_374_);
v___x_381_ = lean_nat_add(v___x_371_, v_size_373_);
lean_dec(v_size_373_);
v___x_382_ = lean_nat_add(v___x_381_, v_size_372_);
lean_dec(v___x_381_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 3, v_impl_370_);
lean_ctor_set(v___x_367_, 0, v___x_382_);
v___x_384_ = v___x_367_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v_impl_370_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v_r_365_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
else
{
lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_451_; 
v_isSharedCheck_451_ = !lean_is_exclusive(v_impl_370_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; lean_object* v_unused_453_; lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; 
v_unused_452_ = lean_ctor_get(v_impl_370_, 4);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_impl_370_, 3);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_impl_370_, 2);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_impl_370_, 1);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_impl_370_, 0);
lean_dec(v_unused_456_);
v___x_387_ = v_impl_370_;
v_isShared_388_ = v_isSharedCheck_451_;
goto v_resetjp_386_;
}
else
{
lean_dec(v_impl_370_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_451_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_size_389_; lean_object* v_size_390_; lean_object* v_k_391_; lean_object* v_v_392_; lean_object* v_l_393_; lean_object* v_r_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_size_389_ = lean_ctor_get(v_l_376_, 0);
v_size_390_ = lean_ctor_get(v_r_377_, 0);
v_k_391_ = lean_ctor_get(v_r_377_, 1);
v_v_392_ = lean_ctor_get(v_r_377_, 2);
v_l_393_ = lean_ctor_get(v_r_377_, 3);
v_r_394_ = lean_ctor_get(v_r_377_, 4);
v___x_395_ = lean_unsigned_to_nat(2u);
v___x_396_ = lean_nat_mul(v___x_395_, v_size_389_);
v___x_397_ = lean_nat_dec_lt(v_size_390_, v___x_396_);
lean_dec(v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_426_; 
lean_inc(v_r_394_);
lean_inc(v_l_393_);
lean_inc(v_v_392_);
lean_inc(v_k_391_);
v_isSharedCheck_426_ = !lean_is_exclusive(v_r_377_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; lean_object* v_unused_428_; lean_object* v_unused_429_; lean_object* v_unused_430_; lean_object* v_unused_431_; 
v_unused_427_ = lean_ctor_get(v_r_377_, 4);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_r_377_, 3);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_r_377_, 2);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_r_377_, 1);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_r_377_, 0);
lean_dec(v_unused_431_);
v___x_399_ = v_r_377_;
v_isShared_400_ = v_isSharedCheck_426_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_r_377_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_426_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___x_414_; lean_object* v___y_416_; 
v___x_401_ = lean_nat_add(v___x_371_, v_size_373_);
lean_dec(v_size_373_);
v___x_402_ = lean_nat_add(v___x_401_, v_size_372_);
lean_dec(v___x_401_);
v___x_414_ = lean_nat_add(v___x_371_, v_size_389_);
if (lean_obj_tag(v_l_393_) == 0)
{
lean_object* v_size_424_; 
v_size_424_ = lean_ctor_get(v_l_393_, 0);
lean_inc(v_size_424_);
v___y_416_ = v_size_424_;
goto v___jp_415_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___y_416_ = v___x_425_;
goto v___jp_415_;
}
v___jp_403_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_nat_add(v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec(v___y_405_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 4, v_r_365_);
lean_ctor_set(v___x_399_, 3, v_r_394_);
lean_ctor_set(v___x_399_, 2, v_v_363_);
lean_ctor_set(v___x_399_, 1, v_k_362_);
lean_ctor_set(v___x_399_, 0, v___x_407_);
v___x_409_ = v___x_399_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_r_394_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_r_365_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 4, v___x_409_);
lean_ctor_set(v___x_387_, 3, v___y_404_);
lean_ctor_set(v___x_387_, 2, v_v_392_);
lean_ctor_set(v___x_387_, 1, v_k_391_);
lean_ctor_set(v___x_387_, 0, v___x_402_);
v___x_411_ = v___x_387_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_k_391_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_v_392_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v___y_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_nat_add(v___x_414_, v___y_416_);
lean_dec(v___y_416_);
lean_dec(v___x_414_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_l_393_);
lean_ctor_set(v___x_367_, 3, v_l_376_);
lean_ctor_set(v___x_367_, 2, v_v_375_);
lean_ctor_set(v___x_367_, 1, v_k_374_);
lean_ctor_set(v___x_367_, 0, v___x_417_);
v___x_419_ = v___x_367_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_l_376_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_l_393_);
v___x_419_ = v_reuseFailAlloc_423_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; 
v___x_420_ = lean_nat_add(v___x_371_, v_size_372_);
if (lean_obj_tag(v_r_394_) == 0)
{
lean_object* v_size_421_; 
v_size_421_ = lean_ctor_get(v_r_394_, 0);
lean_inc(v_size_421_);
v___y_404_ = v___x_419_;
v___y_405_ = v___x_420_;
v___y_406_ = v_size_421_;
goto v___jp_403_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___y_404_ = v___x_419_;
v___y_405_ = v___x_420_;
v___y_406_ = v___x_422_;
goto v___jp_403_;
}
}
}
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
lean_del_object(v___x_367_);
v___x_432_ = lean_nat_add(v___x_371_, v_size_373_);
lean_dec(v_size_373_);
v___x_433_ = lean_nat_add(v___x_432_, v_size_372_);
lean_dec(v___x_432_);
v___x_434_ = lean_nat_add(v___x_371_, v_size_372_);
v___x_435_ = lean_nat_add(v___x_434_, v_size_390_);
lean_dec(v___x_434_);
lean_inc_ref(v_r_365_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 4, v_r_365_);
lean_ctor_set(v___x_387_, 3, v_r_377_);
lean_ctor_set(v___x_387_, 2, v_v_363_);
lean_ctor_set(v___x_387_, 1, v_k_362_);
lean_ctor_set(v___x_387_, 0, v___x_435_);
v___x_437_ = v___x_387_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_r_377_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_r_365_);
v___x_437_ = v_reuseFailAlloc_450_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_isSharedCheck_444_ = !lean_is_exclusive(v_r_365_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_445_ = lean_ctor_get(v_r_365_, 4);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_r_365_, 3);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_r_365_, 2);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_r_365_, 1);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_r_365_, 0);
lean_dec(v_unused_449_);
v___x_439_ = v_r_365_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_r_365_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 4, v___x_437_);
lean_ctor_set(v___x_439_, 3, v_l_376_);
lean_ctor_set(v___x_439_, 2, v_v_375_);
lean_ctor_set(v___x_439_, 1, v_k_374_);
lean_ctor_set(v___x_439_, 0, v___x_433_);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_l_376_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v___x_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_457_; 
v_l_457_ = lean_ctor_get(v_impl_370_, 3);
lean_inc(v_l_457_);
if (lean_obj_tag(v_l_457_) == 0)
{
lean_object* v_r_458_; lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_471_; 
v_r_458_ = lean_ctor_get(v_impl_370_, 4);
v_k_459_ = lean_ctor_get(v_impl_370_, 1);
v_v_460_ = lean_ctor_get(v_impl_370_, 2);
v_isSharedCheck_471_ = !lean_is_exclusive(v_impl_370_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_472_ = lean_ctor_get(v_impl_370_, 3);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_impl_370_, 0);
lean_dec(v_unused_473_);
v___x_462_ = v_impl_370_;
v_isShared_463_ = v_isSharedCheck_471_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_r_458_);
lean_inc(v_v_460_);
lean_inc(v_k_459_);
lean_dec(v_impl_370_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_471_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_458_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 3, v_r_458_);
lean_ctor_set(v___x_462_, 2, v_v_363_);
lean_ctor_set(v___x_462_, 1, v_k_362_);
lean_ctor_set(v___x_462_, 0, v___x_371_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_r_458_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_r_458_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v___x_466_);
lean_ctor_set(v___x_367_, 3, v_l_457_);
lean_ctor_set(v___x_367_, 2, v_v_460_);
lean_ctor_set(v___x_367_, 1, v_k_459_);
lean_ctor_set(v___x_367_, 0, v___x_464_);
v___x_468_ = v___x_367_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_l_457_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_r_474_; 
v_r_474_ = lean_ctor_get(v_impl_370_, 4);
lean_inc(v_r_474_);
if (lean_obj_tag(v_r_474_) == 0)
{
lean_object* v_k_475_; lean_object* v_v_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_499_; 
v_k_475_ = lean_ctor_get(v_impl_370_, 1);
v_v_476_ = lean_ctor_get(v_impl_370_, 2);
v_isSharedCheck_499_ = !lean_is_exclusive(v_impl_370_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; lean_object* v_unused_501_; lean_object* v_unused_502_; 
v_unused_500_ = lean_ctor_get(v_impl_370_, 4);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_impl_370_, 3);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_impl_370_, 0);
lean_dec(v_unused_502_);
v___x_478_ = v_impl_370_;
v_isShared_479_ = v_isSharedCheck_499_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_v_476_);
lean_inc(v_k_475_);
lean_dec(v_impl_370_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_499_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_k_480_; lean_object* v_v_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_495_; 
v_k_480_ = lean_ctor_get(v_r_474_, 1);
v_v_481_ = lean_ctor_get(v_r_474_, 2);
v_isSharedCheck_495_ = !lean_is_exclusive(v_r_474_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; lean_object* v_unused_498_; 
v_unused_496_ = lean_ctor_get(v_r_474_, 4);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_r_474_, 3);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_r_474_, 0);
lean_dec(v_unused_498_);
v___x_483_ = v_r_474_;
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_v_481_);
lean_inc(v_k_480_);
lean_dec(v_r_474_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(3u);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_l_457_);
lean_ctor_set(v___x_483_, 3, v_l_457_);
lean_ctor_set(v___x_483_, 2, v_v_476_);
lean_ctor_set(v___x_483_, 1, v_k_475_);
lean_ctor_set(v___x_483_, 0, v___x_371_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_k_475_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_v_476_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_l_457_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_l_457_);
v___x_487_ = v_reuseFailAlloc_494_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 4, v_l_457_);
lean_ctor_set(v___x_478_, 2, v_v_363_);
lean_ctor_set(v___x_478_, 1, v_k_362_);
lean_ctor_set(v___x_478_, 0, v___x_371_);
v___x_489_ = v___x_478_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_l_457_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_l_457_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v___x_489_);
lean_ctor_set(v___x_367_, 3, v___x_487_);
lean_ctor_set(v___x_367_, 2, v_v_481_);
lean_ctor_set(v___x_367_, 1, v_k_480_);
lean_ctor_set(v___x_367_, 0, v___x_485_);
v___x_491_ = v___x_367_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_k_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_v_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(2u);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_r_474_);
lean_ctor_set(v___x_367_, 3, v_impl_370_);
lean_ctor_set(v___x_367_, 0, v___x_503_);
v___x_505_ = v___x_367_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_impl_370_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_r_474_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
case 1:
{
lean_object* v___x_508_; 
lean_dec(v_v_363_);
lean_dec(v_k_362_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 2, v_v_359_);
lean_ctor_set(v___x_367_, 1, v_k_358_);
v___x_508_ = v___x_367_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_size_361_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_k_358_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_v_359_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_l_364_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_r_365_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
default: 
{
lean_object* v_impl_510_; lean_object* v___x_511_; 
lean_dec(v_size_361_);
v_impl_510_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_358_, v_v_359_, v_r_365_);
v___x_511_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_364_) == 0)
{
lean_object* v_size_512_; lean_object* v_size_513_; lean_object* v_k_514_; lean_object* v_v_515_; lean_object* v_l_516_; lean_object* v_r_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_size_512_ = lean_ctor_get(v_l_364_, 0);
v_size_513_ = lean_ctor_get(v_impl_510_, 0);
lean_inc(v_size_513_);
v_k_514_ = lean_ctor_get(v_impl_510_, 1);
lean_inc(v_k_514_);
v_v_515_ = lean_ctor_get(v_impl_510_, 2);
lean_inc(v_v_515_);
v_l_516_ = lean_ctor_get(v_impl_510_, 3);
lean_inc(v_l_516_);
v_r_517_ = lean_ctor_get(v_impl_510_, 4);
lean_inc(v_r_517_);
v___x_518_ = lean_unsigned_to_nat(3u);
v___x_519_ = lean_nat_mul(v___x_518_, v_size_512_);
v___x_520_ = lean_nat_dec_lt(v___x_519_, v_size_513_);
lean_dec(v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec(v_r_517_);
lean_dec(v_l_516_);
lean_dec(v_v_515_);
lean_dec(v_k_514_);
v___x_521_ = lean_nat_add(v___x_511_, v_size_512_);
v___x_522_ = lean_nat_add(v___x_521_, v_size_513_);
lean_dec(v_size_513_);
lean_dec(v___x_521_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_impl_510_);
lean_ctor_set(v___x_367_, 0, v___x_522_);
v___x_524_ = v___x_367_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_l_364_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_impl_510_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_589_; 
v_isSharedCheck_589_ = !lean_is_exclusive(v_impl_510_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; lean_object* v_unused_594_; 
v_unused_590_ = lean_ctor_get(v_impl_510_, 4);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_impl_510_, 3);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_impl_510_, 2);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_impl_510_, 1);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_impl_510_, 0);
lean_dec(v_unused_594_);
v___x_527_ = v_impl_510_;
v_isShared_528_ = v_isSharedCheck_589_;
goto v_resetjp_526_;
}
else
{
lean_dec(v_impl_510_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_589_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_size_529_; lean_object* v_k_530_; lean_object* v_v_531_; lean_object* v_l_532_; lean_object* v_r_533_; lean_object* v_size_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_size_529_ = lean_ctor_get(v_l_516_, 0);
v_k_530_ = lean_ctor_get(v_l_516_, 1);
v_v_531_ = lean_ctor_get(v_l_516_, 2);
v_l_532_ = lean_ctor_get(v_l_516_, 3);
v_r_533_ = lean_ctor_get(v_l_516_, 4);
v_size_534_ = lean_ctor_get(v_r_517_, 0);
v___x_535_ = lean_unsigned_to_nat(2u);
v___x_536_ = lean_nat_mul(v___x_535_, v_size_534_);
v___x_537_ = lean_nat_dec_lt(v_size_529_, v___x_536_);
lean_dec(v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_565_; 
lean_inc(v_r_533_);
lean_inc(v_l_532_);
lean_inc(v_v_531_);
lean_inc(v_k_530_);
v_isSharedCheck_565_ = !lean_is_exclusive(v_l_516_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_566_ = lean_ctor_get(v_l_516_, 4);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_516_, 3);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_l_516_, 2);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_l_516_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_l_516_, 0);
lean_dec(v_unused_570_);
v___x_539_ = v_l_516_;
v_isShared_540_ = v_isSharedCheck_565_;
goto v_resetjp_538_;
}
else
{
lean_dec(v_l_516_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_565_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_555_; 
v___x_541_ = lean_nat_add(v___x_511_, v_size_512_);
v___x_542_ = lean_nat_add(v___x_541_, v_size_513_);
lean_dec(v_size_513_);
if (lean_obj_tag(v_l_532_) == 0)
{
lean_object* v_size_563_; 
v_size_563_ = lean_ctor_get(v_l_532_, 0);
lean_inc(v_size_563_);
v___y_555_ = v_size_563_;
goto v___jp_554_;
}
else
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___y_555_ = v___x_564_;
goto v___jp_554_;
}
v___jp_543_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_nat_add(v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 4, v_r_517_);
lean_ctor_set(v___x_539_, 3, v_r_533_);
lean_ctor_set(v___x_539_, 2, v_v_515_);
lean_ctor_set(v___x_539_, 1, v_k_514_);
lean_ctor_set(v___x_539_, 0, v___x_547_);
v___x_549_ = v___x_539_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_r_533_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_r_517_);
v___x_549_ = v_reuseFailAlloc_553_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 4, v___x_549_);
lean_ctor_set(v___x_527_, 3, v___y_544_);
lean_ctor_set(v___x_527_, 2, v_v_531_);
lean_ctor_set(v___x_527_, 1, v_k_530_);
lean_ctor_set(v___x_527_, 0, v___x_542_);
v___x_551_ = v___x_527_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_530_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_531_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v___y_544_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_nat_add(v___x_541_, v___y_555_);
lean_dec(v___y_555_);
lean_dec(v___x_541_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_l_532_);
lean_ctor_set(v___x_367_, 0, v___x_556_);
v___x_558_ = v___x_367_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_l_364_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_l_532_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; 
v___x_559_ = lean_nat_add(v___x_511_, v_size_534_);
if (lean_obj_tag(v_r_533_) == 0)
{
lean_object* v_size_560_; 
v_size_560_ = lean_ctor_get(v_r_533_, 0);
lean_inc(v_size_560_);
v___y_544_ = v___x_558_;
v___y_545_ = v___x_559_;
v___y_546_ = v_size_560_;
goto v___jp_543_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___y_544_ = v___x_558_;
v___y_545_ = v___x_559_;
v___y_546_ = v___x_561_;
goto v___jp_543_;
}
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_del_object(v___x_367_);
v___x_571_ = lean_nat_add(v___x_511_, v_size_512_);
v___x_572_ = lean_nat_add(v___x_571_, v_size_513_);
lean_dec(v_size_513_);
v___x_573_ = lean_nat_add(v___x_571_, v_size_529_);
lean_dec(v___x_571_);
lean_inc_ref(v_l_364_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 4, v_l_516_);
lean_ctor_set(v___x_527_, 3, v_l_364_);
lean_ctor_set(v___x_527_, 2, v_v_363_);
lean_ctor_set(v___x_527_, 1, v_k_362_);
lean_ctor_set(v___x_527_, 0, v___x_573_);
v___x_575_ = v___x_527_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_l_364_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_l_516_);
v___x_575_ = v_reuseFailAlloc_588_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_isSharedCheck_582_ = !lean_is_exclusive(v_l_364_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_583_ = lean_ctor_get(v_l_364_, 4);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_l_364_, 3);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_l_364_, 2);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_l_364_, 1);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_l_364_, 0);
lean_dec(v_unused_587_);
v___x_577_ = v_l_364_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_dec(v_l_364_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 4, v_r_517_);
lean_ctor_set(v___x_577_, 3, v___x_575_);
lean_ctor_set(v___x_577_, 2, v_v_515_);
lean_ctor_set(v___x_577_, 1, v_k_514_);
lean_ctor_set(v___x_577_, 0, v___x_572_);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_r_517_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_595_; 
v_l_595_ = lean_ctor_get(v_impl_510_, 3);
lean_inc(v_l_595_);
if (lean_obj_tag(v_l_595_) == 0)
{
lean_object* v_r_596_; lean_object* v_k_597_; lean_object* v_v_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_621_; 
v_r_596_ = lean_ctor_get(v_impl_510_, 4);
v_k_597_ = lean_ctor_get(v_impl_510_, 1);
v_v_598_ = lean_ctor_get(v_impl_510_, 2);
v_isSharedCheck_621_ = !lean_is_exclusive(v_impl_510_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; lean_object* v_unused_623_; 
v_unused_622_ = lean_ctor_get(v_impl_510_, 3);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_impl_510_, 0);
lean_dec(v_unused_623_);
v___x_600_ = v_impl_510_;
v_isShared_601_ = v_isSharedCheck_621_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_r_596_);
lean_inc(v_v_598_);
lean_inc(v_k_597_);
lean_dec(v_impl_510_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_621_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_617_; 
v_k_602_ = lean_ctor_get(v_l_595_, 1);
v_v_603_ = lean_ctor_get(v_l_595_, 2);
v_isSharedCheck_617_ = !lean_is_exclusive(v_l_595_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_618_ = lean_ctor_get(v_l_595_, 4);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_l_595_, 3);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_l_595_, 0);
lean_dec(v_unused_620_);
v___x_605_ = v_l_595_;
v_isShared_606_ = v_isSharedCheck_617_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_dec(v_l_595_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_617_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_596_, 2);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v_r_596_);
lean_ctor_set(v___x_605_, 3, v_r_596_);
lean_ctor_set(v___x_605_, 2, v_v_363_);
lean_ctor_set(v___x_605_, 1, v_k_362_);
lean_ctor_set(v___x_605_, 0, v___x_511_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_r_596_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_r_596_);
v___x_609_ = v_reuseFailAlloc_616_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
lean_inc(v_r_596_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 3, v_r_596_);
lean_ctor_set(v___x_600_, 0, v___x_511_);
v___x_611_ = v___x_600_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_597_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_r_596_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_r_596_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v___x_611_);
lean_ctor_set(v___x_367_, 3, v___x_609_);
lean_ctor_set(v___x_367_, 2, v_v_603_);
lean_ctor_set(v___x_367_, 1, v_k_602_);
lean_ctor_set(v___x_367_, 0, v___x_607_);
v___x_613_ = v___x_367_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
else
{
lean_object* v_r_624_; 
v_r_624_ = lean_ctor_get(v_impl_510_, 4);
lean_inc(v_r_624_);
if (lean_obj_tag(v_r_624_) == 0)
{
lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_637_; 
v_k_625_ = lean_ctor_get(v_impl_510_, 1);
v_v_626_ = lean_ctor_get(v_impl_510_, 2);
v_isSharedCheck_637_ = !lean_is_exclusive(v_impl_510_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_638_ = lean_ctor_get(v_impl_510_, 4);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_impl_510_, 3);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_impl_510_, 0);
lean_dec(v_unused_640_);
v___x_628_ = v_impl_510_;
v_isShared_629_ = v_isSharedCheck_637_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_v_626_);
lean_inc(v_k_625_);
lean_dec(v_impl_510_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_637_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(3u);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v_l_595_);
lean_ctor_set(v___x_628_, 2, v_v_363_);
lean_ctor_set(v___x_628_, 1, v_k_362_);
lean_ctor_set(v___x_628_, 0, v___x_511_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_l_595_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_l_595_);
v___x_632_ = v_reuseFailAlloc_636_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_r_624_);
lean_ctor_set(v___x_367_, 3, v___x_632_);
lean_ctor_set(v___x_367_, 2, v_v_626_);
lean_ctor_set(v___x_367_, 1, v_k_625_);
lean_ctor_set(v___x_367_, 0, v___x_630_);
v___x_634_ = v___x_367_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_625_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_626_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_r_624_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_unsigned_to_nat(2u);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_impl_510_);
lean_ctor_set(v___x_367_, 3, v_r_624_);
lean_ctor_set(v___x_367_, 0, v___x_641_);
v___x_643_ = v___x_367_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_r_624_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_impl_510_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
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
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_k_358_);
lean_ctor_set(v___x_647_, 2, v_v_359_);
lean_ctor_set(v___x_647_, 3, v_t_360_);
lean_ctor_set(v___x_647_, 4, v_t_360_);
return v___x_647_;
}
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_box(1);
v___x_649_ = l_Lake_LeanExe_defaultFacetConfig;
v___x_650_ = l_Lake_LeanExe_defaultFacet;
v___x_651_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_650_, v___x_649_, v___x_648_);
return v___x_651_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__0, &l_Lake_LeanExe_initFacetConfigs___closed__0_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__0);
v___x_653_ = l_Lake_LeanExe_exeFacetConfig;
v___x_654_ = l_Lake_LeanExe_exeFacet;
v___x_655_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_654_, v___x_653_, v___x_652_);
return v___x_655_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs(void){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__1, &l_Lake_LeanExe_initFacetConfigs___closed__1_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__1);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object* v_00_u03b2_657_, lean_object* v_k_658_, lean_object* v_v_659_, lean_object* v_t_660_, lean_object* v_hl_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_658_, v_v_659_, v_t_660_);
return v___x_662_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Executable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
