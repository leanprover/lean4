// Lean compiler output
// Module: Lake.Build.InputFile
// Imports: public import Lake.Config.FacetConfig import Lake.Build.Job import Lake.Build.Common import Lake.Build.Infos
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
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_InputDir_keyword;
extern lean_object* l_Lake_InputDir_defaultFacet;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_inputTextFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_InputFile_keyword;
extern lean_object* l_Lake_InputFile_defaultFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_InputFile_defaultFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFile_defaultFacetConfig___closed__0 = (const lean_object*)&l_Lake_InputFile_defaultFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_InputFile_defaultFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputFile_defaultFacetConfig___closed__1 = (const lean_object*)&l_Lake_InputFile_defaultFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_InputFile_defaultFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFile_defaultFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_InputFile_defaultFacetConfig;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_InputFile_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputFile_initFacetConfigs___closed__0;
LEAN_EXPORT lean_object* l_Lake_InputFile_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0 = (const lean_object*)&l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_InputDir_defaultFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDir_defaultFacetConfig___closed__0 = (const lean_object*)&l_Lake_InputDir_defaultFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_InputDir_defaultFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_InputDir_defaultFacetConfig___closed__1 = (const lean_object*)&l_Lake_InputDir_defaultFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_InputDir_defaultFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDir_defaultFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_InputDir_defaultFacetConfig;
static lean_once_cell_t l_Lake_InputDir_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_InputDir_initFacetConfigs___closed__0;
LEAN_EXPORT lean_object* l_Lake_InputDir_initFacetConfigs;
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(uint8_t v_text_1_, lean_object* v___x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; 
if (v_text_1_ == 0)
{
lean_object* v___x_13_; 
v___x_13_ = l_Lake_inputBinFile___redArg(v___x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
v___y_11_ = v___x_13_;
goto v___jp_10_;
}
else
{
lean_object* v___x_14_; 
v___x_14_ = l_Lake_inputTextFile___redArg(v___x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
v___y_11_ = v___x_14_;
goto v___jp_10_;
}
v___jp_10_:
{
lean_object* v___x_12_; 
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___y_11_);
lean_ctor_set(v___x_12_, 1, v___y_8_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0___boxed(lean_object* v_text_15_, lean_object* v___x_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
uint8_t v_text_boxed_24_; lean_object* v_res_25_; 
v_text_boxed_24_ = lean_unbox(v_text_15_);
v_res_25_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(v_text_boxed_24_, v___x_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(lean_object* v_t_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_pkg_34_; lean_object* v_config_35_; lean_object* v_name_36_; lean_object* v_dir_37_; lean_object* v_path_38_; uint8_t v_text_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___f_43_; lean_object* v___x_44_; 
v_pkg_34_ = lean_ctor_get(v_t_26_, 0);
lean_inc_ref(v_pkg_34_);
v_config_35_ = lean_ctor_get(v_t_26_, 2);
lean_inc(v_config_35_);
v_name_36_ = lean_ctor_get(v_t_26_, 1);
lean_inc(v_name_36_);
lean_dec_ref(v_t_26_);
v_dir_37_ = lean_ctor_get(v_pkg_34_, 4);
lean_inc_ref(v_dir_37_);
lean_dec_ref(v_pkg_34_);
v_path_38_ = lean_ctor_get(v_config_35_, 0);
lean_inc_ref(v_path_38_);
v_text_39_ = lean_ctor_get_uint8(v_config_35_, sizeof(void*)*1);
lean_dec(v_config_35_);
v___x_40_ = l_Lake_instDataKindFilePath;
v___x_41_ = l_Lake_joinRelative(v_dir_37_, v_path_38_);
v___x_42_ = lean_box(v_text_39_);
v___f_43_ = lean_alloc_closure((void*)(l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0___boxed), 9, 2);
lean_closure_set(v___f_43_, 0, v___x_42_);
lean_closure_set(v___f_43_, 1, v___x_41_);
lean_inc_ref(v_a_31_);
v___x_44_ = l_Lake_ensureJob___redArg(v___x_40_, v___f_43_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_72_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_a_46_ = lean_ctor_get(v___x_44_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_72_ == 0)
{
v___x_48_ = v___x_44_;
v_isShared_49_ = v_isSharedCheck_72_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_72_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v_task_50_; lean_object* v_kind_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_70_; 
v_task_50_ = lean_ctor_get(v_a_45_, 0);
v_kind_51_ = lean_ctor_get(v_a_45_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v_a_45_);
if (v_isSharedCheck_70_ == 0)
{
lean_object* v_unused_71_; 
v_unused_71_ = lean_ctor_get(v_a_45_, 2);
lean_dec(v_unused_71_);
v___x_53_ = v_a_45_;
v_isShared_54_ = v_isSharedCheck_70_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_kind_51_);
lean_inc(v_task_50_);
lean_dec(v_a_45_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_70_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_registeredJobs_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v_job_61_; 
v_registeredJobs_55_ = lean_ctor_get(v_a_31_, 3);
lean_inc(v_registeredJobs_55_);
lean_dec_ref(v_a_31_);
v___x_56_ = lean_st_ref_take(v_registeredJobs_55_);
v___x_57_ = 1;
v___x_58_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_36_, v___x_57_);
v___x_59_ = 0;
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 2, v___x_58_);
v_job_61_ = v___x_53_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_task_50_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_kind_51_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v___x_58_);
v_job_61_ = v_reuseFailAlloc_69_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
lean_ctor_set_uint8(v_job_61_, sizeof(void*)*3, v___x_59_);
lean_inc_ref(v_job_61_);
v___x_62_ = l_Lake_Job_toOpaque___redArg(v_job_61_);
v___x_63_ = lean_array_push(v___x_56_, v___x_62_);
v___x_64_ = lean_st_ref_set(v_registeredJobs_55_, v___x_63_);
lean_dec(v_registeredJobs_55_);
v___x_65_ = l_Lake_Job_renew___redArg(v_job_61_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_65_);
v___x_67_ = v___x_48_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_a_46_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
else
{
lean_dec(v_name_36_);
lean_dec_ref(v_a_31_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___boxed(lean_object* v_t_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(v_t_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(uint8_t v_fmt_82_, lean_object* v_a_83_){
_start:
{
if (v_fmt_82_ == 0)
{
return v_a_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = l_Lake_mkRelPathString(v_a_83_);
v___x_85_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
v___x_86_ = l_Lean_Json_compress(v___x_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0___boxed(lean_object* v_fmt_87_, lean_object* v_a_88_){
_start:
{
uint8_t v_fmt_boxed_89_; lean_object* v_res_90_; 
v_fmt_boxed_89_ = lean_unbox(v_fmt_87_);
v_res_90_ = l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(v_fmt_boxed_89_, v_a_88_);
return v_res_90_;
}
}
static lean_object* _init_l_Lake_InputFile_defaultFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___f_93_ = ((lean_object*)(l_Lake_InputFile_defaultFacetConfig___closed__0));
v___x_94_ = 1;
v___x_95_ = l_Lake_instDataKindFilePath;
v___x_96_ = ((lean_object*)(l_Lake_InputFile_defaultFacetConfig___closed__1));
v___x_97_ = l_Lake_InputFile_keyword;
v___x_98_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_95_);
lean_ctor_set(v___x_98_, 3, v___f_93_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*4, v___x_94_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*4 + 1, v___x_94_);
return v___x_98_;
}
}
static lean_object* _init_l_Lake_InputFile_defaultFacetConfig(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lake_InputFile_defaultFacetConfig___closed__2, &l_Lake_InputFile_defaultFacetConfig___closed__2_once, _init_l_Lake_InputFile_defaultFacetConfig___closed__2);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(lean_object* v_k_100_, lean_object* v_v_101_, lean_object* v_t_102_){
_start:
{
if (lean_obj_tag(v_t_102_) == 0)
{
lean_object* v_size_103_; lean_object* v_k_104_; lean_object* v_v_105_; lean_object* v_l_106_; lean_object* v_r_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_387_; 
v_size_103_ = lean_ctor_get(v_t_102_, 0);
v_k_104_ = lean_ctor_get(v_t_102_, 1);
v_v_105_ = lean_ctor_get(v_t_102_, 2);
v_l_106_ = lean_ctor_get(v_t_102_, 3);
v_r_107_ = lean_ctor_get(v_t_102_, 4);
v_isSharedCheck_387_ = !lean_is_exclusive(v_t_102_);
if (v_isSharedCheck_387_ == 0)
{
v___x_109_ = v_t_102_;
v_isShared_110_ = v_isSharedCheck_387_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_r_107_);
lean_inc(v_l_106_);
lean_inc(v_v_105_);
lean_inc(v_k_104_);
lean_inc(v_size_103_);
lean_dec(v_t_102_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_387_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v___x_111_; 
v___x_111_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_100_, v_k_104_);
switch(v___x_111_)
{
case 0:
{
lean_object* v_impl_112_; lean_object* v___x_113_; 
lean_dec(v_size_103_);
v_impl_112_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_100_, v_v_101_, v_l_106_);
v___x_113_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_107_) == 0)
{
lean_object* v_size_114_; lean_object* v_size_115_; lean_object* v_k_116_; lean_object* v_v_117_; lean_object* v_l_118_; lean_object* v_r_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_size_114_ = lean_ctor_get(v_r_107_, 0);
v_size_115_ = lean_ctor_get(v_impl_112_, 0);
lean_inc(v_size_115_);
v_k_116_ = lean_ctor_get(v_impl_112_, 1);
lean_inc(v_k_116_);
v_v_117_ = lean_ctor_get(v_impl_112_, 2);
lean_inc(v_v_117_);
v_l_118_ = lean_ctor_get(v_impl_112_, 3);
lean_inc(v_l_118_);
v_r_119_ = lean_ctor_get(v_impl_112_, 4);
lean_inc(v_r_119_);
v___x_120_ = lean_unsigned_to_nat(3u);
v___x_121_ = lean_nat_mul(v___x_120_, v_size_114_);
v___x_122_ = lean_nat_dec_lt(v___x_121_, v_size_115_);
lean_dec(v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
lean_dec(v_r_119_);
lean_dec(v_l_118_);
lean_dec(v_v_117_);
lean_dec(v_k_116_);
v___x_123_ = lean_nat_add(v___x_113_, v_size_115_);
lean_dec(v_size_115_);
v___x_124_ = lean_nat_add(v___x_123_, v_size_114_);
lean_dec(v___x_123_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 3, v_impl_112_);
lean_ctor_set(v___x_109_, 0, v___x_124_);
v___x_126_ = v___x_109_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_impl_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_r_107_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
else
{
lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_193_; 
v_isSharedCheck_193_ = !lean_is_exclusive(v_impl_112_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; lean_object* v_unused_195_; lean_object* v_unused_196_; lean_object* v_unused_197_; lean_object* v_unused_198_; 
v_unused_194_ = lean_ctor_get(v_impl_112_, 4);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_impl_112_, 3);
lean_dec(v_unused_195_);
v_unused_196_ = lean_ctor_get(v_impl_112_, 2);
lean_dec(v_unused_196_);
v_unused_197_ = lean_ctor_get(v_impl_112_, 1);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_impl_112_, 0);
lean_dec(v_unused_198_);
v___x_129_ = v_impl_112_;
v_isShared_130_ = v_isSharedCheck_193_;
goto v_resetjp_128_;
}
else
{
lean_dec(v_impl_112_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_193_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_size_131_; lean_object* v_size_132_; lean_object* v_k_133_; lean_object* v_v_134_; lean_object* v_l_135_; lean_object* v_r_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_size_131_ = lean_ctor_get(v_l_118_, 0);
v_size_132_ = lean_ctor_get(v_r_119_, 0);
v_k_133_ = lean_ctor_get(v_r_119_, 1);
v_v_134_ = lean_ctor_get(v_r_119_, 2);
v_l_135_ = lean_ctor_get(v_r_119_, 3);
v_r_136_ = lean_ctor_get(v_r_119_, 4);
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_nat_mul(v___x_137_, v_size_131_);
v___x_139_ = lean_nat_dec_lt(v_size_132_, v___x_138_);
lean_dec(v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_168_; 
lean_inc(v_r_136_);
lean_inc(v_l_135_);
lean_inc(v_v_134_);
lean_inc(v_k_133_);
v_isSharedCheck_168_ = !lean_is_exclusive(v_r_119_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; lean_object* v_unused_170_; lean_object* v_unused_171_; lean_object* v_unused_172_; lean_object* v_unused_173_; 
v_unused_169_ = lean_ctor_get(v_r_119_, 4);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_r_119_, 3);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_r_119_, 2);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_r_119_, 1);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_r_119_, 0);
lean_dec(v_unused_173_);
v___x_141_ = v_r_119_;
v_isShared_142_ = v_isSharedCheck_168_;
goto v_resetjp_140_;
}
else
{
lean_dec(v_r_119_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_168_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v___x_156_; lean_object* v___y_158_; 
v___x_143_ = lean_nat_add(v___x_113_, v_size_115_);
lean_dec(v_size_115_);
v___x_144_ = lean_nat_add(v___x_143_, v_size_114_);
lean_dec(v___x_143_);
v___x_156_ = lean_nat_add(v___x_113_, v_size_131_);
if (lean_obj_tag(v_l_135_) == 0)
{
lean_object* v_size_166_; 
v_size_166_ = lean_ctor_get(v_l_135_, 0);
lean_inc(v_size_166_);
v___y_158_ = v_size_166_;
goto v___jp_157_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_unsigned_to_nat(0u);
v___y_158_ = v___x_167_;
goto v___jp_157_;
}
v___jp_145_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_nat_add(v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec(v___y_147_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 4, v_r_107_);
lean_ctor_set(v___x_141_, 3, v_r_136_);
lean_ctor_set(v___x_141_, 2, v_v_105_);
lean_ctor_set(v___x_141_, 1, v_k_104_);
lean_ctor_set(v___x_141_, 0, v___x_149_);
v___x_151_ = v___x_141_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_r_136_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v_r_107_);
v___x_151_ = v_reuseFailAlloc_155_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_151_);
lean_ctor_set(v___x_129_, 3, v___y_146_);
lean_ctor_set(v___x_129_, 2, v_v_134_);
lean_ctor_set(v___x_129_, 1, v_k_133_);
lean_ctor_set(v___x_129_, 0, v___x_144_);
v___x_153_ = v___x_129_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_k_133_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_v_134_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v___y_146_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_nat_add(v___x_156_, v___y_158_);
lean_dec(v___y_158_);
lean_dec(v___x_156_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_l_135_);
lean_ctor_set(v___x_109_, 3, v_l_118_);
lean_ctor_set(v___x_109_, 2, v_v_117_);
lean_ctor_set(v___x_109_, 1, v_k_116_);
lean_ctor_set(v___x_109_, 0, v___x_159_);
v___x_161_ = v___x_109_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_k_116_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_v_117_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_l_118_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_l_135_);
v___x_161_ = v_reuseFailAlloc_165_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; 
v___x_162_ = lean_nat_add(v___x_113_, v_size_114_);
if (lean_obj_tag(v_r_136_) == 0)
{
lean_object* v_size_163_; 
v_size_163_ = lean_ctor_get(v_r_136_, 0);
lean_inc(v_size_163_);
v___y_146_ = v___x_161_;
v___y_147_ = v___x_162_;
v___y_148_ = v_size_163_;
goto v___jp_145_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___y_146_ = v___x_161_;
v___y_147_ = v___x_162_;
v___y_148_ = v___x_164_;
goto v___jp_145_;
}
}
}
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
lean_del_object(v___x_109_);
v___x_174_ = lean_nat_add(v___x_113_, v_size_115_);
lean_dec(v_size_115_);
v___x_175_ = lean_nat_add(v___x_174_, v_size_114_);
lean_dec(v___x_174_);
v___x_176_ = lean_nat_add(v___x_113_, v_size_114_);
v___x_177_ = lean_nat_add(v___x_176_, v_size_132_);
lean_dec(v___x_176_);
lean_inc_ref(v_r_107_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_107_);
lean_ctor_set(v___x_129_, 3, v_r_119_);
lean_ctor_set(v___x_129_, 2, v_v_105_);
lean_ctor_set(v___x_129_, 1, v_k_104_);
lean_ctor_set(v___x_129_, 0, v___x_177_);
v___x_179_ = v___x_129_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_r_119_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_r_107_);
v___x_179_ = v_reuseFailAlloc_192_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_isSharedCheck_186_ = !lean_is_exclusive(v_r_107_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_187_ = lean_ctor_get(v_r_107_, 4);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_r_107_, 3);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_r_107_, 2);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_r_107_, 1);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_r_107_, 0);
lean_dec(v_unused_191_);
v___x_181_ = v_r_107_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_dec(v_r_107_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 4, v___x_179_);
lean_ctor_set(v___x_181_, 3, v_l_118_);
lean_ctor_set(v___x_181_, 2, v_v_117_);
lean_ctor_set(v___x_181_, 1, v_k_116_);
lean_ctor_set(v___x_181_, 0, v___x_175_);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_k_116_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_v_117_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_l_118_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v___x_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_199_; 
v_l_199_ = lean_ctor_get(v_impl_112_, 3);
lean_inc(v_l_199_);
if (lean_obj_tag(v_l_199_) == 0)
{
lean_object* v_r_200_; lean_object* v_k_201_; lean_object* v_v_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_213_; 
v_r_200_ = lean_ctor_get(v_impl_112_, 4);
v_k_201_ = lean_ctor_get(v_impl_112_, 1);
v_v_202_ = lean_ctor_get(v_impl_112_, 2);
v_isSharedCheck_213_ = !lean_is_exclusive(v_impl_112_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; 
v_unused_214_ = lean_ctor_get(v_impl_112_, 3);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_impl_112_, 0);
lean_dec(v_unused_215_);
v___x_204_ = v_impl_112_;
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_r_200_);
lean_inc(v_v_202_);
lean_inc(v_k_201_);
lean_dec(v_impl_112_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_200_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 3, v_r_200_);
lean_ctor_set(v___x_204_, 2, v_v_105_);
lean_ctor_set(v___x_204_, 1, v_k_104_);
lean_ctor_set(v___x_204_, 0, v___x_113_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_r_200_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_r_200_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v___x_208_);
lean_ctor_set(v___x_109_, 3, v_l_199_);
lean_ctor_set(v___x_109_, 2, v_v_202_);
lean_ctor_set(v___x_109_, 1, v_k_201_);
lean_ctor_set(v___x_109_, 0, v___x_206_);
v___x_210_ = v___x_109_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_k_201_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_v_202_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_l_199_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_r_216_; 
v_r_216_ = lean_ctor_get(v_impl_112_, 4);
lean_inc(v_r_216_);
if (lean_obj_tag(v_r_216_) == 0)
{
lean_object* v_k_217_; lean_object* v_v_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_241_; 
v_k_217_ = lean_ctor_get(v_impl_112_, 1);
v_v_218_ = lean_ctor_get(v_impl_112_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_impl_112_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_242_ = lean_ctor_get(v_impl_112_, 4);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_impl_112_, 3);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_impl_112_, 0);
lean_dec(v_unused_244_);
v___x_220_ = v_impl_112_;
v_isShared_221_ = v_isSharedCheck_241_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_v_218_);
lean_inc(v_k_217_);
lean_dec(v_impl_112_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_241_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_k_222_; lean_object* v_v_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_237_; 
v_k_222_ = lean_ctor_get(v_r_216_, 1);
v_v_223_ = lean_ctor_get(v_r_216_, 2);
v_isSharedCheck_237_ = !lean_is_exclusive(v_r_216_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; 
v_unused_238_ = lean_ctor_get(v_r_216_, 4);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_r_216_, 3);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_r_216_, 0);
lean_dec(v_unused_240_);
v___x_225_ = v_r_216_;
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_v_223_);
lean_inc(v_k_222_);
lean_dec(v_r_216_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(3u);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 4, v_l_199_);
lean_ctor_set(v___x_225_, 3, v_l_199_);
lean_ctor_set(v___x_225_, 2, v_v_218_);
lean_ctor_set(v___x_225_, 1, v_k_217_);
lean_ctor_set(v___x_225_, 0, v___x_113_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_k_217_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_v_218_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_l_199_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_l_199_);
v___x_229_ = v_reuseFailAlloc_236_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 4, v_l_199_);
lean_ctor_set(v___x_220_, 2, v_v_105_);
lean_ctor_set(v___x_220_, 1, v_k_104_);
lean_ctor_set(v___x_220_, 0, v___x_113_);
v___x_231_ = v___x_220_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_l_199_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_l_199_);
v___x_231_ = v_reuseFailAlloc_235_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v___x_231_);
lean_ctor_set(v___x_109_, 3, v___x_229_);
lean_ctor_set(v___x_109_, 2, v_v_223_);
lean_ctor_set(v___x_109_, 1, v_k_222_);
lean_ctor_set(v___x_109_, 0, v___x_227_);
v___x_233_ = v___x_109_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_k_222_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_v_223_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v___x_231_);
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
}
else
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(2u);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_r_216_);
lean_ctor_set(v___x_109_, 3, v_impl_112_);
lean_ctor_set(v___x_109_, 0, v___x_245_);
v___x_247_ = v___x_109_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_impl_112_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_r_216_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
case 1:
{
lean_object* v___x_250_; 
lean_dec(v_v_105_);
lean_dec(v_k_104_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 2, v_v_101_);
lean_ctor_set(v___x_109_, 1, v_k_100_);
v___x_250_ = v___x_109_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_size_103_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_k_100_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_v_101_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_l_106_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v_r_107_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
default: 
{
lean_object* v_impl_252_; lean_object* v___x_253_; 
lean_dec(v_size_103_);
v_impl_252_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_100_, v_v_101_, v_r_107_);
v___x_253_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_106_) == 0)
{
lean_object* v_size_254_; lean_object* v_size_255_; lean_object* v_k_256_; lean_object* v_v_257_; lean_object* v_l_258_; lean_object* v_r_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_size_254_ = lean_ctor_get(v_l_106_, 0);
v_size_255_ = lean_ctor_get(v_impl_252_, 0);
lean_inc(v_size_255_);
v_k_256_ = lean_ctor_get(v_impl_252_, 1);
lean_inc(v_k_256_);
v_v_257_ = lean_ctor_get(v_impl_252_, 2);
lean_inc(v_v_257_);
v_l_258_ = lean_ctor_get(v_impl_252_, 3);
lean_inc(v_l_258_);
v_r_259_ = lean_ctor_get(v_impl_252_, 4);
lean_inc(v_r_259_);
v___x_260_ = lean_unsigned_to_nat(3u);
v___x_261_ = lean_nat_mul(v___x_260_, v_size_254_);
v___x_262_ = lean_nat_dec_lt(v___x_261_, v_size_255_);
lean_dec(v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec(v_r_259_);
lean_dec(v_l_258_);
lean_dec(v_v_257_);
lean_dec(v_k_256_);
v___x_263_ = lean_nat_add(v___x_253_, v_size_254_);
v___x_264_ = lean_nat_add(v___x_263_, v_size_255_);
lean_dec(v_size_255_);
lean_dec(v___x_263_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_impl_252_);
lean_ctor_set(v___x_109_, 0, v___x_264_);
v___x_266_ = v___x_109_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_l_106_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_impl_252_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
else
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_331_; 
v_isSharedCheck_331_ = !lean_is_exclusive(v_impl_252_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; lean_object* v_unused_336_; 
v_unused_332_ = lean_ctor_get(v_impl_252_, 4);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_impl_252_, 3);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_impl_252_, 2);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_impl_252_, 1);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_impl_252_, 0);
lean_dec(v_unused_336_);
v___x_269_ = v_impl_252_;
v_isShared_270_ = v_isSharedCheck_331_;
goto v_resetjp_268_;
}
else
{
lean_dec(v_impl_252_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_331_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_size_271_; lean_object* v_k_272_; lean_object* v_v_273_; lean_object* v_l_274_; lean_object* v_r_275_; lean_object* v_size_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_size_271_ = lean_ctor_get(v_l_258_, 0);
v_k_272_ = lean_ctor_get(v_l_258_, 1);
v_v_273_ = lean_ctor_get(v_l_258_, 2);
v_l_274_ = lean_ctor_get(v_l_258_, 3);
v_r_275_ = lean_ctor_get(v_l_258_, 4);
v_size_276_ = lean_ctor_get(v_r_259_, 0);
v___x_277_ = lean_unsigned_to_nat(2u);
v___x_278_ = lean_nat_mul(v___x_277_, v_size_276_);
v___x_279_ = lean_nat_dec_lt(v_size_271_, v___x_278_);
lean_dec(v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_307_; 
lean_inc(v_r_275_);
lean_inc(v_l_274_);
lean_inc(v_v_273_);
lean_inc(v_k_272_);
v_isSharedCheck_307_ = !lean_is_exclusive(v_l_258_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; 
v_unused_308_ = lean_ctor_get(v_l_258_, 4);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_l_258_, 3);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_l_258_, 2);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_l_258_, 1);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_l_258_, 0);
lean_dec(v_unused_312_);
v___x_281_ = v_l_258_;
v_isShared_282_ = v_isSharedCheck_307_;
goto v_resetjp_280_;
}
else
{
lean_dec(v_l_258_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_307_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_297_; 
v___x_283_ = lean_nat_add(v___x_253_, v_size_254_);
v___x_284_ = lean_nat_add(v___x_283_, v_size_255_);
lean_dec(v_size_255_);
if (lean_obj_tag(v_l_274_) == 0)
{
lean_object* v_size_305_; 
v_size_305_ = lean_ctor_get(v_l_274_, 0);
lean_inc(v_size_305_);
v___y_297_ = v_size_305_;
goto v___jp_296_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___y_297_ = v___x_306_;
goto v___jp_296_;
}
v___jp_285_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_nat_add(v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec(v___y_287_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 4, v_r_259_);
lean_ctor_set(v___x_281_, 3, v_r_275_);
lean_ctor_set(v___x_281_, 2, v_v_257_);
lean_ctor_set(v___x_281_, 1, v_k_256_);
lean_ctor_set(v___x_281_, 0, v___x_289_);
v___x_291_ = v___x_281_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_k_256_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_v_257_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_r_275_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_r_259_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v___x_291_);
lean_ctor_set(v___x_269_, 3, v___y_286_);
lean_ctor_set(v___x_269_, 2, v_v_273_);
lean_ctor_set(v___x_269_, 1, v_k_272_);
lean_ctor_set(v___x_269_, 0, v___x_284_);
v___x_293_ = v___x_269_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_k_272_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_v_273_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v___y_286_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_nat_add(v___x_283_, v___y_297_);
lean_dec(v___y_297_);
lean_dec(v___x_283_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_l_274_);
lean_ctor_set(v___x_109_, 0, v___x_298_);
v___x_300_ = v___x_109_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_l_106_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_l_274_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_nat_add(v___x_253_, v_size_276_);
if (lean_obj_tag(v_r_275_) == 0)
{
lean_object* v_size_302_; 
v_size_302_ = lean_ctor_get(v_r_275_, 0);
lean_inc(v_size_302_);
v___y_286_ = v___x_300_;
v___y_287_ = v___x_301_;
v___y_288_ = v_size_302_;
goto v___jp_285_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___y_286_ = v___x_300_;
v___y_287_ = v___x_301_;
v___y_288_ = v___x_303_;
goto v___jp_285_;
}
}
}
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
lean_del_object(v___x_109_);
v___x_313_ = lean_nat_add(v___x_253_, v_size_254_);
v___x_314_ = lean_nat_add(v___x_313_, v_size_255_);
lean_dec(v_size_255_);
v___x_315_ = lean_nat_add(v___x_313_, v_size_271_);
lean_dec(v___x_313_);
lean_inc_ref(v_l_106_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v_l_258_);
lean_ctor_set(v___x_269_, 3, v_l_106_);
lean_ctor_set(v___x_269_, 2, v_v_105_);
lean_ctor_set(v___x_269_, 1, v_k_104_);
lean_ctor_set(v___x_269_, 0, v___x_315_);
v___x_317_ = v___x_269_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_l_106_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_l_258_);
v___x_317_ = v_reuseFailAlloc_330_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_isSharedCheck_324_ = !lean_is_exclusive(v_l_106_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; lean_object* v_unused_328_; lean_object* v_unused_329_; 
v_unused_325_ = lean_ctor_get(v_l_106_, 4);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_l_106_, 3);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_l_106_, 2);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_l_106_, 1);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_l_106_, 0);
lean_dec(v_unused_329_);
v___x_319_ = v_l_106_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_dec(v_l_106_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 4, v_r_259_);
lean_ctor_set(v___x_319_, 3, v___x_317_);
lean_ctor_set(v___x_319_, 2, v_v_257_);
lean_ctor_set(v___x_319_, 1, v_k_256_);
lean_ctor_set(v___x_319_, 0, v___x_314_);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_k_256_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_v_257_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_323_, 4, v_r_259_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_337_; 
v_l_337_ = lean_ctor_get(v_impl_252_, 3);
lean_inc(v_l_337_);
if (lean_obj_tag(v_l_337_) == 0)
{
lean_object* v_r_338_; lean_object* v_k_339_; lean_object* v_v_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_363_; 
v_r_338_ = lean_ctor_get(v_impl_252_, 4);
v_k_339_ = lean_ctor_get(v_impl_252_, 1);
v_v_340_ = lean_ctor_get(v_impl_252_, 2);
v_isSharedCheck_363_ = !lean_is_exclusive(v_impl_252_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; lean_object* v_unused_365_; 
v_unused_364_ = lean_ctor_get(v_impl_252_, 3);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_impl_252_, 0);
lean_dec(v_unused_365_);
v___x_342_ = v_impl_252_;
v_isShared_343_ = v_isSharedCheck_363_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_r_338_);
lean_inc(v_v_340_);
lean_inc(v_k_339_);
lean_dec(v_impl_252_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_363_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_k_344_; lean_object* v_v_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_359_; 
v_k_344_ = lean_ctor_get(v_l_337_, 1);
v_v_345_ = lean_ctor_get(v_l_337_, 2);
v_isSharedCheck_359_ = !lean_is_exclusive(v_l_337_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; 
v_unused_360_ = lean_ctor_get(v_l_337_, 4);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_l_337_, 3);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_l_337_, 0);
lean_dec(v_unused_362_);
v___x_347_ = v_l_337_;
v_isShared_348_ = v_isSharedCheck_359_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_v_345_);
lean_inc(v_k_344_);
lean_dec(v_l_337_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_359_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_338_, 2);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 4, v_r_338_);
lean_ctor_set(v___x_347_, 3, v_r_338_);
lean_ctor_set(v___x_347_, 2, v_v_105_);
lean_ctor_set(v___x_347_, 1, v_k_104_);
lean_ctor_set(v___x_347_, 0, v___x_253_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v_r_338_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v_r_338_);
v___x_351_ = v_reuseFailAlloc_358_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
lean_inc(v_r_338_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 3, v_r_338_);
lean_ctor_set(v___x_342_, 0, v___x_253_);
v___x_353_ = v___x_342_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_k_339_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_v_340_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_r_338_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_r_338_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v___x_353_);
lean_ctor_set(v___x_109_, 3, v___x_351_);
lean_ctor_set(v___x_109_, 2, v_v_345_);
lean_ctor_set(v___x_109_, 1, v_k_344_);
lean_ctor_set(v___x_109_, 0, v___x_349_);
v___x_355_ = v___x_109_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_k_344_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_v_345_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
else
{
lean_object* v_r_366_; 
v_r_366_ = lean_ctor_get(v_impl_252_, 4);
lean_inc(v_r_366_);
if (lean_obj_tag(v_r_366_) == 0)
{
lean_object* v_k_367_; lean_object* v_v_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_379_; 
v_k_367_ = lean_ctor_get(v_impl_252_, 1);
v_v_368_ = lean_ctor_get(v_impl_252_, 2);
v_isSharedCheck_379_ = !lean_is_exclusive(v_impl_252_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_380_ = lean_ctor_get(v_impl_252_, 4);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_impl_252_, 3);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_impl_252_, 0);
lean_dec(v_unused_382_);
v___x_370_ = v_impl_252_;
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_v_368_);
lean_inc(v_k_367_);
lean_dec(v_impl_252_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(3u);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_l_337_);
lean_ctor_set(v___x_370_, 2, v_v_105_);
lean_ctor_set(v___x_370_, 1, v_k_104_);
lean_ctor_set(v___x_370_, 0, v___x_253_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_l_337_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_l_337_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_r_366_);
lean_ctor_set(v___x_109_, 3, v___x_374_);
lean_ctor_set(v___x_109_, 2, v_v_368_);
lean_ctor_set(v___x_109_, 1, v_k_367_);
lean_ctor_set(v___x_109_, 0, v___x_372_);
v___x_376_ = v___x_109_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_r_366_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_unsigned_to_nat(2u);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_impl_252_);
lean_ctor_set(v___x_109_, 3, v_r_366_);
lean_ctor_set(v___x_109_, 0, v___x_383_);
v___x_385_ = v___x_109_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_r_366_);
lean_ctor_set(v_reuseFailAlloc_386_, 4, v_impl_252_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
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
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_k_100_);
lean_ctor_set(v___x_389_, 2, v_v_101_);
lean_ctor_set(v___x_389_, 3, v_t_102_);
lean_ctor_set(v___x_389_, 4, v_t_102_);
return v___x_389_;
}
}
}
static lean_object* _init_l_Lake_InputFile_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_390_ = lean_box(1);
v___x_391_ = l_Lake_InputFile_defaultFacetConfig;
v___x_392_ = l_Lake_InputFile_defaultFacet;
v___x_393_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v___x_392_, v___x_391_, v___x_390_);
return v___x_393_;
}
}
static lean_object* _init_l_Lake_InputFile_initFacetConfigs(void){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lean_obj_once(&l_Lake_InputFile_initFacetConfigs___closed__0, &l_Lake_InputFile_initFacetConfigs___closed__0_once, _init_l_Lake_InputFile_initFacetConfigs___closed__0);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0(lean_object* v_00_u03b2_395_, lean_object* v_k_396_, lean_object* v_v_397_, lean_object* v_t_398_, lean_object* v_hl_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_396_, v_v_397_, v_t_398_);
return v___x_400_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(lean_object* v_filter_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_filter_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_filter_403_ = lean_ctor_get(v_filter_401_, 0);
lean_inc_ref(v_filter_403_);
lean_dec_ref(v_filter_401_);
v___x_404_ = lean_apply_1(v_filter_403_, v___y_402_);
v___x_405_ = lean_unbox(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0___boxed(lean_object* v_filter_406_, lean_object* v___y_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(v_filter_406_, v___y_407_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
static lean_object* _init_l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0));
v___x_412_ = l_Lake_BuildTrace_nil(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(lean_object* v___x_413_, uint8_t v_text_414_, lean_object* v___f_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1, &l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1_once, _init_l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1);
v___x_424_ = l_Lake_inputDir(v___x_413_, v_text_414_, v___f_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___y_421_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___boxed(lean_object* v___x_426_, lean_object* v_text_427_, lean_object* v___f_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v_text_boxed_436_; lean_object* v_res_437_; 
v_text_boxed_436_ = lean_unbox(v_text_427_);
v_res_437_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(v___x_426_, v_text_boxed_436_, v___f_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(lean_object* v_t_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_pkg_446_; lean_object* v_config_447_; lean_object* v_name_448_; lean_object* v_dir_449_; lean_object* v_path_450_; uint8_t v_text_451_; lean_object* v_filter_452_; lean_object* v___x_453_; lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_pkg_446_ = lean_ctor_get(v_t_438_, 0);
lean_inc_ref(v_pkg_446_);
v_config_447_ = lean_ctor_get(v_t_438_, 2);
lean_inc(v_config_447_);
v_name_448_ = lean_ctor_get(v_t_438_, 1);
lean_inc(v_name_448_);
lean_dec_ref(v_t_438_);
v_dir_449_ = lean_ctor_get(v_pkg_446_, 4);
lean_inc_ref(v_dir_449_);
lean_dec_ref(v_pkg_446_);
v_path_450_ = lean_ctor_get(v_config_447_, 0);
lean_inc_ref(v_path_450_);
v_text_451_ = lean_ctor_get_uint8(v_config_447_, sizeof(void*)*2);
v_filter_452_ = lean_ctor_get(v_config_447_, 1);
lean_inc_ref(v_filter_452_);
lean_dec(v_config_447_);
v___x_453_ = lean_box(0);
v___f_454_ = lean_alloc_closure((void*)(l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0___boxed), 2, 1);
lean_closure_set(v___f_454_, 0, v_filter_452_);
v___x_455_ = l_Lake_joinRelative(v_dir_449_, v_path_450_);
v___x_456_ = lean_box(v_text_451_);
v___f_457_ = lean_alloc_closure((void*)(l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___boxed), 10, 3);
lean_closure_set(v___f_457_, 0, v___x_455_);
lean_closure_set(v___f_457_, 1, v___x_456_);
lean_closure_set(v___f_457_, 2, v___f_454_);
lean_inc_ref(v_a_443_);
v___x_458_ = l_Lake_ensureJob___redArg(v___x_453_, v___f_457_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_486_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_a_460_ = lean_ctor_get(v___x_458_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_486_ == 0)
{
v___x_462_ = v___x_458_;
v_isShared_463_ = v_isSharedCheck_486_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_486_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_task_464_; lean_object* v_kind_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_484_; 
v_task_464_ = lean_ctor_get(v_a_459_, 0);
v_kind_465_ = lean_ctor_get(v_a_459_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_459_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_a_459_, 2);
lean_dec(v_unused_485_);
v___x_467_ = v_a_459_;
v_isShared_468_ = v_isSharedCheck_484_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_kind_465_);
lean_inc(v_task_464_);
lean_dec(v_a_459_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_484_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_registeredJobs_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v_job_475_; 
v_registeredJobs_469_ = lean_ctor_get(v_a_443_, 3);
lean_inc(v_registeredJobs_469_);
lean_dec_ref(v_a_443_);
v___x_470_ = lean_st_ref_take(v_registeredJobs_469_);
v___x_471_ = 1;
v___x_472_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_448_, v___x_471_);
v___x_473_ = 0;
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 2, v___x_472_);
v_job_475_ = v___x_467_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_task_464_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_kind_465_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v___x_472_);
v_job_475_ = v_reuseFailAlloc_483_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_ctor_set_uint8(v_job_475_, sizeof(void*)*3, v___x_473_);
lean_inc_ref(v_job_475_);
v___x_476_ = l_Lake_Job_toOpaque___redArg(v_job_475_);
v___x_477_ = lean_array_push(v___x_470_, v___x_476_);
v___x_478_ = lean_st_ref_set(v_registeredJobs_469_, v___x_477_);
lean_dec(v_registeredJobs_469_);
v___x_479_ = l_Lake_Job_renew___redArg(v_job_475_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_479_);
v___x_481_ = v___x_462_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_a_460_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
else
{
lean_dec(v_name_448_);
lean_dec_ref(v_a_443_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___boxed(lean_object* v_t_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(v_t_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_496_, size_t v_i_497_, lean_object* v_bs_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_497_, v_sz_496_);
if (v___x_499_ == 0)
{
return v_bs_498_;
}
else
{
lean_object* v_v_500_; lean_object* v___x_501_; lean_object* v_bs_x27_502_; lean_object* v___x_503_; lean_object* v___x_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_v_500_ = lean_array_uget(v_bs_498_, v_i_497_);
v___x_501_ = lean_unsigned_to_nat(0u);
v_bs_x27_502_ = lean_array_uset(v_bs_498_, v_i_497_, v___x_501_);
v___x_503_ = l_Lake_mkRelPathString(v_v_500_);
v___x_504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_497_, v___x_505_);
v___x_507_ = lean_array_uset(v_bs_x27_502_, v_i_497_, v___x_504_);
v_i_497_ = v___x_506_;
v_bs_498_ = v___x_507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_509_, lean_object* v_i_510_, lean_object* v_bs_511_){
_start:
{
size_t v_sz_boxed_512_; size_t v_i_boxed_513_; lean_object* v_res_514_; 
v_sz_boxed_512_ = lean_unbox_usize(v_sz_509_);
lean_dec(v_sz_509_);
v_i_boxed_513_ = lean_unbox_usize(v_i_510_);
lean_dec(v_i_510_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_512_, v_i_boxed_513_, v_bs_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(lean_object* v_a_515_){
_start:
{
size_t v_sz_516_; size_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_sz_516_ = lean_array_size(v_a_515_);
v___x_517_ = ((size_t)0ULL);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(v_sz_516_, v___x_517_, v_a_515_);
v___x_519_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(lean_object* v_as_521_, size_t v_i_522_, size_t v_stop_523_, lean_object* v_b_524_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_eq(v_i_522_, v_stop_523_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; size_t v___x_530_; size_t v___x_531_; 
v___x_526_ = lean_array_uget_borrowed(v_as_521_, v_i_522_);
v___x_527_ = lean_string_append(v_b_524_, v___x_526_);
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0));
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_522_, v___x_530_);
v_i_522_ = v___x_531_;
v_b_524_ = v___x_529_;
goto _start;
}
else
{
return v_b_524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_533_, lean_object* v_i_534_, lean_object* v_stop_535_, lean_object* v_b_536_){
_start:
{
size_t v_i_boxed_537_; size_t v_stop_boxed_538_; lean_object* v_res_539_; 
v_i_boxed_537_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_stop_boxed_538_ = lean_unbox_usize(v_stop_535_);
lean_dec(v_stop_535_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_as_533_, v_i_boxed_537_, v_stop_boxed_538_, v_b_536_);
lean_dec_ref(v_as_533_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(uint8_t v_fmt_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___y_544_; 
if (v_fmt_541_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_551_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0));
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_array_get_size(v_a_542_);
v___x_554_ = lean_nat_dec_lt(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_dec_ref(v_a_542_);
v___y_544_ = v___x_551_;
goto v___jp_543_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_le(v___x_553_, v___x_553_);
if (v___x_555_ == 0)
{
if (v___x_554_ == 0)
{
lean_dec_ref(v_a_542_);
v___y_544_ = v___x_551_;
goto v___jp_543_;
}
else
{
size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((size_t)0ULL);
v___x_557_ = lean_usize_of_nat(v___x_553_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_a_542_, v___x_556_, v___x_557_, v___x_551_);
lean_dec_ref(v_a_542_);
v___y_544_ = v___x_558_;
goto v___jp_543_;
}
}
else
{
size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((size_t)0ULL);
v___x_560_ = lean_usize_of_nat(v___x_553_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_a_542_, v___x_559_, v___x_560_, v___x_551_);
lean_dec_ref(v_a_542_);
v___y_544_ = v___x_561_;
goto v___jp_543_;
}
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = l_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(v_a_542_);
v___x_563_ = l_Lean_Json_compress(v___x_562_);
return v___x_563_;
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_string_utf8_byte_size(v___y_544_);
lean_inc_ref(v___y_544_);
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v___y_544_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
v___x_549_ = l_String_Slice_Pos_prevn(v___x_548_, v___x_547_, v___x_545_);
lean_dec_ref(v___x_548_);
v___x_550_ = lean_string_utf8_extract(v___y_544_, v___x_546_, v___x_549_);
lean_dec(v___x_549_);
lean_dec_ref(v___y_544_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___boxed(lean_object* v_fmt_564_, lean_object* v_a_565_){
_start:
{
uint8_t v_fmt_boxed_566_; lean_object* v_res_567_; 
v_fmt_boxed_566_ = lean_unbox(v_fmt_564_);
v_res_567_ = l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(v_fmt_boxed_566_, v_a_565_);
return v_res_567_;
}
}
static lean_object* _init_l_Lake_InputDir_defaultFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___f_570_ = ((lean_object*)(l_Lake_InputDir_defaultFacetConfig___closed__0));
v___x_571_ = 1;
v___x_572_ = lean_box(0);
v___x_573_ = ((lean_object*)(l_Lake_InputDir_defaultFacetConfig___closed__1));
v___x_574_ = l_Lake_InputDir_keyword;
v___x_575_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
lean_ctor_set(v___x_575_, 2, v___x_572_);
lean_ctor_set(v___x_575_, 3, v___f_570_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*4, v___x_571_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*4 + 1, v___x_571_);
return v___x_575_;
}
}
static lean_object* _init_l_Lake_InputDir_defaultFacetConfig(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Lake_InputDir_defaultFacetConfig___closed__2, &l_Lake_InputDir_defaultFacetConfig___closed__2_once, _init_l_Lake_InputDir_defaultFacetConfig___closed__2);
return v___x_576_;
}
}
static lean_object* _init_l_Lake_InputDir_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_box(1);
v___x_578_ = l_Lake_InputDir_defaultFacetConfig;
v___x_579_ = l_Lake_InputDir_defaultFacet;
v___x_580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v___x_579_, v___x_578_, v___x_577_);
return v___x_580_;
}
}
static lean_object* _init_l_Lake_InputDir_initFacetConfigs(void){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lake_InputDir_initFacetConfigs___closed__0, &l_Lake_InputDir_initFacetConfigs___closed__0_once, _init_l_Lake_InputDir_initFacetConfigs___closed__0);
return v___x_581_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_InputFile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_InputFile_defaultFacetConfig = _init_l_Lake_InputFile_defaultFacetConfig();
lean_mark_persistent(l_Lake_InputFile_defaultFacetConfig);
l_Lake_InputFile_initFacetConfigs = _init_l_Lake_InputFile_initFacetConfigs();
lean_mark_persistent(l_Lake_InputFile_initFacetConfigs);
l_Lake_InputDir_defaultFacetConfig = _init_l_Lake_InputDir_defaultFacetConfig();
lean_mark_persistent(l_Lake_InputDir_defaultFacetConfig);
l_Lake_InputDir_initFacetConfigs = _init_l_Lake_InputDir_initFacetConfigs();
lean_mark_persistent(l_Lake_InputDir_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_InputFile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Job(uint8_t builtin);
lean_object* initialize_Lake_Build_Common(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_InputFile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_InputFile(builtin);
}
#ifdef __cplusplus
}
#endif
