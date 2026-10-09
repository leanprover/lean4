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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(lean_object*);
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
lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(uint8_t v_text_1_, lean_object* v___x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
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
LEAN_EXPORT void l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_text_1_ = stack[0].m_num;
lean_object* v___x_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_15_;
v_res_15_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(v_text_1_, v___x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0___boxed(lean_object* v_text_16_, lean_object* v___x_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
uint8_t v_text_boxed_25_; lean_object* v_res_26_; 
v_text_boxed_25_ = lean_unbox(v_text_16_);
v_res_26_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(v_text_boxed_25_, v___x_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec(v___y_20_);
lean_dec(v___y_19_);
return v_res_26_;
}
}
lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(lean_object* v_t_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_pkg_35_; lean_object* v_config_36_; lean_object* v_name_37_; lean_object* v_dir_38_; lean_object* v_path_39_; uint8_t v_text_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___f_46_; uint8_t v___x_47_; lean_object* v___x_48_; 
v_pkg_35_ = lean_ctor_get(v_t_27_, 0);
lean_inc_ref(v_pkg_35_);
v_config_36_ = lean_ctor_get(v_t_27_, 2);
lean_inc(v_config_36_);
v_name_37_ = lean_ctor_get(v_t_27_, 1);
lean_inc(v_name_37_);
lean_dec_ref(v_t_27_);
v_dir_38_ = lean_ctor_get(v_pkg_35_, 4);
lean_inc_ref(v_dir_38_);
lean_dec_ref(v_pkg_35_);
v_path_39_ = lean_ctor_get(v_config_36_, 0);
lean_inc_ref(v_path_39_);
v_text_40_ = lean_ctor_get_uint8(v_config_36_, sizeof(void*)*1);
lean_dec(v_config_36_);
v___x_41_ = l_Lake_instDataKindFilePath;
v___x_42_ = 1;
v___x_43_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_37_, v___x_42_);
v___x_44_ = l_Lake_joinRelative(v_dir_38_, v_path_39_);
v___x_45_ = lean_box(v_text_40_);
v___f_46_ = lean_alloc_closure((void*)(l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0___boxed), 9, 2);
lean_closure_set(v___f_46_, 0, v___x_45_);
lean_closure_set(v___f_46_, 1, v___x_44_);
v___x_47_ = 0;
v___x_48_ = l_Lake_ensureJob___redArg(v___x_41_, v___f_46_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_73_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
v_a_50_ = lean_ctor_get(v___x_48_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_73_ == 0)
{
v___x_52_ = v___x_48_;
v_isShared_53_ = v_isSharedCheck_73_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_inc(v_a_49_);
lean_dec(v___x_48_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_73_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_task_54_; lean_object* v_kind_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_71_; 
v_task_54_ = lean_ctor_get(v_a_49_, 0);
v_kind_55_ = lean_ctor_get(v_a_49_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_a_49_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v_a_49_, 2);
lean_dec(v_unused_72_);
v___x_57_ = v_a_49_;
v_isShared_58_ = v_isSharedCheck_71_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_kind_55_);
lean_inc(v_task_54_);
lean_dec(v_a_49_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_71_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_registeredJobs_59_; lean_object* v_job_61_; 
v_registeredJobs_59_ = lean_ctor_get(v_a_32_, 4);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 2, v___x_43_);
v_job_61_ = v___x_57_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_task_54_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_kind_55_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v___x_43_);
v_job_61_ = v_reuseFailAlloc_70_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
lean_ctor_set_uint8(v_job_61_, sizeof(void*)*3, v___x_47_);
v___x_62_ = lean_st_ref_take(v_registeredJobs_59_);
lean_inc_ref(v_job_61_);
v___x_63_ = l_Lake_Job_toOpaque___redArg(v_job_61_);
v___x_64_ = lean_array_push(v___x_62_, v___x_63_);
v___x_65_ = lean_st_ref_put(v_registeredJobs_59_, v___x_64_);
v___x_66_ = l_Lake_Job_renew___redArg(v_job_61_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_66_);
v___x_68_ = v___x_52_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_a_50_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_43_);
return v___x_48_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_27_ = stack[0].m_obj;
lean_object* v_a_28_ = stack[1].m_obj;
lean_object* v_a_29_ = stack[2].m_obj;
lean_object* v_a_30_ = stack[3].m_obj;
lean_object* v_a_31_ = stack[4].m_obj;
lean_object* v_a_32_ = stack[5].m_obj;
lean_object* v_a_33_ = stack[6].m_obj;
lean_object* v_res_74_;
v_res_74_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(v_t_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___boxed(lean_object* v_t_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(v_t_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec(v_a_78_);
lean_dec(v_a_77_);
return v_res_83_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(uint8_t v_fmt_84_, lean_object* v_a_85_){
_start:
{
if (v_fmt_84_ == 0)
{
return v_a_85_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = l_Lake_mkRelPathString(v_a_85_);
v___x_87_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
v___x_88_ = l_Lean_Json_compress(v___x_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_84_ = stack[0].m_num;
lean_object* v_a_85_ = stack[1].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(v_fmt_84_, v_a_85_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0___boxed(lean_object* v_fmt_90_, lean_object* v_a_91_){
_start:
{
uint8_t v_fmt_boxed_92_; lean_object* v_res_93_; 
v_fmt_boxed_92_ = lean_unbox(v_fmt_90_);
v_res_93_ = l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(v_fmt_boxed_92_, v_a_91_);
return v_res_93_;
}
}
static lean_object* _init_l_Lake_InputFile_defaultFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___f_96_ = ((lean_object*)(l_Lake_InputFile_defaultFacetConfig___closed__0));
v___x_97_ = 1;
v___x_98_ = l_Lake_instDataKindFilePath;
v___x_99_ = ((lean_object*)(l_Lake_InputFile_defaultFacetConfig___closed__1));
v___x_100_ = l_Lake_InputFile_keyword;
v___x_101_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
lean_ctor_set(v___x_101_, 3, v___f_96_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*4, v___x_97_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*4 + 1, v___x_97_);
return v___x_101_;
}
}
static lean_object* _init_l_Lake_InputFile_defaultFacetConfig(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lake_InputFile_defaultFacetConfig___closed__2, &l_Lake_InputFile_defaultFacetConfig___closed__2_once, _init_l_Lake_InputFile_defaultFacetConfig___closed__2);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(lean_object* v_k_103_, lean_object* v_v_104_, lean_object* v_t_105_){
_start:
{
if (lean_obj_tag(v_t_105_) == 0)
{
lean_object* v_size_106_; lean_object* v_k_107_; lean_object* v_v_108_; lean_object* v_l_109_; lean_object* v_r_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_390_; 
v_size_106_ = lean_ctor_get(v_t_105_, 0);
v_k_107_ = lean_ctor_get(v_t_105_, 1);
v_v_108_ = lean_ctor_get(v_t_105_, 2);
v_l_109_ = lean_ctor_get(v_t_105_, 3);
v_r_110_ = lean_ctor_get(v_t_105_, 4);
v_isSharedCheck_390_ = !lean_is_exclusive(v_t_105_);
if (v_isSharedCheck_390_ == 0)
{
v___x_112_ = v_t_105_;
v_isShared_113_ = v_isSharedCheck_390_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_r_110_);
lean_inc(v_l_109_);
lean_inc(v_v_108_);
lean_inc(v_k_107_);
lean_inc(v_size_106_);
lean_dec(v_t_105_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_390_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v___x_114_; 
v___x_114_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_103_, v_k_107_);
switch(v___x_114_)
{
case 0:
{
lean_object* v_impl_115_; lean_object* v___x_116_; 
lean_dec(v_size_106_);
v_impl_115_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_103_, v_v_104_, v_l_109_);
v___x_116_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_110_) == 0)
{
lean_object* v_size_117_; lean_object* v_size_118_; lean_object* v_k_119_; lean_object* v_v_120_; lean_object* v_l_121_; lean_object* v_r_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_size_117_ = lean_ctor_get(v_r_110_, 0);
v_size_118_ = lean_ctor_get(v_impl_115_, 0);
v_k_119_ = lean_ctor_get(v_impl_115_, 1);
v_v_120_ = lean_ctor_get(v_impl_115_, 2);
v_l_121_ = lean_ctor_get(v_impl_115_, 3);
v_r_122_ = lean_ctor_get(v_impl_115_, 4);
lean_inc(v_r_122_);
v___x_123_ = lean_unsigned_to_nat(3u);
v___x_124_ = lean_nat_mul(v___x_123_, v_size_117_);
v___x_125_ = lean_nat_dec_lt(v___x_124_, v_size_118_);
lean_dec(v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
lean_dec(v_r_122_);
v___x_126_ = lean_nat_add(v___x_116_, v_size_118_);
v___x_127_ = lean_nat_add(v___x_126_, v_size_117_);
lean_dec(v___x_126_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 3, v_impl_115_);
lean_ctor_set(v___x_112_, 0, v___x_127_);
v___x_129_ = v___x_112_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v_impl_115_);
lean_ctor_set(v_reuseFailAlloc_130_, 4, v_r_110_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_196_; 
lean_inc(v_l_121_);
lean_inc(v_v_120_);
lean_inc(v_k_119_);
lean_inc(v_size_118_);
v_isSharedCheck_196_ = !lean_is_exclusive(v_impl_115_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; lean_object* v_unused_198_; lean_object* v_unused_199_; lean_object* v_unused_200_; lean_object* v_unused_201_; 
v_unused_197_ = lean_ctor_get(v_impl_115_, 4);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_impl_115_, 3);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_impl_115_, 2);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_impl_115_, 1);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_impl_115_, 0);
lean_dec(v_unused_201_);
v___x_132_ = v_impl_115_;
v_isShared_133_ = v_isSharedCheck_196_;
goto v_resetjp_131_;
}
else
{
lean_dec(v_impl_115_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_196_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_size_134_; lean_object* v_size_135_; lean_object* v_k_136_; lean_object* v_v_137_; lean_object* v_l_138_; lean_object* v_r_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_size_134_ = lean_ctor_get(v_l_121_, 0);
v_size_135_ = lean_ctor_get(v_r_122_, 0);
v_k_136_ = lean_ctor_get(v_r_122_, 1);
v_v_137_ = lean_ctor_get(v_r_122_, 2);
v_l_138_ = lean_ctor_get(v_r_122_, 3);
v_r_139_ = lean_ctor_get(v_r_122_, 4);
v___x_140_ = lean_unsigned_to_nat(2u);
v___x_141_ = lean_nat_mul(v___x_140_, v_size_134_);
v___x_142_ = lean_nat_dec_lt(v_size_135_, v___x_141_);
lean_dec(v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_171_; 
lean_inc(v_r_139_);
lean_inc(v_l_138_);
lean_inc(v_v_137_);
lean_inc(v_k_136_);
v_isSharedCheck_171_ = !lean_is_exclusive(v_r_122_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; 
v_unused_172_ = lean_ctor_get(v_r_122_, 4);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_r_122_, 3);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_r_122_, 2);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_r_122_, 1);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_r_122_, 0);
lean_dec(v_unused_176_);
v___x_144_ = v_r_122_;
v_isShared_145_ = v_isSharedCheck_171_;
goto v_resetjp_143_;
}
else
{
lean_dec(v_r_122_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_171_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___x_159_; lean_object* v___y_161_; 
v___x_146_ = lean_nat_add(v___x_116_, v_size_118_);
lean_dec(v_size_118_);
v___x_147_ = lean_nat_add(v___x_146_, v_size_117_);
lean_dec(v___x_146_);
v___x_159_ = lean_nat_add(v___x_116_, v_size_134_);
if (lean_obj_tag(v_l_138_) == 0)
{
lean_object* v_size_169_; 
v_size_169_ = lean_ctor_get(v_l_138_, 0);
lean_inc(v_size_169_);
v___y_161_ = v_size_169_;
goto v___jp_160_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___y_161_ = v___x_170_;
goto v___jp_160_;
}
v___jp_148_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_nat_add(v___y_149_, v___y_151_);
lean_dec(v___y_151_);
lean_dec(v___y_149_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 4, v_r_110_);
lean_ctor_set(v___x_144_, 3, v_r_139_);
lean_ctor_set(v___x_144_, 2, v_v_108_);
lean_ctor_set(v___x_144_, 1, v_k_107_);
lean_ctor_set(v___x_144_, 0, v___x_152_);
v___x_154_ = v___x_144_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_r_139_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v_r_110_);
v___x_154_ = v_reuseFailAlloc_158_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_156_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_154_);
lean_ctor_set(v___x_132_, 3, v___y_150_);
lean_ctor_set(v___x_132_, 2, v_v_137_);
lean_ctor_set(v___x_132_, 1, v_k_136_);
lean_ctor_set(v___x_132_, 0, v___x_147_);
v___x_156_ = v___x_132_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_k_136_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_v_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v___y_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_nat_add(v___x_159_, v___y_161_);
lean_dec(v___y_161_);
lean_dec(v___x_159_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_l_138_);
lean_ctor_set(v___x_112_, 3, v_l_121_);
lean_ctor_set(v___x_112_, 2, v_v_120_);
lean_ctor_set(v___x_112_, 1, v_k_119_);
lean_ctor_set(v___x_112_, 0, v___x_162_);
v___x_164_ = v___x_112_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_119_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_v_120_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_l_121_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_l_138_);
v___x_164_ = v_reuseFailAlloc_168_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; 
v___x_165_ = lean_nat_add(v___x_116_, v_size_117_);
if (lean_obj_tag(v_r_139_) == 0)
{
lean_object* v_size_166_; 
v_size_166_ = lean_ctor_get(v_r_139_, 0);
lean_inc(v_size_166_);
v___y_149_ = v___x_165_;
v___y_150_ = v___x_164_;
v___y_151_ = v_size_166_;
goto v___jp_148_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_unsigned_to_nat(0u);
v___y_149_ = v___x_165_;
v___y_150_ = v___x_164_;
v___y_151_ = v___x_167_;
goto v___jp_148_;
}
}
}
}
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
lean_del_object(v___x_112_);
v___x_177_ = lean_nat_add(v___x_116_, v_size_118_);
lean_dec(v_size_118_);
v___x_178_ = lean_nat_add(v___x_177_, v_size_117_);
lean_dec(v___x_177_);
v___x_179_ = lean_nat_add(v___x_116_, v_size_117_);
v___x_180_ = lean_nat_add(v___x_179_, v_size_135_);
lean_dec(v___x_179_);
lean_inc_ref(v_r_110_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_r_110_);
lean_ctor_set(v___x_132_, 3, v_r_122_);
lean_ctor_set(v___x_132_, 2, v_v_108_);
lean_ctor_set(v___x_132_, 1, v_k_107_);
lean_ctor_set(v___x_132_, 0, v___x_180_);
v___x_182_ = v___x_132_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_r_122_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_r_110_);
v___x_182_ = v_reuseFailAlloc_195_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_isSharedCheck_189_ = !lean_is_exclusive(v_r_110_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; 
v_unused_190_ = lean_ctor_get(v_r_110_, 4);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_r_110_, 3);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_r_110_, 2);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_r_110_, 1);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_r_110_, 0);
lean_dec(v_unused_194_);
v___x_184_ = v_r_110_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_r_110_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 4, v___x_182_);
lean_ctor_set(v___x_184_, 3, v_l_121_);
lean_ctor_set(v___x_184_, 2, v_v_120_);
lean_ctor_set(v___x_184_, 1, v_k_119_);
lean_ctor_set(v___x_184_, 0, v___x_178_);
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_k_119_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_v_120_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_l_121_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v___x_182_);
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
}
else
{
lean_object* v_l_202_; 
v_l_202_ = lean_ctor_get(v_impl_115_, 3);
if (lean_obj_tag(v_l_202_) == 0)
{
lean_object* v_r_203_; lean_object* v_k_204_; lean_object* v_v_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_216_; 
lean_inc_ref(v_l_202_);
v_r_203_ = lean_ctor_get(v_impl_115_, 4);
v_k_204_ = lean_ctor_get(v_impl_115_, 1);
v_v_205_ = lean_ctor_get(v_impl_115_, 2);
v_isSharedCheck_216_ = !lean_is_exclusive(v_impl_115_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_217_ = lean_ctor_get(v_impl_115_, 3);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_impl_115_, 0);
lean_dec(v_unused_218_);
v___x_207_ = v_impl_115_;
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_r_203_);
lean_inc(v_v_205_);
lean_inc(v_k_204_);
lean_dec(v_impl_115_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_203_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 3, v_r_203_);
lean_ctor_set(v___x_207_, 2, v_v_108_);
lean_ctor_set(v___x_207_, 1, v_k_107_);
lean_ctor_set(v___x_207_, 0, v___x_116_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_r_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_r_203_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_211_);
lean_ctor_set(v___x_112_, 3, v_l_202_);
lean_ctor_set(v___x_112_, 2, v_v_205_);
lean_ctor_set(v___x_112_, 1, v_k_204_);
lean_ctor_set(v___x_112_, 0, v___x_209_);
v___x_213_ = v___x_112_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_205_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_l_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_object* v_r_219_; 
v_r_219_ = lean_ctor_get(v_impl_115_, 4);
lean_inc(v_r_219_);
if (lean_obj_tag(v_r_219_) == 0)
{
lean_object* v_k_220_; lean_object* v_v_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_244_; 
lean_inc(v_l_202_);
v_k_220_ = lean_ctor_get(v_impl_115_, 1);
v_v_221_ = lean_ctor_get(v_impl_115_, 2);
v_isSharedCheck_244_ = !lean_is_exclusive(v_impl_115_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; lean_object* v_unused_246_; lean_object* v_unused_247_; 
v_unused_245_ = lean_ctor_get(v_impl_115_, 4);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_impl_115_, 3);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_impl_115_, 0);
lean_dec(v_unused_247_);
v___x_223_ = v_impl_115_;
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_v_221_);
lean_inc(v_k_220_);
lean_dec(v_impl_115_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_244_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_k_225_; lean_object* v_v_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_240_; 
v_k_225_ = lean_ctor_get(v_r_219_, 1);
v_v_226_ = lean_ctor_get(v_r_219_, 2);
v_isSharedCheck_240_ = !lean_is_exclusive(v_r_219_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; 
v_unused_241_ = lean_ctor_get(v_r_219_, 4);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_r_219_, 3);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_r_219_, 0);
lean_dec(v_unused_243_);
v___x_228_ = v_r_219_;
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_v_226_);
lean_inc(v_k_225_);
lean_dec(v_r_219_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(3u);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 4, v_l_202_);
lean_ctor_set(v___x_228_, 3, v_l_202_);
lean_ctor_set(v___x_228_, 2, v_v_221_);
lean_ctor_set(v___x_228_, 1, v_k_220_);
lean_ctor_set(v___x_228_, 0, v___x_116_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_220_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_221_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_l_202_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_l_202_);
v___x_232_ = v_reuseFailAlloc_239_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v_l_202_);
lean_ctor_set(v___x_223_, 2, v_v_108_);
lean_ctor_set(v___x_223_, 1, v_k_107_);
lean_ctor_set(v___x_223_, 0, v___x_116_);
v___x_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_l_202_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_l_202_);
v___x_234_ = v_reuseFailAlloc_238_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_234_);
lean_ctor_set(v___x_112_, 3, v___x_232_);
lean_ctor_set(v___x_112_, 2, v_v_226_);
lean_ctor_set(v___x_112_, 1, v_k_225_);
lean_ctor_set(v___x_112_, 0, v___x_230_);
v___x_236_ = v___x_112_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_k_225_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_v_226_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_unsigned_to_nat(2u);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_r_219_);
lean_ctor_set(v___x_112_, 3, v_impl_115_);
lean_ctor_set(v___x_112_, 0, v___x_248_);
v___x_250_ = v___x_112_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_impl_115_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v_r_219_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
case 1:
{
lean_object* v___x_253_; 
lean_dec(v_v_108_);
lean_dec(v_k_107_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 2, v_v_104_);
lean_ctor_set(v___x_112_, 1, v_k_103_);
v___x_253_ = v___x_112_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_size_106_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_103_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_104_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_r_110_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
default: 
{
lean_object* v_impl_255_; lean_object* v___x_256_; 
lean_dec(v_size_106_);
v_impl_255_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_103_, v_v_104_, v_r_110_);
v___x_256_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_109_) == 0)
{
lean_object* v_size_257_; lean_object* v_size_258_; lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v_l_261_; lean_object* v_r_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_size_257_ = lean_ctor_get(v_l_109_, 0);
v_size_258_ = lean_ctor_get(v_impl_255_, 0);
v_k_259_ = lean_ctor_get(v_impl_255_, 1);
v_v_260_ = lean_ctor_get(v_impl_255_, 2);
v_l_261_ = lean_ctor_get(v_impl_255_, 3);
lean_inc(v_l_261_);
v_r_262_ = lean_ctor_get(v_impl_255_, 4);
v___x_263_ = lean_unsigned_to_nat(3u);
v___x_264_ = lean_nat_mul(v___x_263_, v_size_257_);
v___x_265_ = lean_nat_dec_lt(v___x_264_, v_size_258_);
lean_dec(v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_l_261_);
v___x_266_ = lean_nat_add(v___x_256_, v_size_257_);
v___x_267_ = lean_nat_add(v___x_266_, v_size_258_);
lean_dec(v___x_266_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_impl_255_);
lean_ctor_set(v___x_112_, 0, v___x_267_);
v___x_269_ = v___x_112_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_impl_255_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
else
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_334_; 
lean_inc(v_r_262_);
lean_inc(v_v_260_);
lean_inc(v_k_259_);
lean_inc(v_size_258_);
v_isSharedCheck_334_ = !lean_is_exclusive(v_impl_255_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; lean_object* v_unused_336_; lean_object* v_unused_337_; lean_object* v_unused_338_; lean_object* v_unused_339_; 
v_unused_335_ = lean_ctor_get(v_impl_255_, 4);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_impl_255_, 3);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_impl_255_, 2);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_impl_255_, 1);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_impl_255_, 0);
lean_dec(v_unused_339_);
v___x_272_ = v_impl_255_;
v_isShared_273_ = v_isSharedCheck_334_;
goto v_resetjp_271_;
}
else
{
lean_dec(v_impl_255_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_334_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_size_274_; lean_object* v_k_275_; lean_object* v_v_276_; lean_object* v_l_277_; lean_object* v_r_278_; lean_object* v_size_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_size_274_ = lean_ctor_get(v_l_261_, 0);
v_k_275_ = lean_ctor_get(v_l_261_, 1);
v_v_276_ = lean_ctor_get(v_l_261_, 2);
v_l_277_ = lean_ctor_get(v_l_261_, 3);
v_r_278_ = lean_ctor_get(v_l_261_, 4);
v_size_279_ = lean_ctor_get(v_r_262_, 0);
v___x_280_ = lean_unsigned_to_nat(2u);
v___x_281_ = lean_nat_mul(v___x_280_, v_size_279_);
v___x_282_ = lean_nat_dec_lt(v_size_274_, v___x_281_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_310_; 
lean_inc(v_r_278_);
lean_inc(v_l_277_);
lean_inc(v_v_276_);
lean_inc(v_k_275_);
v_isSharedCheck_310_ = !lean_is_exclusive(v_l_261_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_311_ = lean_ctor_get(v_l_261_, 4);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_l_261_, 3);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_l_261_, 2);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_261_, 1);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_261_, 0);
lean_dec(v_unused_315_);
v___x_284_ = v_l_261_;
v_isShared_285_ = v_isSharedCheck_310_;
goto v_resetjp_283_;
}
else
{
lean_dec(v_l_261_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_310_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_300_; 
v___x_286_ = lean_nat_add(v___x_256_, v_size_257_);
v___x_287_ = lean_nat_add(v___x_286_, v_size_258_);
lean_dec(v_size_258_);
if (lean_obj_tag(v_l_277_) == 0)
{
lean_object* v_size_308_; 
v_size_308_ = lean_ctor_get(v_l_277_, 0);
lean_inc(v_size_308_);
v___y_300_ = v_size_308_;
goto v___jp_299_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___y_300_ = v___x_309_;
goto v___jp_299_;
}
v___jp_288_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_nat_add(v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec(v___y_290_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 4, v_r_262_);
lean_ctor_set(v___x_284_, 3, v_r_278_);
lean_ctor_set(v___x_284_, 2, v_v_260_);
lean_ctor_set(v___x_284_, 1, v_k_259_);
lean_ctor_set(v___x_284_, 0, v___x_292_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_259_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_260_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_r_278_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_r_262_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_296_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 4, v___x_294_);
lean_ctor_set(v___x_272_, 3, v___y_289_);
lean_ctor_set(v___x_272_, 2, v_v_276_);
lean_ctor_set(v___x_272_, 1, v_k_275_);
lean_ctor_set(v___x_272_, 0, v___x_287_);
v___x_296_ = v___x_272_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v___y_289_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_nat_add(v___x_286_, v___y_300_);
lean_dec(v___y_300_);
lean_dec(v___x_286_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_l_277_);
lean_ctor_set(v___x_112_, 0, v___x_301_);
v___x_303_ = v___x_112_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_l_277_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; 
v___x_304_ = lean_nat_add(v___x_256_, v_size_279_);
if (lean_obj_tag(v_r_278_) == 0)
{
lean_object* v_size_305_; 
v_size_305_ = lean_ctor_get(v_r_278_, 0);
lean_inc(v_size_305_);
v___y_289_ = v___x_303_;
v___y_290_ = v___x_304_;
v___y_291_ = v_size_305_;
goto v___jp_288_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___y_289_ = v___x_303_;
v___y_290_ = v___x_304_;
v___y_291_ = v___x_306_;
goto v___jp_288_;
}
}
}
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_del_object(v___x_112_);
v___x_316_ = lean_nat_add(v___x_256_, v_size_257_);
v___x_317_ = lean_nat_add(v___x_316_, v_size_258_);
lean_dec(v_size_258_);
v___x_318_ = lean_nat_add(v___x_316_, v_size_274_);
lean_dec(v___x_316_);
lean_inc_ref(v_l_109_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 4, v_l_261_);
lean_ctor_set(v___x_272_, 3, v_l_109_);
lean_ctor_set(v___x_272_, 2, v_v_108_);
lean_ctor_set(v___x_272_, 1, v_k_107_);
lean_ctor_set(v___x_272_, 0, v___x_318_);
v___x_320_ = v___x_272_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_l_261_);
v___x_320_ = v_reuseFailAlloc_333_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_isSharedCheck_327_ = !lean_is_exclusive(v_l_109_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_328_ = lean_ctor_get(v_l_109_, 4);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_l_109_, 3);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_109_, 2);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_l_109_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_l_109_, 0);
lean_dec(v_unused_332_);
v___x_322_ = v_l_109_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_dec(v_l_109_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 4, v_r_262_);
lean_ctor_set(v___x_322_, 3, v___x_320_);
lean_ctor_set(v___x_322_, 2, v_v_260_);
lean_ctor_set(v___x_322_, 1, v_k_259_);
lean_ctor_set(v___x_322_, 0, v___x_317_);
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_k_259_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_v_260_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_r_262_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_340_; 
v_l_340_ = lean_ctor_get(v_impl_255_, 3);
lean_inc(v_l_340_);
if (lean_obj_tag(v_l_340_) == 0)
{
lean_object* v_r_341_; lean_object* v_k_342_; lean_object* v_v_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_366_; 
v_r_341_ = lean_ctor_get(v_impl_255_, 4);
v_k_342_ = lean_ctor_get(v_impl_255_, 1);
v_v_343_ = lean_ctor_get(v_impl_255_, 2);
v_isSharedCheck_366_ = !lean_is_exclusive(v_impl_255_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; 
v_unused_367_ = lean_ctor_get(v_impl_255_, 3);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_impl_255_, 0);
lean_dec(v_unused_368_);
v___x_345_ = v_impl_255_;
v_isShared_346_ = v_isSharedCheck_366_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_r_341_);
lean_inc(v_v_343_);
lean_inc(v_k_342_);
lean_dec(v_impl_255_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_366_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_k_347_; lean_object* v_v_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_362_; 
v_k_347_ = lean_ctor_get(v_l_340_, 1);
v_v_348_ = lean_ctor_get(v_l_340_, 2);
v_isSharedCheck_362_ = !lean_is_exclusive(v_l_340_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; lean_object* v_unused_364_; lean_object* v_unused_365_; 
v_unused_363_ = lean_ctor_get(v_l_340_, 4);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_l_340_, 3);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_l_340_, 0);
lean_dec(v_unused_365_);
v___x_350_ = v_l_340_;
v_isShared_351_ = v_isSharedCheck_362_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_v_348_);
lean_inc(v_k_347_);
lean_dec(v_l_340_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_362_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_341_, 2);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 4, v_r_341_);
lean_ctor_set(v___x_350_, 3, v_r_341_);
lean_ctor_set(v___x_350_, 2, v_v_108_);
lean_ctor_set(v___x_350_, 1, v_k_107_);
lean_ctor_set(v___x_350_, 0, v___x_256_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_r_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_r_341_);
v___x_354_ = v_reuseFailAlloc_361_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
lean_inc(v_r_341_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 3, v_r_341_);
lean_ctor_set(v___x_345_, 0, v___x_256_);
v___x_356_ = v___x_345_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_342_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_343_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_r_341_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_r_341_);
v___x_356_ = v_reuseFailAlloc_360_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_358_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_356_);
lean_ctor_set(v___x_112_, 3, v___x_354_);
lean_ctor_set(v___x_112_, 2, v_v_348_);
lean_ctor_set(v___x_112_, 1, v_k_347_);
lean_ctor_set(v___x_112_, 0, v___x_352_);
v___x_358_ = v___x_112_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_k_347_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_v_348_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
else
{
lean_object* v_r_369_; 
v_r_369_ = lean_ctor_get(v_impl_255_, 4);
lean_inc(v_r_369_);
if (lean_obj_tag(v_r_369_) == 0)
{
lean_object* v_k_370_; lean_object* v_v_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_382_; 
v_k_370_ = lean_ctor_get(v_impl_255_, 1);
v_v_371_ = lean_ctor_get(v_impl_255_, 2);
v_isSharedCheck_382_ = !lean_is_exclusive(v_impl_255_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_383_ = lean_ctor_get(v_impl_255_, 4);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_impl_255_, 3);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_impl_255_, 0);
lean_dec(v_unused_385_);
v___x_373_ = v_impl_255_;
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_v_371_);
lean_inc(v_k_370_);
lean_dec(v_impl_255_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(3u);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 4, v_l_340_);
lean_ctor_set(v___x_373_, 2, v_v_108_);
lean_ctor_set(v___x_373_, 1, v_k_107_);
lean_ctor_set(v___x_373_, 0, v___x_256_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_l_340_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_l_340_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_r_369_);
lean_ctor_set(v___x_112_, 3, v___x_377_);
lean_ctor_set(v___x_112_, 2, v_v_371_);
lean_ctor_set(v___x_112_, 1, v_k_370_);
lean_ctor_set(v___x_112_, 0, v___x_375_);
v___x_379_ = v___x_112_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_k_370_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_v_371_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_380_, 4, v_r_369_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_unsigned_to_nat(2u);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_impl_255_);
lean_ctor_set(v___x_112_, 3, v_r_369_);
lean_ctor_set(v___x_112_, 0, v___x_386_);
v___x_388_ = v___x_112_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_r_369_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v_impl_255_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
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
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_k_103_);
lean_ctor_set(v___x_392_, 2, v_v_104_);
lean_ctor_set(v___x_392_, 3, v_t_105_);
lean_ctor_set(v___x_392_, 4, v_t_105_);
return v___x_392_;
}
}
}
static lean_object* _init_l_Lake_InputFile_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_box(1);
v___x_394_ = l_Lake_InputFile_defaultFacetConfig;
v___x_395_ = l_Lake_InputFile_defaultFacet;
v___x_396_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v___x_395_, v___x_394_, v___x_393_);
return v___x_396_;
}
}
static lean_object* _init_l_Lake_InputFile_initFacetConfigs(void){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = lean_obj_once(&l_Lake_InputFile_initFacetConfigs___closed__0, &l_Lake_InputFile_initFacetConfigs___closed__0_once, _init_l_Lake_InputFile_initFacetConfigs___closed__0);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0(lean_object* v_00_u03b2_398_, lean_object* v_k_399_, lean_object* v_v_400_, lean_object* v_t_401_, lean_object* v_hl_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_399_, v_v_400_, v_t_401_);
return v___x_403_;
}
}
uint8_t l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(lean_object* v_filter_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_filter_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_filter_406_ = lean_ctor_get(v_filter_404_, 0);
lean_inc_ref(v_filter_406_);
lean_dec_ref(v_filter_404_);
v___x_407_ = lean_apply_1(v_filter_406_, v___y_405_);
v___x_408_ = lean_unbox(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT void l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_404_ = stack[0].m_obj;
lean_object* v___y_405_ = stack[1].m_obj;
uint8_t v_res_409_;
v_res_409_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(v_filter_404_, v___y_405_);
stack->m_num = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0___boxed(lean_object* v_filter_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(v_filter_410_, v___y_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
static lean_object* _init_l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0));
v___x_416_ = l_Lake_BuildTrace_nil(v___x_415_);
return v___x_416_;
}
}
lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(lean_object* v___x_417_, uint8_t v_text_418_, lean_object* v___f_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1, &l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1_once, _init_l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1);
v___x_428_ = l_Lake_inputDir(v___x_417_, v_text_418_, v___f_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___y_425_);
return v___x_429_;
}
}
LEAN_EXPORT void l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_417_ = stack[0].m_obj;
uint8_t v_text_418_ = stack[1].m_num;
lean_object* v___f_419_ = stack[2].m_obj;
lean_object* v___y_420_ = stack[3].m_obj;
lean_object* v___y_421_ = stack[4].m_obj;
lean_object* v___y_422_ = stack[5].m_obj;
lean_object* v___y_423_ = stack[6].m_obj;
lean_object* v___y_424_ = stack[7].m_obj;
lean_object* v___y_425_ = stack[8].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(v___x_417_, v_text_418_, v___f_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___boxed(lean_object* v___x_431_, lean_object* v_text_432_, lean_object* v___f_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_text_boxed_441_; lean_object* v_res_442_; 
v_text_boxed_441_ = lean_unbox(v_text_432_);
v_res_442_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(v___x_431_, v_text_boxed_441_, v___f_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec(v___y_436_);
lean_dec(v___y_435_);
return v_res_442_;
}
}
lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(lean_object* v_t_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_pkg_451_; lean_object* v_config_452_; lean_object* v_name_453_; lean_object* v_dir_454_; lean_object* v_path_455_; uint8_t v_text_456_; lean_object* v_filter_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___f_464_; uint8_t v___x_465_; lean_object* v___x_466_; 
v_pkg_451_ = lean_ctor_get(v_t_443_, 0);
lean_inc_ref(v_pkg_451_);
v_config_452_ = lean_ctor_get(v_t_443_, 2);
lean_inc(v_config_452_);
v_name_453_ = lean_ctor_get(v_t_443_, 1);
lean_inc(v_name_453_);
lean_dec_ref(v_t_443_);
v_dir_454_ = lean_ctor_get(v_pkg_451_, 4);
lean_inc_ref(v_dir_454_);
lean_dec_ref(v_pkg_451_);
v_path_455_ = lean_ctor_get(v_config_452_, 0);
lean_inc_ref(v_path_455_);
v_text_456_ = lean_ctor_get_uint8(v_config_452_, sizeof(void*)*2);
v_filter_457_ = lean_ctor_get(v_config_452_, 1);
lean_inc_ref(v_filter_457_);
lean_dec(v_config_452_);
v___x_458_ = lean_box(0);
v___x_459_ = 1;
v___x_460_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_453_, v___x_459_);
v___f_461_ = lean_alloc_closure((void*)(l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0___boxed), 2, 1);
lean_closure_set(v___f_461_, 0, v_filter_457_);
v___x_462_ = l_Lake_joinRelative(v_dir_454_, v_path_455_);
v___x_463_ = lean_box(v_text_456_);
v___f_464_ = lean_alloc_closure((void*)(l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___boxed), 10, 3);
lean_closure_set(v___f_464_, 0, v___x_462_);
lean_closure_set(v___f_464_, 1, v___x_463_);
lean_closure_set(v___f_464_, 2, v___f_461_);
v___x_465_ = 0;
v___x_466_ = l_Lake_ensureJob___redArg(v___x_458_, v___f_464_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_491_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_a_468_ = lean_ctor_get(v___x_466_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_491_ == 0)
{
v___x_470_ = v___x_466_;
v_isShared_471_ = v_isSharedCheck_491_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_491_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_task_472_; lean_object* v_kind_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_489_; 
v_task_472_ = lean_ctor_get(v_a_467_, 0);
v_kind_473_ = lean_ctor_get(v_a_467_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_a_467_, 2);
lean_dec(v_unused_490_);
v___x_475_ = v_a_467_;
v_isShared_476_ = v_isSharedCheck_489_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_kind_473_);
lean_inc(v_task_472_);
lean_dec(v_a_467_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_489_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_registeredJobs_477_; lean_object* v_job_479_; 
v_registeredJobs_477_ = lean_ctor_get(v_a_448_, 4);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 2, v___x_460_);
v_job_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_task_472_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_kind_473_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v___x_460_);
v_job_479_ = v_reuseFailAlloc_488_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
lean_ctor_set_uint8(v_job_479_, sizeof(void*)*3, v___x_465_);
v___x_480_ = lean_st_ref_take(v_registeredJobs_477_);
lean_inc_ref(v_job_479_);
v___x_481_ = l_Lake_Job_toOpaque___redArg(v_job_479_);
v___x_482_ = lean_array_push(v___x_480_, v___x_481_);
v___x_483_ = lean_st_ref_put(v_registeredJobs_477_, v___x_482_);
v___x_484_ = l_Lake_Job_renew___redArg(v_job_479_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_484_);
v___x_486_ = v___x_470_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_a_468_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_460_);
return v___x_466_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_443_ = stack[0].m_obj;
lean_object* v_a_444_ = stack[1].m_obj;
lean_object* v_a_445_ = stack[2].m_obj;
lean_object* v_a_446_ = stack[3].m_obj;
lean_object* v_a_447_ = stack[4].m_obj;
lean_object* v_a_448_ = stack[5].m_obj;
lean_object* v_a_449_ = stack[6].m_obj;
lean_object* v_res_492_;
v_res_492_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(v_t_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___boxed(lean_object* v_t_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(v_t_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec(v_a_496_);
lean_dec(v_a_495_);
return v_res_501_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_502_, size_t v_i_503_, lean_object* v_bs_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_505_ == 0)
{
return v_bs_504_;
}
else
{
lean_object* v_v_506_; lean_object* v___x_507_; lean_object* v_bs_x27_508_; lean_object* v___x_509_; lean_object* v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_v_506_ = lean_array_uget(v_bs_504_, v_i_503_);
v___x_507_ = lean_unsigned_to_nat(0u);
v_bs_x27_508_ = lean_array_uset(v_bs_504_, v_i_503_, v___x_507_);
v___x_509_ = l_Lake_mkRelPathString(v_v_506_);
v___x_510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_503_, v___x_511_);
v___x_513_ = lean_array_uset(v_bs_x27_508_, v_i_503_, v___x_510_);
v_i_503_ = v___x_512_;
v_bs_504_ = v___x_513_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_502_ = stack[0].m_num;
size_t v_i_503_ = stack[1].m_num;
lean_object* v_bs_504_ = stack[2].m_obj;
lean_object* v_res_515_;
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(v_sz_502_, v_i_503_, v_bs_504_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_bs_518_){
_start:
{
size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_sz_boxed_519_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_519_, v_i_boxed_520_, v_bs_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(lean_object* v_a_522_){
_start:
{
size_t v_sz_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_sz_523_ = lean_array_size(v_a_522_);
v___x_524_ = ((size_t)0ULL);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(v_sz_523_, v___x_524_, v_a_522_);
v___x_526_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(lean_object* v_as_528_, size_t v_i_529_, size_t v_stop_530_, lean_object* v_b_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = lean_usize_dec_eq(v_i_529_, v_stop_530_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; size_t v___x_537_; size_t v___x_538_; 
v___x_533_ = lean_array_uget_borrowed(v_as_528_, v_i_529_);
v___x_534_ = lean_string_append(v_b_531_, v___x_533_);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0));
v___x_536_ = lean_string_append(v___x_534_, v___x_535_);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_529_, v___x_537_);
v_i_529_ = v___x_538_;
v_b_531_ = v___x_536_;
goto _start;
}
else
{
return v_b_531_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_528_ = stack[0].m_obj;
size_t v_i_529_ = stack[1].m_num;
size_t v_stop_530_ = stack[2].m_num;
lean_object* v_b_531_ = stack[3].m_obj;
lean_object* v_res_540_;
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_as_528_, v_i_529_, v_stop_530_, v_b_531_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_541_, lean_object* v_i_542_, lean_object* v_stop_543_, lean_object* v_b_544_){
_start:
{
size_t v_i_boxed_545_; size_t v_stop_boxed_546_; lean_object* v_res_547_; 
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_stop_boxed_546_ = lean_unbox_usize(v_stop_543_);
lean_dec(v_stop_543_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_as_541_, v_i_boxed_545_, v_stop_boxed_546_, v_b_544_);
lean_dec_ref(v_as_541_);
return v_res_547_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(uint8_t v_fmt_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___y_552_; 
if (v_fmt_549_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_559_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0));
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_array_get_size(v_a_550_);
v___x_562_ = lean_nat_dec_lt(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec_ref(v_a_550_);
v___y_552_ = v___x_559_;
goto v___jp_551_;
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((size_t)0ULL);
v___x_564_ = lean_usize_of_nat(v___x_561_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_a_550_, v___x_563_, v___x_564_, v___x_559_);
lean_dec_ref(v_a_550_);
v___y_552_ = v___x_565_;
goto v___jp_551_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(v_a_550_);
v___x_567_ = l_Lean_Json_compress(v___x_566_);
return v___x_567_;
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_string_utf8_byte_size(v___y_552_);
lean_inc_ref(v___y_552_);
v___x_556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_556_, 0, v___y_552_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
v___x_557_ = l_String_Slice_Pos_prevn(v___x_556_, v___x_555_, v___x_553_);
lean_dec_ref_known(v___x_556_, 3);
v___x_558_ = lean_string_utf8_extract_fast(v___y_552_, v___x_554_, v___x_557_);
lean_dec(v___x_557_);
lean_dec_ref(v___y_552_);
return v___x_558_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_549_ = stack[0].m_num;
lean_object* v_a_550_ = stack[1].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(v_fmt_549_, v_a_550_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___boxed(lean_object* v_fmt_569_, lean_object* v_a_570_){
_start:
{
uint8_t v_fmt_boxed_571_; lean_object* v_res_572_; 
v_fmt_boxed_571_ = lean_unbox(v_fmt_569_);
v_res_572_ = l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(v_fmt_boxed_571_, v_a_570_);
return v_res_572_;
}
}
static lean_object* _init_l_Lake_InputDir_defaultFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___f_575_ = ((lean_object*)(l_Lake_InputDir_defaultFacetConfig___closed__0));
v___x_576_ = 1;
v___x_577_ = lean_box(0);
v___x_578_ = ((lean_object*)(l_Lake_InputDir_defaultFacetConfig___closed__1));
v___x_579_ = l_Lake_InputDir_keyword;
v___x_580_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_577_);
lean_ctor_set(v___x_580_, 3, v___f_575_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*4, v___x_576_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*4 + 1, v___x_576_);
return v___x_580_;
}
}
static lean_object* _init_l_Lake_InputDir_defaultFacetConfig(void){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lake_InputDir_defaultFacetConfig___closed__2, &l_Lake_InputDir_defaultFacetConfig___closed__2_once, _init_l_Lake_InputDir_defaultFacetConfig___closed__2);
return v___x_581_;
}
}
static lean_object* _init_l_Lake_InputDir_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_box(1);
v___x_583_ = l_Lake_InputDir_defaultFacetConfig;
v___x_584_ = l_Lake_InputDir_defaultFacet;
v___x_585_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v___x_584_, v___x_583_, v___x_582_);
return v___x_585_;
}
}
static lean_object* _init_l_Lake_InputDir_initFacetConfigs(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lake_InputDir_initFacetConfigs___closed__0, &l_Lake_InputDir_initFacetConfigs___closed__0_once, _init_l_Lake_InputDir_initFacetConfigs___closed__0);
return v___x_586_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_InputFile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
