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
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, uint64_t v_b_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
uint64_t v_b_4_ = stack[3].m_num;
uint64_t v_res_14_;
v_res_14_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v_as_1_, v_i_2_, v_stop_3_, v_b_4_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1___boxed(lean_object* v_as_15_, lean_object* v_i_16_, lean_object* v_stop_17_, lean_object* v_b_18_){
_start:
{
size_t v_i_boxed_19_; size_t v_stop_boxed_20_; uint64_t v_b_boxed_21_; uint64_t v_res_22_; lean_object* v_r_23_; 
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_stop_boxed_20_ = lean_unbox_usize(v_stop_17_);
lean_dec(v_stop_17_);
v_b_boxed_21_ = lean_unbox_uint64(v_b_18_);
lean_dec_ref(v_b_18_);
v_res_22_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v_as_15_, v_i_boxed_19_, v_stop_boxed_20_, v_b_boxed_21_);
lean_dec_ref(v_as_15_);
v_r_23_ = lean_box_uint64(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
return v_x_25_;
}
else
{
lean_object* v_head_27_; lean_object* v_tail_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_head_27_ = lean_ctor_get(v_x_26_, 0);
v_tail_28_ = lean_ctor_get(v_x_26_, 1);
v___x_29_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___closed__0));
v___x_30_ = lean_string_append(v_x_25_, v___x_29_);
v___x_31_ = lean_string_append(v___x_30_, v_head_27_);
v_x_25_ = v___x_31_;
v_x_26_ = v_tail_28_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___boxed(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(v_x_33_, v_x_34_);
lean_dec(v_x_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__0));
return v___x_40_;
}
else
{
lean_object* v_tail_41_; 
v_tail_41_ = lean_ctor_get(v_x_39_, 1);
if (lean_obj_tag(v_tail_41_) == 0)
{
lean_object* v_head_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_head_42_ = lean_ctor_get(v_x_39_, 0);
v___x_43_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__1));
v___x_44_ = lean_string_append(v___x_43_, v_head_42_);
v___x_45_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__2));
v___x_46_ = lean_string_append(v___x_44_, v___x_45_);
return v___x_46_;
}
else
{
lean_object* v_head_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint32_t v___x_51_; lean_object* v___x_52_; 
v_head_47_ = lean_ctor_get(v_x_39_, 0);
v___x_48_ = ((lean_object*)(l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___closed__1));
v___x_49_ = lean_string_append(v___x_48_, v_head_47_);
v___x_50_ = l_List_foldl___at___00List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(v___x_49_, v_tail_41_);
v___x_51_ = 93;
v___x_52_ = lean_string_push(v___x_50_, v___x_51_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0___boxed(lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(v_x_53_);
lean_dec(v_x_53_);
return v_res_54_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4(void){
_start:
{
uint32_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = 0;
v___x_62_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3);
v___x_63_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set_uint32(v___x_63_, sizeof(void*)*1, v___x_61_);
return v___x_63_;
}
}
lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(lean_object* v_self_64_, lean_object* v_pkg_65_, lean_object* v_exeName_66_, uint8_t v_supportInterpreter_67_, lean_object* v_info_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_args_76_; lean_object* v_objs_77_; lean_object* v_libs_78_; lean_object* v___x_79_; lean_object* v_args_80_; uint64_t v___y_82_; uint64_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_args_76_ = lean_ctor_get(v_info_68_, 0);
lean_inc_ref(v_args_76_);
v_objs_77_ = lean_ctor_get(v_info_68_, 1);
lean_inc_ref(v_objs_77_);
v_libs_78_ = lean_ctor_get(v_info_68_, 2);
lean_inc_ref(v_libs_78_);
lean_dec_ref(v_info_68_);
v___x_79_ = l_Lake_LeanExe_exeOnlyLinkArgs(v_self_64_);
lean_inc_ref(v___x_79_);
v_args_80_ = l_Array_append___redArg(v___x_79_, v_args_76_);
lean_dec_ref(v_args_76_);
v___x_121_ = l_Lake_Hash_nil;
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_array_get_size(v___x_79_);
v___x_124_ = lean_nat_dec_lt(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
v___y_82_ = v___x_121_;
goto v___jp_81_;
}
else
{
size_t v___x_125_; size_t v___x_126_; uint64_t v___x_127_; 
v___x_125_ = ((size_t)0ULL);
v___x_126_ = lean_usize_of_nat(v___x_123_);
v___x_127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___x_79_, v___x_125_, v___x_126_, v___x_121_);
v___y_82_ = v___x_127_;
goto v___jp_81_;
}
v___jp_81_:
{
lean_object* v_config_83_; lean_object* v_log_84_; uint8_t v_action_85_; uint8_t v_wantsRebuild_86_; uint8_t v_canceled_87_; lean_object* v_trace_88_; lean_object* v_buildTime_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_120_; 
v_config_83_ = lean_ctor_get(v_pkg_65_, 6);
lean_inc_ref(v_config_83_);
v_log_84_ = lean_ctor_get(v___y_74_, 0);
v_action_85_ = lean_ctor_get_uint8(v___y_74_, sizeof(void*)*3);
v_wantsRebuild_86_ = lean_ctor_get_uint8(v___y_74_, sizeof(void*)*3 + 1);
v_canceled_87_ = lean_ctor_get_uint8(v___y_74_, sizeof(void*)*3 + 2);
v_trace_88_ = lean_ctor_get(v___y_74_, 1);
v_buildTime_89_ = lean_ctor_get(v___y_74_, 2);
v_isSharedCheck_120_ = !lean_is_exclusive(v___y_74_);
if (v_isSharedCheck_120_ == 0)
{
v___x_91_ = v___y_74_;
v_isShared_92_ = v_isSharedCheck_120_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_buildTime_89_);
lean_inc(v_trace_88_);
lean_inc(v_log_84_);
lean_dec(v___y_74_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_120_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_dir_93_; lean_object* v_buildDir_94_; lean_object* v_binDir_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v_dir_93_ = lean_ctor_get(v_pkg_65_, 4);
lean_inc_ref(v_dir_93_);
lean_dec_ref(v_pkg_65_);
v_buildDir_94_ = lean_ctor_get(v_config_83_, 5);
lean_inc_ref(v_buildDir_94_);
v_binDir_95_ = lean_ctor_get(v_config_83_, 8);
lean_inc_ref(v_binDir_95_);
lean_dec_ref(v_config_83_);
v___x_96_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0));
v___x_97_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1));
v___x_98_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2));
v___x_99_ = lean_array_to_list(v___x_79_);
v___x_100_ = l_List_toString___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(v___x_99_);
lean_dec(v___x_99_);
v___x_101_ = lean_string_append(v___x_98_, v___x_100_);
lean_dec_ref(v___x_100_);
v___x_102_ = lean_string_append(v___x_97_, v___x_101_);
lean_dec_ref(v___x_101_);
v___x_103_ = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__4);
v___x_104_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_96_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
lean_ctor_set_uint64(v___x_104_, sizeof(void*)*3, v___y_82_);
v___x_105_ = l_Lake_BuildTrace_mix(v_trace_88_, v___x_104_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___x_105_);
v___x_107_ = v___x_91_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_log_84_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_buildTime_89_);
lean_ctor_set_uint8(v_reuseFailAlloc_119_, sizeof(void*)*3, v_action_85_);
lean_ctor_set_uint8(v_reuseFailAlloc_119_, sizeof(void*)*3 + 1, v_wantsRebuild_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_119_, sizeof(void*)*3 + 2, v_canceled_87_);
v___x_107_ = v_reuseFailAlloc_119_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_108_ = l_System_FilePath_normalize(v_buildDir_94_);
v___x_109_ = l_Lake_joinRelative(v_dir_93_, v___x_108_);
v___x_110_ = l_System_FilePath_normalize(v_binDir_95_);
v___x_111_ = l_Lake_joinRelative(v___x_109_, v___x_110_);
v___x_112_ = l_System_FilePath_exeExtension;
v___x_113_ = l_System_FilePath_addExtension(v_exeName_66_, v___x_112_);
v___x_114_ = l_Lake_joinRelative(v___x_111_, v___x_113_);
v___x_115_ = l_System_Platform_isWindows;
v___x_116_ = lean_strict_and(v___x_115_, v_supportInterpreter_67_);
v___x_117_ = lean_box(0);
v___x_118_ = l_Lake_buildLeanExeSync(v___x_114_, v_objs_77_, v_libs_78_, v_args_80_, v___x_116_, v___x_117_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___x_107_);
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_64_ = stack[0].m_obj;
lean_object* v_pkg_65_ = stack[1].m_obj;
lean_object* v_exeName_66_ = stack[2].m_obj;
uint8_t v_supportInterpreter_67_ = stack[3].m_num;
lean_object* v_info_68_ = stack[4].m_obj;
lean_object* v___y_69_ = stack[5].m_obj;
lean_object* v___y_70_ = stack[6].m_obj;
lean_object* v___y_71_ = stack[7].m_obj;
lean_object* v___y_72_ = stack[8].m_obj;
lean_object* v___y_73_ = stack[9].m_obj;
lean_object* v___y_74_ = stack[10].m_obj;
lean_object* v_res_128_;
v_res_128_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(v_self_64_, v_pkg_65_, v_exeName_66_, v_supportInterpreter_67_, v_info_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
stack->m_obj
 = v_res_128_;
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
lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(lean_object* v___x_146_, lean_object* v___f_147_, lean_object* v_infoJob_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
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
LEAN_EXPORT void l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_146_ = stack[0].m_obj;
lean_object* v___f_147_ = stack[1].m_obj;
lean_object* v_infoJob_148_ = stack[2].m_obj;
lean_object* v___y_149_ = stack[3].m_obj;
lean_object* v___y_150_ = stack[4].m_obj;
lean_object* v___y_151_ = stack[5].m_obj;
lean_object* v___y_152_ = stack[6].m_obj;
lean_object* v___y_153_ = stack[7].m_obj;
lean_object* v___y_154_ = stack[8].m_obj;
lean_object* v_res_161_;
v_res_161_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1(v___x_146_, v___f_147_, v_infoJob_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
stack->m_obj
 = v_res_161_;
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
lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(uint8_t v_supportInterpreter_173_, lean_object* v_pkg_174_, lean_object* v_config_175_, lean_object* v_name_176_, lean_object* v_root_177_, lean_object* v___x_178_, lean_object* v___f_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
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
LEAN_EXPORT void l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_supportInterpreter_173_ = stack[0].m_num;
lean_object* v_pkg_174_ = stack[1].m_obj;
lean_object* v_config_175_ = stack[2].m_obj;
lean_object* v_name_176_ = stack[3].m_obj;
lean_object* v_root_177_ = stack[4].m_obj;
lean_object* v___x_178_ = stack[5].m_obj;
lean_object* v___f_179_ = stack[6].m_obj;
lean_object* v___y_180_ = stack[7].m_obj;
lean_object* v___y_181_ = stack[8].m_obj;
lean_object* v___y_182_ = stack[9].m_obj;
lean_object* v___y_183_ = stack[10].m_obj;
lean_object* v___y_184_ = stack[11].m_obj;
lean_object* v___y_185_ = stack[12].m_obj;
lean_object* v_res_229_;
v_res_229_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(v_supportInterpreter_173_, v_pkg_174_, v_config_175_, v_name_176_, v_root_177_, v___x_178_, v___f_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed(lean_object* v_supportInterpreter_230_, lean_object* v_pkg_231_, lean_object* v_config_232_, lean_object* v_name_233_, lean_object* v_root_234_, lean_object* v___x_235_, lean_object* v___f_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
uint8_t v_supportInterpreter_boxed_244_; lean_object* v_res_245_; 
v_supportInterpreter_boxed_244_ = lean_unbox(v_supportInterpreter_230_);
v_res_245_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2(v_supportInterpreter_boxed_244_, v_pkg_231_, v_config_232_, v_name_233_, v_root_234_, v___x_235_, v___f_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
lean_dec(v_config_232_);
return v_res_245_;
}
}
lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object* v_self_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_config_255_; lean_object* v_pkg_256_; lean_object* v_name_257_; lean_object* v_root_258_; lean_object* v_exeName_259_; uint8_t v_supportInterpreter_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___f_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___f_271_; uint8_t v___x_272_; lean_object* v___x_273_; 
v_config_255_ = lean_ctor_get(v_self_247_, 2);
lean_inc(v_config_255_);
v_pkg_256_ = lean_ctor_get(v_self_247_, 0);
lean_inc_ref_n(v_pkg_256_, 3);
v_name_257_ = lean_ctor_get(v_self_247_, 1);
lean_inc_n(v_name_257_, 2);
v_root_258_ = lean_ctor_get(v_config_255_, 2);
lean_inc(v_root_258_);
v_exeName_259_ = lean_ctor_get(v_config_255_, 3);
v_supportInterpreter_260_ = lean_ctor_get_uint8(v_config_255_, sizeof(void*)*7);
v___x_261_ = lean_box(v_supportInterpreter_260_);
lean_inc_ref(v_exeName_259_);
v___f_262_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed), 12, 4);
lean_closure_set(v___f_262_, 0, v_self_247_);
lean_closure_set(v___f_262_, 1, v_pkg_256_);
lean_closure_set(v___f_262_, 2, v_exeName_259_);
lean_closure_set(v___f_262_, 3, v___x_261_);
v___x_263_ = l_Lake_instDataKindFilePath;
v___f_264_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__1___boxed), 10, 2);
lean_closure_set(v___f_264_, 0, v___x_263_);
lean_closure_set(v___f_264_, 1, v___f_262_);
v___x_265_ = 1;
v___x_266_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_257_, v___x_265_);
v___x_267_ = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0));
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_pkg_256_);
v___x_270_ = lean_box(v_supportInterpreter_260_);
v___f_271_ = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__2___boxed), 14, 7);
lean_closure_set(v___f_271_, 0, v___x_270_);
lean_closure_set(v___f_271_, 1, v_pkg_256_);
lean_closure_set(v___f_271_, 2, v_config_255_);
lean_closure_set(v___f_271_, 3, v_name_257_);
lean_closure_set(v___f_271_, 4, v_root_258_);
lean_closure_set(v___f_271_, 5, v___x_269_);
lean_closure_set(v___f_271_, 6, v___f_264_);
v___x_272_ = 0;
v___x_273_ = l_Lake_ensureJob___redArg(v___x_263_, v___f_271_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_298_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_a_275_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_298_ == 0)
{
v___x_277_ = v___x_273_;
v_isShared_278_ = v_isSharedCheck_298_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_298_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_task_279_; lean_object* v_kind_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_296_; 
v_task_279_ = lean_ctor_get(v_a_274_, 0);
v_kind_280_ = lean_ctor_get(v_a_274_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_a_274_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_a_274_, 2);
lean_dec(v_unused_297_);
v___x_282_ = v_a_274_;
v_isShared_283_ = v_isSharedCheck_296_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_kind_280_);
lean_inc(v_task_279_);
lean_dec(v_a_274_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_296_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_registeredJobs_284_; lean_object* v_job_286_; 
v_registeredJobs_284_ = lean_ctor_get(v_a_252_, 4);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 2, v___x_268_);
v_job_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_task_279_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_kind_280_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v___x_268_);
v_job_286_ = v_reuseFailAlloc_295_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
lean_ctor_set_uint8(v_job_286_, sizeof(void*)*3, v___x_272_);
v___x_287_ = lean_st_ref_take(v_registeredJobs_284_);
lean_inc_ref(v_job_286_);
v___x_288_ = l_Lake_Job_toOpaque___redArg(v_job_286_);
v___x_289_ = lean_array_push(v___x_287_, v___x_288_);
v___x_290_ = lean_st_ref_put(v_registeredJobs_284_, v___x_289_);
v___x_291_ = l_Lake_Job_renew___redArg(v_job_286_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_291_);
v___x_293_ = v___x_277_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_a_275_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_268_);
return v___x_273_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_247_ = stack[0].m_obj;
lean_object* v_a_248_ = stack[1].m_obj;
lean_object* v_a_249_ = stack[2].m_obj;
lean_object* v_a_250_ = stack[3].m_obj;
lean_object* v_a_251_ = stack[4].m_obj;
lean_object* v_a_252_ = stack[5].m_obj;
lean_object* v_a_253_ = stack[6].m_obj;
lean_object* v_res_299_;
v_res_299_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(v_self_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object* v_self_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(v_self_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec(v_a_303_);
lean_dec(v_a_302_);
return v_res_308_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t v_fmt_309_, lean_object* v_a_310_){
_start:
{
if (v_fmt_309_ == 0)
{
return v_a_310_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = l_Lake_mkRelPathString(v_a_310_);
v___x_312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
v___x_313_ = l_Lean_Json_compress(v___x_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_309_ = stack[0].m_num;
lean_object* v_a_310_ = stack[1].m_obj;
lean_object* v_res_314_;
v_res_314_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(v_fmt_309_, v_a_310_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object* v_fmt_315_, lean_object* v_a_316_){
_start:
{
uint8_t v_fmt_boxed_317_; lean_object* v_res_318_; 
v_fmt_boxed_317_ = lean_unbox(v_fmt_315_);
v_res_318_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(v_fmt_boxed_317_, v_a_316_);
return v_res_318_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___f_321_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_322_ = 1;
v___x_323_ = l_Lake_instDataKindFilePath;
v___x_324_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__1));
v___x_325_ = l_Lake_LeanExe_keyword;
v___x_326_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_323_);
lean_ctor_set(v___x_326_, 3, v___f_321_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*4, v___x_322_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*4 + 1, v___x_322_);
return v___x_326_;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lake_LeanExe_exeFacetConfig___closed__2, &l_Lake_LeanExe_exeFacetConfig___closed__2_once, _init_l_Lake_LeanExe_exeFacetConfig___closed__2);
return v___x_327_;
}
}
lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object* v_lib_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_pkg_336_; lean_object* v_name_337_; lean_object* v_keyName_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_pkg_336_ = lean_ctor_get(v_lib_328_, 0);
v_name_337_ = lean_ctor_get(v_lib_328_, 1);
v_keyName_338_ = lean_ctor_get(v_pkg_336_, 2);
v___x_339_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_337_);
lean_inc(v_keyName_338_);
v___x_340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_340_, 0, v_keyName_338_);
lean_ctor_set(v___x_340_, 1, v_name_337_);
v___x_341_ = l_Lake_LeanExe_keyword;
v___x_342_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
lean_ctor_set(v___x_342_, 2, v_lib_328_);
lean_ctor_set(v___x_342_, 3, v___x_339_);
lean_inc_ref(v_a_333_);
lean_inc(v_a_332_);
lean_inc(v_a_331_);
lean_inc(v_a_330_);
v___x_343_ = lean_apply_7(v_a_329_, v___x_342_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, lean_box(0));
return v___x_343_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_lib_328_ = stack[0].m_obj;
lean_object* v_a_329_ = stack[1].m_obj;
lean_object* v_a_330_ = stack[2].m_obj;
lean_object* v_a_331_ = stack[3].m_obj;
lean_object* v_a_332_ = stack[4].m_obj;
lean_object* v_a_333_ = stack[5].m_obj;
lean_object* v_a_334_ = stack[6].m_obj;
lean_object* v_res_344_;
v_res_344_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(v_lib_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object* v_lib_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(v_lib_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec(v_a_348_);
lean_dec(v_a_347_);
return v_res_353_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_355_; lean_object* v___f_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_355_ = 0;
v___f_356_ = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
v___x_357_ = 1;
v___x_358_ = l_Lake_instDataKindFilePath;
v___x_359_ = ((lean_object*)(l_Lake_LeanExe_defaultFacetConfig___closed__0));
v___x_360_ = l_Lake_LeanExe_keyword;
v___x_361_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
lean_ctor_set(v___x_361_, 2, v___x_358_);
lean_ctor_set(v___x_361_, 3, v___f_356_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*4, v___x_357_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*4 + 1, v___x_355_);
return v___x_361_;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Lake_LeanExe_defaultFacetConfig___closed__1, &l_Lake_LeanExe_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanExe_defaultFacetConfig___closed__1);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object* v_k_363_, lean_object* v_v_364_, lean_object* v_t_365_){
_start:
{
if (lean_obj_tag(v_t_365_) == 0)
{
lean_object* v_size_366_; lean_object* v_k_367_; lean_object* v_v_368_; lean_object* v_l_369_; lean_object* v_r_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_650_; 
v_size_366_ = lean_ctor_get(v_t_365_, 0);
v_k_367_ = lean_ctor_get(v_t_365_, 1);
v_v_368_ = lean_ctor_get(v_t_365_, 2);
v_l_369_ = lean_ctor_get(v_t_365_, 3);
v_r_370_ = lean_ctor_get(v_t_365_, 4);
v_isSharedCheck_650_ = !lean_is_exclusive(v_t_365_);
if (v_isSharedCheck_650_ == 0)
{
v___x_372_ = v_t_365_;
v_isShared_373_ = v_isSharedCheck_650_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_r_370_);
lean_inc(v_l_369_);
lean_inc(v_v_368_);
lean_inc(v_k_367_);
lean_inc(v_size_366_);
lean_dec(v_t_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_650_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_363_, v_k_367_);
switch(v___x_374_)
{
case 0:
{
lean_object* v_impl_375_; lean_object* v___x_376_; 
lean_dec(v_size_366_);
v_impl_375_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_363_, v_v_364_, v_l_369_);
v___x_376_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_370_) == 0)
{
lean_object* v_size_377_; lean_object* v_size_378_; lean_object* v_k_379_; lean_object* v_v_380_; lean_object* v_l_381_; lean_object* v_r_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_size_377_ = lean_ctor_get(v_r_370_, 0);
v_size_378_ = lean_ctor_get(v_impl_375_, 0);
v_k_379_ = lean_ctor_get(v_impl_375_, 1);
v_v_380_ = lean_ctor_get(v_impl_375_, 2);
v_l_381_ = lean_ctor_get(v_impl_375_, 3);
v_r_382_ = lean_ctor_get(v_impl_375_, 4);
lean_inc(v_r_382_);
v___x_383_ = lean_unsigned_to_nat(3u);
v___x_384_ = lean_nat_mul(v___x_383_, v_size_377_);
v___x_385_ = lean_nat_dec_lt(v___x_384_, v_size_378_);
lean_dec(v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
lean_dec(v_r_382_);
v___x_386_ = lean_nat_add(v___x_376_, v_size_378_);
v___x_387_ = lean_nat_add(v___x_386_, v_size_377_);
lean_dec(v___x_386_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 3, v_impl_375_);
lean_ctor_set(v___x_372_, 0, v___x_387_);
v___x_389_ = v___x_372_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_impl_375_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_r_370_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
else
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_456_; 
lean_inc(v_l_381_);
lean_inc(v_v_380_);
lean_inc(v_k_379_);
lean_inc(v_size_378_);
v_isSharedCheck_456_ = !lean_is_exclusive(v_impl_375_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; lean_object* v_unused_461_; 
v_unused_457_ = lean_ctor_get(v_impl_375_, 4);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_impl_375_, 3);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_impl_375_, 2);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_impl_375_, 1);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_impl_375_, 0);
lean_dec(v_unused_461_);
v___x_392_ = v_impl_375_;
v_isShared_393_ = v_isSharedCheck_456_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_impl_375_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_456_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_size_394_; lean_object* v_size_395_; lean_object* v_k_396_; lean_object* v_v_397_; lean_object* v_l_398_; lean_object* v_r_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_size_394_ = lean_ctor_get(v_l_381_, 0);
v_size_395_ = lean_ctor_get(v_r_382_, 0);
v_k_396_ = lean_ctor_get(v_r_382_, 1);
v_v_397_ = lean_ctor_get(v_r_382_, 2);
v_l_398_ = lean_ctor_get(v_r_382_, 3);
v_r_399_ = lean_ctor_get(v_r_382_, 4);
v___x_400_ = lean_unsigned_to_nat(2u);
v___x_401_ = lean_nat_mul(v___x_400_, v_size_394_);
v___x_402_ = lean_nat_dec_lt(v_size_395_, v___x_401_);
lean_dec(v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_431_; 
lean_inc(v_r_399_);
lean_inc(v_l_398_);
lean_inc(v_v_397_);
lean_inc(v_k_396_);
v_isSharedCheck_431_ = !lean_is_exclusive(v_r_382_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_432_ = lean_ctor_get(v_r_382_, 4);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_r_382_, 3);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_r_382_, 2);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_r_382_, 1);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_r_382_, 0);
lean_dec(v_unused_436_);
v___x_404_ = v_r_382_;
v_isShared_405_ = v_isSharedCheck_431_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_r_382_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_431_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___x_419_; lean_object* v___y_421_; 
v___x_406_ = lean_nat_add(v___x_376_, v_size_378_);
lean_dec(v_size_378_);
v___x_407_ = lean_nat_add(v___x_406_, v_size_377_);
lean_dec(v___x_406_);
v___x_419_ = lean_nat_add(v___x_376_, v_size_394_);
if (lean_obj_tag(v_l_398_) == 0)
{
lean_object* v_size_429_; 
v_size_429_ = lean_ctor_get(v_l_398_, 0);
lean_inc(v_size_429_);
v___y_421_ = v_size_429_;
goto v___jp_420_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___y_421_ = v___x_430_;
goto v___jp_420_;
}
v___jp_408_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = lean_nat_add(v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec(v___y_410_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 4, v_r_370_);
lean_ctor_set(v___x_404_, 3, v_r_399_);
lean_ctor_set(v___x_404_, 2, v_v_368_);
lean_ctor_set(v___x_404_, 1, v_k_367_);
lean_ctor_set(v___x_404_, 0, v___x_412_);
v___x_414_ = v___x_404_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_r_399_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_r_370_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 4, v___x_414_);
lean_ctor_set(v___x_392_, 3, v___y_409_);
lean_ctor_set(v___x_392_, 2, v_v_397_);
lean_ctor_set(v___x_392_, 1, v_k_396_);
lean_ctor_set(v___x_392_, 0, v___x_407_);
v___x_416_ = v___x_392_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_k_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_v_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v___y_409_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
v___jp_420_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_nat_add(v___x_419_, v___y_421_);
lean_dec(v___y_421_);
lean_dec(v___x_419_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_l_398_);
lean_ctor_set(v___x_372_, 3, v_l_381_);
lean_ctor_set(v___x_372_, 2, v_v_380_);
lean_ctor_set(v___x_372_, 1, v_k_379_);
lean_ctor_set(v___x_372_, 0, v___x_422_);
v___x_424_ = v___x_372_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_379_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_380_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_l_381_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_l_398_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; 
v___x_425_ = lean_nat_add(v___x_376_, v_size_377_);
if (lean_obj_tag(v_r_399_) == 0)
{
lean_object* v_size_426_; 
v_size_426_ = lean_ctor_get(v_r_399_, 0);
lean_inc(v_size_426_);
v___y_409_ = v___x_424_;
v___y_410_ = v___x_425_;
v___y_411_ = v_size_426_;
goto v___jp_408_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___y_409_ = v___x_424_;
v___y_410_ = v___x_425_;
v___y_411_ = v___x_427_;
goto v___jp_408_;
}
}
}
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
lean_del_object(v___x_372_);
v___x_437_ = lean_nat_add(v___x_376_, v_size_378_);
lean_dec(v_size_378_);
v___x_438_ = lean_nat_add(v___x_437_, v_size_377_);
lean_dec(v___x_437_);
v___x_439_ = lean_nat_add(v___x_376_, v_size_377_);
v___x_440_ = lean_nat_add(v___x_439_, v_size_395_);
lean_dec(v___x_439_);
lean_inc_ref(v_r_370_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 4, v_r_370_);
lean_ctor_set(v___x_392_, 3, v_r_382_);
lean_ctor_set(v___x_392_, 2, v_v_368_);
lean_ctor_set(v___x_392_, 1, v_k_367_);
lean_ctor_set(v___x_392_, 0, v___x_440_);
v___x_442_ = v___x_392_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_r_382_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_r_370_);
v___x_442_ = v_reuseFailAlloc_455_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v_r_370_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_450_ = lean_ctor_get(v_r_370_, 4);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_r_370_, 3);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_r_370_, 2);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_r_370_, 1);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_r_370_, 0);
lean_dec(v_unused_454_);
v___x_444_ = v_r_370_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_dec(v_r_370_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 4, v___x_442_);
lean_ctor_set(v___x_444_, 3, v_l_381_);
lean_ctor_set(v___x_444_, 2, v_v_380_);
lean_ctor_set(v___x_444_, 1, v_k_379_);
lean_ctor_set(v___x_444_, 0, v___x_438_);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_k_379_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_v_380_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_l_381_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v___x_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_462_; 
v_l_462_ = lean_ctor_get(v_impl_375_, 3);
if (lean_obj_tag(v_l_462_) == 0)
{
lean_object* v_r_463_; lean_object* v_k_464_; lean_object* v_v_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_476_; 
lean_inc_ref(v_l_462_);
v_r_463_ = lean_ctor_get(v_impl_375_, 4);
v_k_464_ = lean_ctor_get(v_impl_375_, 1);
v_v_465_ = lean_ctor_get(v_impl_375_, 2);
v_isSharedCheck_476_ = !lean_is_exclusive(v_impl_375_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_477_ = lean_ctor_get(v_impl_375_, 3);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_impl_375_, 0);
lean_dec(v_unused_478_);
v___x_467_ = v_impl_375_;
v_isShared_468_ = v_isSharedCheck_476_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_r_463_);
lean_inc(v_v_465_);
lean_inc(v_k_464_);
lean_dec(v_impl_375_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_476_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_463_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 3, v_r_463_);
lean_ctor_set(v___x_467_, 2, v_v_368_);
lean_ctor_set(v___x_467_, 1, v_k_367_);
lean_ctor_set(v___x_467_, 0, v___x_376_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_r_463_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_r_463_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_471_);
lean_ctor_set(v___x_372_, 3, v_l_462_);
lean_ctor_set(v___x_372_, 2, v_v_465_);
lean_ctor_set(v___x_372_, 1, v_k_464_);
lean_ctor_set(v___x_372_, 0, v___x_469_);
v___x_473_ = v___x_372_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_l_462_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_r_479_; 
v_r_479_ = lean_ctor_get(v_impl_375_, 4);
lean_inc(v_r_479_);
if (lean_obj_tag(v_r_479_) == 0)
{
lean_object* v_k_480_; lean_object* v_v_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_504_; 
lean_inc(v_l_462_);
v_k_480_ = lean_ctor_get(v_impl_375_, 1);
v_v_481_ = lean_ctor_get(v_impl_375_, 2);
v_isSharedCheck_504_ = !lean_is_exclusive(v_impl_375_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; lean_object* v_unused_506_; lean_object* v_unused_507_; 
v_unused_505_ = lean_ctor_get(v_impl_375_, 4);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_impl_375_, 3);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_impl_375_, 0);
lean_dec(v_unused_507_);
v___x_483_ = v_impl_375_;
v_isShared_484_ = v_isSharedCheck_504_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_v_481_);
lean_inc(v_k_480_);
lean_dec(v_impl_375_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_504_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_k_485_; lean_object* v_v_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_500_; 
v_k_485_ = lean_ctor_get(v_r_479_, 1);
v_v_486_ = lean_ctor_get(v_r_479_, 2);
v_isSharedCheck_500_ = !lean_is_exclusive(v_r_479_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_501_ = lean_ctor_get(v_r_479_, 4);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_r_479_, 3);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_r_479_, 0);
lean_dec(v_unused_503_);
v___x_488_ = v_r_479_;
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_v_486_);
lean_inc(v_k_485_);
lean_dec(v_r_479_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_unsigned_to_nat(3u);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_l_462_);
lean_ctor_set(v___x_488_, 3, v_l_462_);
lean_ctor_set(v___x_488_, 2, v_v_481_);
lean_ctor_set(v___x_488_, 1, v_k_480_);
lean_ctor_set(v___x_488_, 0, v___x_376_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_k_480_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_v_481_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_l_462_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_l_462_);
v___x_492_ = v_reuseFailAlloc_499_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_l_462_);
lean_ctor_set(v___x_483_, 2, v_v_368_);
lean_ctor_set(v___x_483_, 1, v_k_367_);
lean_ctor_set(v___x_483_, 0, v___x_376_);
v___x_494_ = v___x_483_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_l_462_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_l_462_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_494_);
lean_ctor_set(v___x_372_, 3, v___x_492_);
lean_ctor_set(v___x_372_, 2, v_v_486_);
lean_ctor_set(v___x_372_, 1, v_k_485_);
lean_ctor_set(v___x_372_, 0, v___x_490_);
v___x_496_ = v___x_372_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_k_485_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_v_486_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_unsigned_to_nat(2u);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_r_479_);
lean_ctor_set(v___x_372_, 3, v_impl_375_);
lean_ctor_set(v___x_372_, 0, v___x_508_);
v___x_510_ = v___x_372_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_impl_375_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_r_479_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
case 1:
{
lean_object* v___x_513_; 
lean_dec(v_v_368_);
lean_dec(v_k_367_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 2, v_v_364_);
lean_ctor_set(v___x_372_, 1, v_k_363_);
v___x_513_ = v___x_372_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_size_366_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_k_363_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_v_364_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_r_370_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
default: 
{
lean_object* v_impl_515_; lean_object* v___x_516_; 
lean_dec(v_size_366_);
v_impl_515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_363_, v_v_364_, v_r_370_);
v___x_516_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_369_) == 0)
{
lean_object* v_size_517_; lean_object* v_size_518_; lean_object* v_k_519_; lean_object* v_v_520_; lean_object* v_l_521_; lean_object* v_r_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_size_517_ = lean_ctor_get(v_l_369_, 0);
v_size_518_ = lean_ctor_get(v_impl_515_, 0);
v_k_519_ = lean_ctor_get(v_impl_515_, 1);
v_v_520_ = lean_ctor_get(v_impl_515_, 2);
v_l_521_ = lean_ctor_get(v_impl_515_, 3);
lean_inc(v_l_521_);
v_r_522_ = lean_ctor_get(v_impl_515_, 4);
v___x_523_ = lean_unsigned_to_nat(3u);
v___x_524_ = lean_nat_mul(v___x_523_, v_size_517_);
v___x_525_ = lean_nat_dec_lt(v___x_524_, v_size_518_);
lean_dec(v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_l_521_);
v___x_526_ = lean_nat_add(v___x_516_, v_size_517_);
v___x_527_ = lean_nat_add(v___x_526_, v_size_518_);
lean_dec(v___x_526_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_impl_515_);
lean_ctor_set(v___x_372_, 0, v___x_527_);
v___x_529_ = v___x_372_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v_impl_515_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_594_; 
lean_inc(v_r_522_);
lean_inc(v_v_520_);
lean_inc(v_k_519_);
lean_inc(v_size_518_);
v_isSharedCheck_594_ = !lean_is_exclusive(v_impl_515_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; lean_object* v_unused_596_; lean_object* v_unused_597_; lean_object* v_unused_598_; lean_object* v_unused_599_; 
v_unused_595_ = lean_ctor_get(v_impl_515_, 4);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_impl_515_, 3);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_impl_515_, 2);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_impl_515_, 1);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_impl_515_, 0);
lean_dec(v_unused_599_);
v___x_532_ = v_impl_515_;
v_isShared_533_ = v_isSharedCheck_594_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_impl_515_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_594_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_size_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v_size_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_size_534_ = lean_ctor_get(v_l_521_, 0);
v_k_535_ = lean_ctor_get(v_l_521_, 1);
v_v_536_ = lean_ctor_get(v_l_521_, 2);
v_l_537_ = lean_ctor_get(v_l_521_, 3);
v_r_538_ = lean_ctor_get(v_l_521_, 4);
v_size_539_ = lean_ctor_get(v_r_522_, 0);
v___x_540_ = lean_unsigned_to_nat(2u);
v___x_541_ = lean_nat_mul(v___x_540_, v_size_539_);
v___x_542_ = lean_nat_dec_lt(v_size_534_, v___x_541_);
lean_dec(v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_r_538_);
lean_inc(v_l_537_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_l_521_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_571_ = lean_ctor_get(v_l_521_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_l_521_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_l_521_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_l_521_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_l_521_, 0);
lean_dec(v_unused_575_);
v___x_544_ = v_l_521_;
v_isShared_545_ = v_isSharedCheck_570_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_l_521_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_570_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_560_; 
v___x_546_ = lean_nat_add(v___x_516_, v_size_517_);
v___x_547_ = lean_nat_add(v___x_546_, v_size_518_);
lean_dec(v_size_518_);
if (lean_obj_tag(v_l_537_) == 0)
{
lean_object* v_size_568_; 
v_size_568_ = lean_ctor_get(v_l_537_, 0);
lean_inc(v_size_568_);
v___y_560_ = v_size_568_;
goto v___jp_559_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___y_560_ = v___x_569_;
goto v___jp_559_;
}
v___jp_548_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_nat_add(v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec(v___y_550_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 4, v_r_522_);
lean_ctor_set(v___x_544_, 3, v_r_538_);
lean_ctor_set(v___x_544_, 2, v_v_520_);
lean_ctor_set(v___x_544_, 1, v_k_519_);
lean_ctor_set(v___x_544_, 0, v___x_552_);
v___x_554_ = v___x_544_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_r_538_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_r_522_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v___x_554_);
lean_ctor_set(v___x_532_, 3, v___y_549_);
lean_ctor_set(v___x_532_, 2, v_v_536_);
lean_ctor_set(v___x_532_, 1, v_k_535_);
lean_ctor_set(v___x_532_, 0, v___x_547_);
v___x_556_ = v___x_532_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_k_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_v_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v___y_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_nat_add(v___x_546_, v___y_560_);
lean_dec(v___y_560_);
lean_dec(v___x_546_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_l_537_);
lean_ctor_set(v___x_372_, 0, v___x_561_);
v___x_563_ = v___x_372_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_l_537_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_nat_add(v___x_516_, v_size_539_);
if (lean_obj_tag(v_r_538_) == 0)
{
lean_object* v_size_565_; 
v_size_565_ = lean_ctor_get(v_r_538_, 0);
lean_inc(v_size_565_);
v___y_549_ = v___x_563_;
v___y_550_ = v___x_564_;
v___y_551_ = v_size_565_;
goto v___jp_548_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___y_549_ = v___x_563_;
v___y_550_ = v___x_564_;
v___y_551_ = v___x_566_;
goto v___jp_548_;
}
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_del_object(v___x_372_);
v___x_576_ = lean_nat_add(v___x_516_, v_size_517_);
v___x_577_ = lean_nat_add(v___x_576_, v_size_518_);
lean_dec(v_size_518_);
v___x_578_ = lean_nat_add(v___x_576_, v_size_534_);
lean_dec(v___x_576_);
lean_inc_ref(v_l_369_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v_l_521_);
lean_ctor_set(v___x_532_, 3, v_l_369_);
lean_ctor_set(v___x_532_, 2, v_v_368_);
lean_ctor_set(v___x_532_, 1, v_k_367_);
lean_ctor_set(v___x_532_, 0, v___x_578_);
v___x_580_ = v___x_532_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_l_369_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_l_521_);
v___x_580_ = v_reuseFailAlloc_593_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v_l_369_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; 
v_unused_588_ = lean_ctor_get(v_l_369_, 4);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_l_369_, 3);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_l_369_, 2);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_l_369_, 1);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_l_369_, 0);
lean_dec(v_unused_592_);
v___x_582_ = v_l_369_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_l_369_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 4, v_r_522_);
lean_ctor_set(v___x_582_, 3, v___x_580_);
lean_ctor_set(v___x_582_, 2, v_v_520_);
lean_ctor_set(v___x_582_, 1, v_k_519_);
lean_ctor_set(v___x_582_, 0, v___x_577_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_r_522_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_600_; 
v_l_600_ = lean_ctor_get(v_impl_515_, 3);
lean_inc(v_l_600_);
if (lean_obj_tag(v_l_600_) == 0)
{
lean_object* v_r_601_; lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_626_; 
v_r_601_ = lean_ctor_get(v_impl_515_, 4);
v_k_602_ = lean_ctor_get(v_impl_515_, 1);
v_v_603_ = lean_ctor_get(v_impl_515_, 2);
v_isSharedCheck_626_ = !lean_is_exclusive(v_impl_515_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; lean_object* v_unused_628_; 
v_unused_627_ = lean_ctor_get(v_impl_515_, 3);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_impl_515_, 0);
lean_dec(v_unused_628_);
v___x_605_ = v_impl_515_;
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_r_601_);
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_dec(v_impl_515_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_k_607_; lean_object* v_v_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_622_; 
v_k_607_ = lean_ctor_get(v_l_600_, 1);
v_v_608_ = lean_ctor_get(v_l_600_, 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v_l_600_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_623_ = lean_ctor_get(v_l_600_, 4);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_l_600_, 3);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_l_600_, 0);
lean_dec(v_unused_625_);
v___x_610_ = v_l_600_;
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_v_608_);
lean_inc(v_k_607_);
lean_dec(v_l_600_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_601_, 2);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 4, v_r_601_);
lean_ctor_set(v___x_610_, 3, v_r_601_);
lean_ctor_set(v___x_610_, 2, v_v_368_);
lean_ctor_set(v___x_610_, 1, v_k_367_);
lean_ctor_set(v___x_610_, 0, v___x_516_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_r_601_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_r_601_);
v___x_614_ = v_reuseFailAlloc_621_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
lean_inc(v_r_601_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 3, v_r_601_);
lean_ctor_set(v___x_605_, 0, v___x_516_);
v___x_616_ = v___x_605_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_r_601_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_r_601_);
v___x_616_ = v_reuseFailAlloc_620_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_616_);
lean_ctor_set(v___x_372_, 3, v___x_614_);
lean_ctor_set(v___x_372_, 2, v_v_608_);
lean_ctor_set(v___x_372_, 1, v_k_607_);
lean_ctor_set(v___x_372_, 0, v___x_612_);
v___x_618_ = v___x_372_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_k_607_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_v_608_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
else
{
lean_object* v_r_629_; 
v_r_629_ = lean_ctor_get(v_impl_515_, 4);
lean_inc(v_r_629_);
if (lean_obj_tag(v_r_629_) == 0)
{
lean_object* v_k_630_; lean_object* v_v_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_642_; 
v_k_630_ = lean_ctor_get(v_impl_515_, 1);
v_v_631_ = lean_ctor_get(v_impl_515_, 2);
v_isSharedCheck_642_ = !lean_is_exclusive(v_impl_515_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_643_ = lean_ctor_get(v_impl_515_, 4);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_impl_515_, 3);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_impl_515_, 0);
lean_dec(v_unused_645_);
v___x_633_ = v_impl_515_;
v_isShared_634_ = v_isSharedCheck_642_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_v_631_);
lean_inc(v_k_630_);
lean_dec(v_impl_515_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_642_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(3u);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_l_600_);
lean_ctor_set(v___x_633_, 2, v_v_368_);
lean_ctor_set(v___x_633_, 1, v_k_367_);
lean_ctor_set(v___x_633_, 0, v___x_516_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_l_600_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v_l_600_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_r_629_);
lean_ctor_set(v___x_372_, 3, v___x_637_);
lean_ctor_set(v___x_372_, 2, v_v_631_);
lean_ctor_set(v___x_372_, 1, v_k_630_);
lean_ctor_set(v___x_372_, 0, v___x_635_);
v___x_639_ = v___x_372_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_k_630_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_v_631_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v_r_629_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(2u);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_impl_515_);
lean_ctor_set(v___x_372_, 3, v_r_629_);
lean_ctor_set(v___x_372_, 0, v___x_646_);
v___x_648_ = v___x_372_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_impl_515_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
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
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_k_363_);
lean_ctor_set(v___x_652_, 2, v_v_364_);
lean_ctor_set(v___x_652_, 3, v_t_365_);
lean_ctor_set(v___x_652_, 4, v_t_365_);
return v___x_652_;
}
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_box(1);
v___x_654_ = l_Lake_LeanExe_defaultFacetConfig;
v___x_655_ = l_Lake_LeanExe_defaultFacet;
v___x_656_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_655_, v___x_654_, v___x_653_);
return v___x_656_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__0, &l_Lake_LeanExe_initFacetConfigs___closed__0_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__0);
v___x_658_ = l_Lake_LeanExe_exeFacetConfig;
v___x_659_ = l_Lake_LeanExe_exeFacet;
v___x_660_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v___x_659_, v___x_658_, v___x_657_);
return v___x_660_;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs(void){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__1, &l_Lake_LeanExe_initFacetConfigs___closed__1_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__1);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object* v_00_u03b2_662_, lean_object* v_k_663_, lean_object* v_v_664_, lean_object* v_t_665_, lean_object* v_hl_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_663_, v_v_664_, v_t_665_);
return v___x_667_;
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
