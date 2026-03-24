// Lean compiler output
// Module: Lake.Config.Kinds
// Imports: public import Init.Prelude
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_keyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l_Lake_Package_keyword___closed__0 = (const lean_object*)&l_Lake_Package_keyword___closed__0_value;
static const lean_ctor_object l_Lake_Package_keyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_keyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_object* l_Lake_Package_keyword___closed__1 = (const lean_object*)&l_Lake_Package_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_keyword = (const lean_object*)&l_Lake_Package_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Package_facetKind = (const lean_object*)&l_Lake_Package_keyword___closed__1_value;
static const lean_string_object l_Lake_Module_keyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lake_Module_keyword___closed__0 = (const lean_object*)&l_Lake_Module_keyword___closed__0_value;
static const lean_ctor_object l_Lake_Module_keyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Module_keyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_object* l_Lake_Module_keyword___closed__1 = (const lean_object*)&l_Lake_Module_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_keyword = (const lean_object*)&l_Lake_Module_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Module_facetKind = (const lean_object*)&l_Lake_Module_keyword___closed__1_value;
static const lean_string_object l_Lake_LeanLib_keyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_LeanLib_keyword___closed__0 = (const lean_object*)&l_Lake_LeanLib_keyword___closed__0_value;
static const lean_ctor_object l_Lake_LeanLib_keyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_keyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake_LeanLib_keyword___closed__1 = (const lean_object*)&l_Lake_LeanLib_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_keyword = (const lean_object*)&l_Lake_LeanLib_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_facetKind = (const lean_object*)&l_Lake_LeanLib_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanLib_configKind = (const lean_object*)&l_Lake_LeanLib_keyword___closed__1_value;
static const lean_string_object l_Lake_LeanExe_keyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_exe"};
static const lean_object* l_Lake_LeanExe_keyword___closed__0 = (const lean_object*)&l_Lake_LeanExe_keyword___closed__0_value;
static const lean_ctor_object l_Lake_LeanExe_keyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanExe_keyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 234, 10, 11, 117, 216, 237, 146)}};
static const lean_object* l_Lake_LeanExe_keyword___closed__1 = (const lean_object*)&l_Lake_LeanExe_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanExe_keyword = (const lean_object*)&l_Lake_LeanExe_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanExe_facetKind = (const lean_object*)&l_Lake_LeanExe_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_LeanExe_configKind = (const lean_object*)&l_Lake_LeanExe_keyword___closed__1_value;
static const lean_string_object l_Lake_ExternLib_keyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extern_lib"};
static const lean_object* l_Lake_ExternLib_keyword___closed__0 = (const lean_object*)&l_Lake_ExternLib_keyword___closed__0_value;
static const lean_ctor_object l_Lake_ExternLib_keyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_ExternLib_keyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 249, 245, 64, 44, 199, 117, 160)}};
static const lean_object* l_Lake_ExternLib_keyword___closed__1 = (const lean_object*)&l_Lake_ExternLib_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_ExternLib_keyword = (const lean_object*)&l_Lake_ExternLib_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_ExternLib_facetKind = (const lean_object*)&l_Lake_ExternLib_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_ExternLib_configKind = (const lean_object*)&l_Lake_ExternLib_keyword___closed__1_value;
static const lean_string_object l_Lake_InputFile_keyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "input_file"};
static const lean_object* l_Lake_InputFile_keyword___closed__0 = (const lean_object*)&l_Lake_InputFile_keyword___closed__0_value;
static const lean_ctor_object l_Lake_InputFile_keyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_InputFile_keyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 212, 171, 164, 114, 171, 114, 56)}};
static const lean_object* l_Lake_InputFile_keyword___closed__1 = (const lean_object*)&l_Lake_InputFile_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputFile_keyword = (const lean_object*)&l_Lake_InputFile_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputFile_facetKind = (const lean_object*)&l_Lake_InputFile_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputFile_configKind = (const lean_object*)&l_Lake_InputFile_keyword___closed__1_value;
static const lean_string_object l_Lake_InputDir_keyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "input_dir"};
static const lean_object* l_Lake_InputDir_keyword___closed__0 = (const lean_object*)&l_Lake_InputDir_keyword___closed__0_value;
static const lean_ctor_object l_Lake_InputDir_keyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_InputDir_keyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 20, 59, 254, 237, 234, 192, 134)}};
static const lean_object* l_Lake_InputDir_keyword___closed__1 = (const lean_object*)&l_Lake_InputDir_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputDir_keyword = (const lean_object*)&l_Lake_InputDir_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputDir_facetKind = (const lean_object*)&l_Lake_InputDir_keyword___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_InputDir_configKind = (const lean_object*)&l_Lake_InputDir_keyword___closed__1_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Package"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LeanLib"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LeanExe"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ExternLib"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "InputFile"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6_value;
static const lean_string_object l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "InputDir"};
static const lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7 = (const lean_object*)&l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(lean_object* v_ns_49_){
_start:
{
switch(lean_obj_tag(v_ns_49_))
{
case 0:
{
return v_ns_49_;
}
case 1:
{
lean_object* v_pre_50_; 
v_pre_50_ = lean_ctor_get(v_ns_49_, 0);
switch(lean_obj_tag(v_pre_50_))
{
case 0:
{
return v_pre_50_;
}
case 1:
{
lean_object* v_pre_51_; 
v_pre_51_ = lean_ctor_get(v_pre_50_, 0);
if (lean_obj_tag(v_pre_51_) == 0)
{
lean_object* v_str_52_; lean_object* v_str_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_str_52_ = lean_ctor_get(v_ns_49_, 1);
v_str_53_ = lean_ctor_get(v_pre_50_, 1);
v___x_54_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__0));
v___x_55_ = lean_string_dec_eq(v_str_53_, v___x_54_);
if (v___x_55_ == 0)
{
return v_pre_51_;
}
else
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__1));
v___x_57_ = lean_string_dec_eq(v_str_52_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__2));
v___x_59_ = lean_string_dec_eq(v_str_52_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__3));
v___x_61_ = lean_string_dec_eq(v_str_52_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__4));
v___x_63_ = lean_string_dec_eq(v_str_52_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__5));
v___x_65_ = lean_string_dec_eq(v_str_52_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__6));
v___x_67_ = lean_string_dec_eq(v_str_52_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = ((lean_object*)(l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___closed__7));
v___x_69_ = lean_string_dec_eq(v_str_52_, v___x_68_);
if (v___x_69_ == 0)
{
return v_pre_51_;
}
else
{
lean_object* v___x_70_; 
v___x_70_ = ((lean_object*)(l_Lake_InputDir_keyword));
return v___x_70_;
}
}
else
{
lean_object* v___x_71_; 
v___x_71_ = ((lean_object*)(l_Lake_InputFile_keyword));
return v___x_71_;
}
}
else
{
lean_object* v___x_72_; 
v___x_72_ = ((lean_object*)(l_Lake_ExternLib_keyword));
return v___x_72_;
}
}
else
{
lean_object* v___x_73_; 
v___x_73_ = ((lean_object*)(l_Lake_LeanExe_keyword));
return v___x_73_;
}
}
else
{
lean_object* v___x_74_; 
v___x_74_ = ((lean_object*)(l_Lake_LeanLib_keyword___closed__1));
return v___x_74_;
}
}
else
{
lean_object* v___x_75_; 
v___x_75_ = ((lean_object*)(l_Lake_Module_keyword));
return v___x_75_;
}
}
else
{
lean_object* v___x_76_; 
v___x_76_ = ((lean_object*)(l_Lake_Package_keyword));
return v___x_76_;
}
}
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
default: 
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
}
default: 
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace___boxed(lean_object* v_ns_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(v_ns_80_);
lean_dec(v_ns_80_);
return v_res_81_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Kinds(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Kinds(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Kinds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Kinds(builtin);
}
#ifdef __cplusplus
}
#endif
