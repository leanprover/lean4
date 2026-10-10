// Lean compiler output
// Module: Lean.PrivateName
// Imports: public import Init.Notation public import Init.Data.Option.Coe
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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_string_object l_Lean_privateHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l_Lean_privateHeader___closed__0 = (const lean_object*)&l_Lean_privateHeader___closed__0_value;
static const lean_ctor_object l_Lean_privateHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_privateHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l_Lean_privateHeader___closed__1 = (const lean_object*)&l_Lean_privateHeader___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_privateHeader = (const lean_object*)&l_Lean_privateHeader___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkPrivateNameCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_privateToUserName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_privatePrefix_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_privatePrefix_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateNameCore(lean_object* v_mainModule_5_, lean_object* v_n_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = ((lean_object*)(l_Lean_privateHeader));
v___x_8_ = l_Lean_Name_append(v___x_7_, v_mainModule_5_);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = l_Lean_Name_num___override(v___x_8_, v___x_9_);
v___x_11_ = l_Lean_Name_append(v___x_10_, v_n_6_);
return v___x_11_;
}
}
uint8_t l_Lean_isPrivateName(lean_object* v_x_12_){
_start:
{
switch(lean_obj_tag(v_x_12_))
{
case 0:
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
case 1:
{
lean_object* v_pre_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_pre_14_ = lean_ctor_get(v_x_12_, 0);
v___x_15_ = ((lean_object*)(l_Lean_privateHeader));
v___x_16_ = lean_name_eq(v_x_12_, v___x_15_);
if (v___x_16_ == 0)
{
v_x_12_ = v_pre_14_;
goto _start;
}
else
{
return v___x_16_;
}
}
default: 
{
lean_object* v_pre_18_; 
v_pre_18_ = lean_ctor_get(v_x_12_, 0);
v_x_12_ = v_pre_18_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Lean_isPrivateName_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_12_ = stack[0].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Lean_isPrivateName(v_x_12_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Lean_isPrivateName(v_x_21_);
lean_dec(v_x_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
uint8_t l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(lean_object* v_n_24_){
_start:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = ((lean_object*)(l_Lean_privateHeader));
v___x_26_ = lean_name_eq(v_n_24_, v___x_25_);
if (v___x_26_ == 0)
{
if (lean_obj_tag(v_n_24_) == 1)
{
lean_object* v_pre_27_; 
v_pre_27_ = lean_ctor_get(v_n_24_, 0);
v_n_24_ = v_pre_27_;
goto _start;
}
else
{
return v___x_26_;
}
}
else
{
return v___x_26_;
}
}
}
LEAN_EXPORT void l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_24_ = stack[0].m_obj;
uint8_t v_res_29_;
v_res_29_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_n_24_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go___boxed(lean_object* v_n_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_n_30_);
lean_dec(v_n_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
uint8_t l_Lean_isPrivatePrefix(lean_object* v_n_33_){
_start:
{
if (lean_obj_tag(v_n_33_) == 2)
{
lean_object* v_pre_34_; lean_object* v_i_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_pre_34_ = lean_ctor_get(v_n_33_, 0);
v_i_35_ = lean_ctor_get(v_n_33_, 1);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_dec_eq(v_i_35_, v___x_36_);
if (v___x_37_ == 0)
{
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_pre_34_);
return v___x_38_;
}
}
else
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
}
}
LEAN_EXPORT void l_Lean_isPrivatePrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_33_ = stack[0].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_Lean_isPrivatePrefix(v_n_33_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object* v_n_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Lean_isPrivatePrefix(v_n_41_);
lean_dec(v_n_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object* v_n_44_){
_start:
{
switch(lean_obj_tag(v_n_44_))
{
case 0:
{
return v_n_44_;
}
case 1:
{
lean_object* v_pre_45_; lean_object* v_str_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_pre_45_ = lean_ctor_get(v_n_44_, 0);
lean_inc(v_pre_45_);
v_str_46_ = lean_ctor_get(v_n_44_, 1);
lean_inc_ref(v_str_46_);
lean_dec_ref_known(v_n_44_, 2);
v___x_47_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_45_);
v___x_48_ = l_Lean_Name_str___override(v___x_47_, v_str_46_);
return v___x_48_;
}
default: 
{
lean_object* v_pre_49_; lean_object* v_i_50_; uint8_t v___x_51_; 
v_pre_49_ = lean_ctor_get(v_n_44_, 0);
lean_inc(v_pre_49_);
v_i_50_ = lean_ctor_get(v_n_44_, 1);
lean_inc(v_i_50_);
v___x_51_ = l_Lean_isPrivatePrefix(v_n_44_);
lean_dec_ref_known(v_n_44_, 2);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_49_);
v___x_53_ = l_Lean_Name_num___override(v___x_52_, v_i_50_);
return v___x_53_;
}
else
{
lean_object* v___x_54_; 
lean_dec(v_i_50_);
lean_dec(v_pre_49_);
v___x_54_ = lean_box(0);
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_privateToUserName_x3f(lean_object* v_n_55_){
_start:
{
uint8_t v___x_56_; 
v___x_56_ = l_Lean_isPrivateName(v_n_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec(v_n_55_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_55_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object* v_n_60_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = l_Lean_isPrivateName(v_n_60_);
if (v___x_61_ == 0)
{
return v_n_60_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_60_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux(lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_63_) == 1)
{
lean_object* v_pre_64_; 
v_pre_64_ = lean_ctor_get(v_x_63_, 0);
v_x_63_ = v_pre_64_;
goto _start;
}
else
{
lean_inc(v_x_63_);
return v_x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_x_66_);
lean_dec(v_x_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_privatePrefix_x3f(lean_object* v_n_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_isPrivateName(v_n_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_n_68_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_privatePrefix_x3f___boxed(lean_object* v_n_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_privatePrefix_x3f(v_n_73_);
lean_dec(v_n_73_);
return v_res_74_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrivateName(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PrivateName(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrivateName(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrivateName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PrivateName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PrivateName(builtin);
}
#ifdef __cplusplus
}
#endif
