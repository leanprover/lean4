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
LEAN_EXPORT uint8_t lean_is_private_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateNameExport___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object*);
LEAN_EXPORT lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_private_prefix(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object* v_x_12_){
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
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Lean_isPrivateName(v_x_20_);
lean_dec(v_x_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t lean_is_private_name(lean_object* v_n_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l_Lean_isPrivateName(v_n_23_);
lean_dec(v_n_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivateNameExport___boxed(lean_object* v_n_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = lean_is_private_name(v_n_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(lean_object* v_n_28_){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = ((lean_object*)(l_Lean_privateHeader));
v___x_30_ = lean_name_eq(v_n_28_, v___x_29_);
if (v___x_30_ == 0)
{
if (lean_obj_tag(v_n_28_) == 1)
{
lean_object* v_pre_31_; 
v_pre_31_ = lean_ctor_get(v_n_28_, 0);
v_n_28_ = v_pre_31_;
goto _start;
}
else
{
return v___x_30_;
}
}
else
{
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go___boxed(lean_object* v_n_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_n_33_);
lean_dec(v_n_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix(lean_object* v_n_36_){
_start:
{
if (lean_obj_tag(v_n_36_) == 2)
{
lean_object* v_pre_37_; lean_object* v_i_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_pre_37_ = lean_ctor_get(v_n_36_, 0);
v_i_38_ = lean_ctor_get(v_n_36_, 1);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = lean_nat_dec_eq(v_i_38_, v___x_39_);
if (v___x_40_ == 0)
{
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_pre_37_);
return v___x_41_;
}
}
else
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object* v_n_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Lean_isPrivatePrefix(v_n_43_);
lean_dec(v_n_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object* v_n_46_){
_start:
{
switch(lean_obj_tag(v_n_46_))
{
case 0:
{
return v_n_46_;
}
case 1:
{
lean_object* v_pre_47_; lean_object* v_str_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_pre_47_ = lean_ctor_get(v_n_46_, 0);
lean_inc(v_pre_47_);
v_str_48_ = lean_ctor_get(v_n_46_, 1);
lean_inc_ref(v_str_48_);
lean_dec_ref(v_n_46_);
v___x_49_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_47_);
v___x_50_ = l_Lean_Name_str___override(v___x_49_, v_str_48_);
return v___x_50_;
}
default: 
{
lean_object* v_pre_51_; lean_object* v_i_52_; uint8_t v___x_53_; 
v_pre_51_ = lean_ctor_get(v_n_46_, 0);
lean_inc(v_pre_51_);
v_i_52_ = lean_ctor_get(v_n_46_, 1);
lean_inc(v_i_52_);
v___x_53_ = l_Lean_isPrivatePrefix(v_n_46_);
lean_dec_ref(v_n_46_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_pre_51_);
v___x_55_ = l_Lean_Name_num___override(v___x_54_, v_i_52_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; 
lean_dec(v_i_52_);
lean_dec(v_pre_51_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_private_to_user_name(lean_object* v_n_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = l_Lean_isPrivateName(v_n_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; 
lean_dec(v_n_57_);
v___x_59_ = lean_box(0);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_57_);
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object* v_n_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = l_Lean_isPrivateName(v_n_62_);
if (v___x_63_ == 0)
{
return v_n_62_;
}
else
{
lean_object* v___x_64_; 
v___x_64_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(v_n_62_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux(lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 1)
{
lean_object* v_pre_66_; 
v_pre_66_ = lean_ctor_get(v_x_65_, 0);
v_x_65_ = v_pre_66_;
goto _start;
}
else
{
lean_inc(v_x_65_);
return v_x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privatePrefixAux___boxed(lean_object* v_x_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_x_68_);
lean_dec(v_x_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lean_private_prefix(lean_object* v_n_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = l_Lean_isPrivateName(v_n_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec(v_n_70_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = l___private_Lean_PrivateName_0__Lean_privatePrefixAux(v_n_70_);
lean_dec(v_n_70_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrivateName(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
