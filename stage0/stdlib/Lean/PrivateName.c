// Lean compiler output
// Module: Lean.PrivateName
// Imports: public import Init.Notation public import Init.Data.Option.Coe import Init.SimpLemmas
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
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_string_object l_Lean_privateHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l_Lean_privateHeader___closed__0 = (const lean_object*)&l_Lean_privateHeader___closed__0_value;
static const lean_ctor_object l_Lean_privateHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_privateHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l_Lean_privateHeader___closed__1 = (const lean_object*)&l_Lean_privateHeader___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_privateHeader = (const lean_object*)&l_Lean_privateHeader___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkPrivateNameCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivateName_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivateName_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_privateToUserName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_privatePrefix_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateNameCore(lean_object* v_mainModule_5_, lean_object* v_n_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = ((lean_object*)(l_Lean_privateHeader));
v___x_8_ = l_Lean_Name_appendCore(v___x_7_, v_mainModule_5_);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = l_Lean_Name_num___override(v___x_8_, v___x_9_);
v___x_11_ = l_Lean_Name_appendCore(v___x_10_, v_n_6_);
lean_dec(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(lean_object* v_n_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_privateHeader));
v___x_14_ = lean_name_eq(v_n_12_, v___x_13_);
if (v___x_14_ == 0)
{
if (lean_obj_tag(v_n_12_) == 1)
{
lean_object* v_pre_15_; 
v_pre_15_ = lean_ctor_get(v_n_12_, 0);
v_n_12_ = v_pre_15_;
goto _start;
}
else
{
return v___x_14_;
}
}
else
{
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go___boxed(lean_object* v_n_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_n_17_);
lean_dec(v_n_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivatePrefix(lean_object* v_n_20_){
_start:
{
if (lean_obj_tag(v_n_20_) == 2)
{
lean_object* v_pre_21_; lean_object* v_i_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v_pre_21_ = lean_ctor_get(v_n_20_, 0);
v_i_22_ = lean_ctor_get(v_n_20_, 1);
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_nat_dec_eq(v_i_22_, v___x_23_);
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_pre_21_);
return v___x_25_;
}
}
else
{
uint8_t v___x_26_; 
v___x_26_ = 0;
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivatePrefix___boxed(lean_object* v_n_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Lean_isPrivatePrefix(v_n_27_);
lean_dec(v_n_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPrivateName(lean_object* v_n_30_){
_start:
{
switch(lean_obj_tag(v_n_30_))
{
case 0:
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
case 1:
{
lean_object* v_pre_32_; 
v_pre_32_ = lean_ctor_get(v_n_30_, 0);
v_n_30_ = v_pre_32_;
goto _start;
}
default: 
{
lean_object* v_pre_34_; lean_object* v_i_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_pre_34_ = lean_ctor_get(v_n_30_, 0);
v_i_35_ = lean_ctor_get(v_n_30_, 1);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_dec_eq(v_i_35_, v___x_36_);
if (v___x_37_ == 0)
{
v_n_30_ = v_pre_34_;
goto _start;
}
else
{
uint8_t v___x_39_; 
v___x_39_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_pre_34_);
if (v___x_39_ == 0)
{
v_n_30_ = v_pre_34_;
goto _start;
}
else
{
return v___x_39_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPrivateName___boxed(lean_object* v_n_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Lean_isPrivateName(v_n_41_);
lean_dec(v_n_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivateName_match__1_splitter___redArg(lean_object* v_n_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
_start:
{
switch(lean_obj_tag(v_n_44_))
{
case 0:
{
lean_object* v___x_48_; 
lean_dec(v_h__2_46_);
lean_dec(v_h__1_45_);
v___x_48_ = lean_apply_3(v_h__3_47_, v_n_44_, lean_box(0), lean_box(0));
return v___x_48_;
}
case 1:
{
lean_object* v_pre_49_; lean_object* v_str_50_; lean_object* v___x_51_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__2_46_);
v_pre_49_ = lean_ctor_get(v_n_44_, 0);
lean_inc(v_pre_49_);
v_str_50_ = lean_ctor_get(v_n_44_, 1);
lean_inc_ref(v_str_50_);
lean_dec_ref_known(v_n_44_, 2);
v___x_51_ = lean_apply_2(v_h__1_45_, v_pre_49_, v_str_50_);
return v___x_51_;
}
default: 
{
lean_object* v_pre_52_; lean_object* v_i_53_; lean_object* v___x_54_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__1_45_);
v_pre_52_ = lean_ctor_get(v_n_44_, 0);
lean_inc(v_pre_52_);
v_i_53_ = lean_ctor_get(v_n_44_, 1);
lean_inc(v_i_53_);
lean_dec_ref_known(v_n_44_, 2);
v___x_54_ = lean_apply_2(v_h__2_46_, v_pre_52_, v_i_53_);
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_isPrivateName_match__1_splitter(lean_object* v_motive_55_, lean_object* v_n_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_, lean_object* v_h__3_59_){
_start:
{
switch(lean_obj_tag(v_n_56_))
{
case 0:
{
lean_object* v___x_60_; 
lean_dec(v_h__2_58_);
lean_dec(v_h__1_57_);
v___x_60_ = lean_apply_3(v_h__3_59_, v_n_56_, lean_box(0), lean_box(0));
return v___x_60_;
}
case 1:
{
lean_object* v_pre_61_; lean_object* v_str_62_; lean_object* v___x_63_; 
lean_dec(v_h__3_59_);
lean_dec(v_h__2_58_);
v_pre_61_ = lean_ctor_get(v_n_56_, 0);
lean_inc(v_pre_61_);
v_str_62_ = lean_ctor_get(v_n_56_, 1);
lean_inc_ref(v_str_62_);
lean_dec_ref_known(v_n_56_, 2);
v___x_63_ = lean_apply_2(v_h__1_57_, v_pre_61_, v_str_62_);
return v___x_63_;
}
default: 
{
lean_object* v_pre_64_; lean_object* v_i_65_; lean_object* v___x_66_; 
lean_dec(v_h__3_59_);
lean_dec(v_h__1_57_);
v_pre_64_ = lean_ctor_get(v_n_56_, 0);
lean_inc(v_pre_64_);
v_i_65_ = lean_ctor_get(v_n_56_, 1);
lean_inc(v_i_65_);
lean_dec_ref_known(v_n_56_, 2);
v___x_66_ = lean_apply_2(v_h__2_58_, v_pre_64_, v_i_65_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux___redArg(lean_object* v_n_67_){
_start:
{
if (lean_obj_tag(v_n_67_) == 1)
{
lean_object* v_pre_68_; lean_object* v_str_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_pre_68_ = lean_ctor_get(v_n_67_, 0);
lean_inc(v_pre_68_);
v_str_69_ = lean_ctor_get(v_n_67_, 1);
lean_inc_ref(v_str_69_);
lean_dec_ref_known(v_n_67_, 2);
v___x_70_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux___redArg(v_pre_68_);
v___x_71_ = l_Lean_Name_str___override(v___x_70_, v_str_69_);
return v___x_71_;
}
else
{
lean_object* v_pre_72_; lean_object* v_i_73_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_pre_72_ = lean_ctor_get(v_n_67_, 0);
lean_inc(v_pre_72_);
v_i_73_ = lean_ctor_get(v_n_67_, 1);
lean_inc(v_i_73_);
lean_dec_ref_known(v_n_67_, 2);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_nat_dec_eq(v_i_73_, v___x_77_);
if (v___x_78_ == 0)
{
goto v___jp_74_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_pre_72_);
if (v___x_79_ == 0)
{
goto v___jp_74_;
}
else
{
lean_object* v___x_80_; 
lean_dec(v_i_73_);
lean_dec(v_pre_72_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
v___jp_74_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux___redArg(v_pre_72_);
v___x_76_ = l_Lean_Name_num___override(v___x_75_, v_i_73_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrivateName_0__Lean_privateToUserNameAux(lean_object* v_n_81_, lean_object* v_h_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux___redArg(v_n_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_privateToUserName_x3f(lean_object* v_n_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = l_Lean_isPrivateName(v_n_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v_n_84_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux___redArg(v_n_84_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_privateToUserName(lean_object* v_n_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Lean_isPrivateName(v_n_89_);
if (v___x_90_ == 0)
{
return v_n_89_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_PrivateName_0__Lean_privateToUserNameAux___redArg(v_n_89_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_privatePrefix_x3f(lean_object* v_n_92_){
_start:
{
switch(lean_obj_tag(v_n_92_))
{
case 0:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
return v___x_93_;
}
case 1:
{
lean_object* v_pre_94_; 
v_pre_94_ = lean_ctor_get(v_n_92_, 0);
lean_inc(v_pre_94_);
lean_dec_ref_known(v_n_92_, 2);
v_n_92_ = v_pre_94_;
goto _start;
}
default: 
{
lean_object* v_pre_96_; lean_object* v_i_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_pre_96_ = lean_ctor_get(v_n_92_, 0);
v_i_97_ = lean_ctor_get(v_n_92_, 1);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_eq(v_i_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_inc(v_pre_96_);
lean_dec_ref_known(v_n_92_, 2);
v_n_92_ = v_pre_96_;
goto _start;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = l___private_Lean_PrivateName_0__Lean_isPrivatePrefix_go(v_pre_96_);
if (v___x_101_ == 0)
{
lean_inc(v_pre_96_);
lean_dec_ref_known(v_n_92_, 2);
v_n_92_ = v_pre_96_;
goto _start;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_n_92_);
return v___x_103_;
}
}
}
}
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
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
res = runtime_initialize_Init_SimpLemmas(builtin);
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
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
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
res = initialize_Init_SimpLemmas(builtin);
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
