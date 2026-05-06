// Lean compiler output
// Module: Std.Http.Data.Extensions
// Imports: public import Init.Dynamic public import Init.Data.String.Basic public import Std.Data.TreeMap
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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Extensions_compareName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedExtensions_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedExtensions;
LEAN_EXPORT lean_object* l_Std_Http_Extensions_empty;
static const lean_closure_object l_Std_Http_Extensions_get___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Extensions_get___redArg___closed__0 = (const lean_object*)&l_Std_Http_Extensions_get___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Extensions_compareName(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_2_))
{
case 0:
{
uint8_t v___x_5_; 
v___x_5_ = 2;
return v___x_5_;
}
case 1:
{
lean_object* v_pre_6_; lean_object* v_str_7_; lean_object* v_pre_8_; lean_object* v_str_9_; uint8_t v___x_10_; 
v_pre_6_ = lean_ctor_get(v_x_1_, 0);
v_str_7_ = lean_ctor_get(v_x_1_, 1);
v_pre_8_ = lean_ctor_get(v_x_2_, 0);
v_str_9_ = lean_ctor_get(v_x_2_, 1);
v___x_10_ = l_Std_Http_Extensions_compareName(v_pre_6_, v_pre_8_);
if (v___x_10_ == 1)
{
uint8_t v___x_11_; 
v___x_11_ = lean_string_dec_lt(v_str_7_, v_str_9_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; 
v___x_12_ = lean_string_dec_eq(v_str_7_, v_str_9_);
if (v___x_12_ == 0)
{
uint8_t v___x_13_; 
v___x_13_ = 2;
return v___x_13_;
}
else
{
return v___x_10_;
}
}
else
{
uint8_t v___x_14_; 
v___x_14_ = 0;
return v___x_14_;
}
}
else
{
return v___x_10_;
}
}
default: 
{
uint8_t v___x_15_; 
v___x_15_ = 0;
return v___x_15_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_2_) == 2)
{
lean_object* v_pre_16_; lean_object* v_i_17_; lean_object* v_pre_18_; lean_object* v_i_19_; uint8_t v___x_20_; 
v_pre_16_ = lean_ctor_get(v_x_1_, 0);
v_i_17_ = lean_ctor_get(v_x_1_, 1);
v_pre_18_ = lean_ctor_get(v_x_2_, 0);
v_i_19_ = lean_ctor_get(v_x_2_, 1);
v___x_20_ = l_Std_Http_Extensions_compareName(v_pre_16_, v_pre_18_);
if (v___x_20_ == 1)
{
uint8_t v___x_21_; 
v___x_21_ = lean_nat_dec_lt(v_i_17_, v_i_19_);
if (v___x_21_ == 0)
{
uint8_t v___x_22_; 
v___x_22_ = lean_nat_dec_eq(v_i_17_, v_i_19_);
if (v___x_22_ == 0)
{
uint8_t v___x_23_; 
v___x_23_ = 2;
return v___x_23_;
}
else
{
return v___x_20_;
}
}
else
{
uint8_t v___x_24_; 
v___x_24_ = 0;
return v___x_24_;
}
}
else
{
return v___x_20_;
}
}
else
{
uint8_t v___x_25_; 
v___x_25_ = 2;
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Std_Http_Extensions_compareName(v_x_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec(v_x_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions_default(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(1);
return v___x_30_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(1);
return v___x_31_;
}
}
static lean_object* _init_l_Std_Http_Extensions_empty(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(1);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get___redArg(lean_object* v_x_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(v_inst_35_);
v___x_37_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_36_, v_x_34_, v_inst_35_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v___x_38_; 
lean_dec(v_inst_35_);
v___x_38_ = lean_box(0);
return v___x_38_;
}
else
{
lean_object* v_val_39_; lean_object* v___x_40_; 
v_val_39_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_val_39_);
lean_dec_ref(v___x_37_);
v___x_40_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_39_, v_inst_35_);
lean_dec(v_inst_35_);
lean_dec(v_val_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get(lean_object* v_x_41_, lean_object* v_00_u03b1_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(v_inst_43_);
v___x_45_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_44_, v_x_41_, v_inst_43_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v___x_46_; 
lean_dec(v_inst_43_);
v___x_46_ = lean_box(0);
return v___x_46_;
}
else
{
lean_object* v_val_47_; lean_object* v___x_48_; 
v_val_47_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_val_47_);
lean_dec_ref(v___x_45_);
v___x_48_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_47_, v_inst_43_);
lean_dec(v_inst_43_);
lean_dec(v_val_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert___redArg(lean_object* v_x_49_, lean_object* v_inst_50_, lean_object* v_data_51_){
_start:
{
lean_object* v_dyn_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_dyn_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_52_, 0, v_inst_50_);
lean_ctor_set(v_dyn_52_, 1, v_data_51_);
v___x_53_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_54_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_52_);
v___x_55_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_53_, v___x_54_, v_dyn_52_, v_x_49_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert(lean_object* v_00_u03b1_56_, lean_object* v_x_57_, lean_object* v_inst_58_, lean_object* v_data_59_){
_start:
{
lean_object* v_dyn_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_dyn_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_60_, 0, v_inst_58_);
lean_ctor_set(v_dyn_60_, 1, v_data_59_);
v___x_61_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_62_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_60_);
v___x_63_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_61_, v___x_62_, v_dyn_60_, v_x_57_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove___redArg(lean_object* v_x_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_67_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_66_, v_inst_65_, v_x_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove(lean_object* v_x_68_, lean_object* v_00_u03b1_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_72_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_71_, v_inst_70_, v_x_68_);
return v___x_72_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains___redArg(lean_object* v_x_73_, lean_object* v_inst_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_76_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_75_, v_inst_74_, v_x_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___redArg___boxed(lean_object* v_x_77_, lean_object* v_inst_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Std_Http_Extensions_contains___redArg(v_x_77_, v_inst_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains(lean_object* v_x_81_, lean_object* v_00_u03b1_82_, lean_object* v_inst_83_){
_start:
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_85_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_84_, v_inst_83_, v_x_81_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___boxed(lean_object* v_x_86_, lean_object* v_00_u03b1_87_, lean_object* v_inst_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_Http_Extensions_contains(v_x_86_, v_00_u03b1_87_, v_inst_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Extensions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instInhabitedExtensions_default = _init_l_Std_Http_instInhabitedExtensions_default();
lean_mark_persistent(l_Std_Http_instInhabitedExtensions_default);
l_Std_Http_instInhabitedExtensions = _init_l_Std_Http_instInhabitedExtensions();
lean_mark_persistent(l_Std_Http_instInhabitedExtensions);
l_Std_Http_Extensions_empty = _init_l_Std_Http_Extensions_empty();
lean_mark_persistent(l_Std_Http_Extensions_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Extensions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Extensions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Extensions(builtin);
}
#ifdef __cplusplus
}
#endif
