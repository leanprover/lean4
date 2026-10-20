// Lean compiler output
// Module: Std.Http.Data.Extensions
// Imports: public import Init.Dynamic public import Init.Data.String.Basic public import Std.Data.TreeMap import Init.Data.String.Compare
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
uint8_t lean_string_compare(lean_object*, lean_object*);
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
v___x_11_ = lean_string_compare(v_str_7_, v_str_9_);
return v___x_11_;
}
else
{
return v___x_10_;
}
}
default: 
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_2_) == 2)
{
lean_object* v_pre_13_; lean_object* v_i_14_; lean_object* v_pre_15_; lean_object* v_i_16_; uint8_t v___x_17_; 
v_pre_13_ = lean_ctor_get(v_x_1_, 0);
v_i_14_ = lean_ctor_get(v_x_1_, 1);
v_pre_15_ = lean_ctor_get(v_x_2_, 0);
v_i_16_ = lean_ctor_get(v_x_2_, 1);
v___x_17_ = l_Std_Http_Extensions_compareName(v_pre_13_, v_pre_15_);
if (v___x_17_ == 1)
{
uint8_t v___x_18_; 
v___x_18_ = lean_nat_dec_lt(v_i_14_, v_i_16_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_eq(v_i_14_, v_i_16_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = 2;
return v___x_20_;
}
else
{
return v___x_17_;
}
}
else
{
uint8_t v___x_21_; 
v___x_21_ = 0;
return v___x_21_;
}
}
else
{
return v___x_17_;
}
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 2;
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Std_Http_Extensions_compareName(v_x_23_, v_x_24_);
lean_dec(v_x_24_);
lean_dec(v_x_23_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions_default(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(1);
return v___x_27_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_box(1);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Http_Extensions_empty(void){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(1);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get___redArg(lean_object* v_x_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(v_inst_32_);
v___x_34_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_33_, v_x_31_, v_inst_32_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; 
lean_dec(v_inst_32_);
v___x_35_ = lean_box(0);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_37_; 
v_val_36_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v___x_34_, 1);
v___x_37_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_36_, v_inst_32_);
lean_dec(v_inst_32_);
lean_dec(v_val_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get(lean_object* v_x_38_, lean_object* v_00_u03b1_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(v_inst_40_);
v___x_42_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_41_, v_x_38_, v_inst_40_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v___x_43_; 
lean_dec(v_inst_40_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
else
{
lean_object* v_val_44_; lean_object* v___x_45_; 
v_val_44_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v___x_42_, 1);
v___x_45_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_44_, v_inst_40_);
lean_dec(v_inst_40_);
lean_dec(v_val_44_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert___redArg(lean_object* v_x_46_, lean_object* v_inst_47_, lean_object* v_data_48_){
_start:
{
lean_object* v_dyn_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_dyn_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_49_, 0, v_inst_47_);
lean_ctor_set(v_dyn_49_, 1, v_data_48_);
v___x_50_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_51_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_49_);
v___x_52_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_50_, v___x_51_, v_dyn_49_, v_x_46_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert(lean_object* v_00_u03b1_53_, lean_object* v_x_54_, lean_object* v_inst_55_, lean_object* v_data_56_){
_start:
{
lean_object* v_dyn_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_dyn_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_57_, 0, v_inst_55_);
lean_ctor_set(v_dyn_57_, 1, v_data_56_);
v___x_58_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_59_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_57_);
v___x_60_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_58_, v___x_59_, v_dyn_57_, v_x_54_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove___redArg(lean_object* v_x_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_64_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_63_, v_inst_62_, v_x_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove(lean_object* v_x_65_, lean_object* v_00_u03b1_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_69_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_68_, v_inst_67_, v_x_65_);
return v___x_69_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains___redArg(lean_object* v_x_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_73_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_72_, v_inst_71_, v_x_70_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___redArg___boxed(lean_object* v_x_74_, lean_object* v_inst_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Std_Http_Extensions_contains___redArg(v_x_74_, v_inst_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Extensions_contains(lean_object* v_x_78_, lean_object* v_00_u03b1_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_82_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_81_, v_inst_80_, v_x_78_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___boxed(lean_object* v_x_83_, lean_object* v_00_u03b1_84_, lean_object* v_inst_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Http_Extensions_contains(v_x_83_, v_00_u03b1_84_, v_inst_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Compare(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Extensions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Compare(builtin);
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
lean_object* initialize_Init_Data_String_Compare(uint8_t builtin);
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
res = initialize_Init_Data_String_Compare(builtin);
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
