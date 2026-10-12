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
uint8_t l_Std_Http_Extensions_compareName(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Std_Http_Extensions_compareName_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_26_;
v_res_26_ = l_Std_Http_Extensions_compareName(v_x_1_, v_x_2_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Std_Http_Extensions_compareName(v_x_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec(v_x_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions_default(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(1);
return v___x_31_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedExtensions(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(1);
return v___x_32_;
}
}
static lean_object* _init_l_Std_Http_Extensions_empty(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(1);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get___redArg(lean_object* v_x_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(v_inst_36_);
v___x_38_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_37_, v_x_35_, v_inst_36_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v___x_39_; 
lean_dec(v_inst_36_);
v___x_39_ = lean_box(0);
return v___x_39_;
}
else
{
lean_object* v_val_40_; lean_object* v___x_41_; 
v_val_40_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v___x_38_, 1);
v___x_41_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_40_, v_inst_36_);
lean_dec(v_inst_36_);
lean_dec(v_val_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_get(lean_object* v_x_42_, lean_object* v_00_u03b1_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
lean_inc(v_inst_44_);
v___x_46_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_45_, v_x_42_, v_inst_44_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v___x_47_; 
lean_dec(v_inst_44_);
v___x_47_ = lean_box(0);
return v___x_47_;
}
else
{
lean_object* v_val_48_; lean_object* v___x_49_; 
v_val_48_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_val_48_);
lean_dec_ref_known(v___x_46_, 1);
v___x_49_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_48_, v_inst_44_);
lean_dec(v_inst_44_);
lean_dec(v_val_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert___redArg(lean_object* v_x_50_, lean_object* v_inst_51_, lean_object* v_data_52_){
_start:
{
lean_object* v_dyn_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_dyn_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_53_, 0, v_inst_51_);
lean_ctor_set(v_dyn_53_, 1, v_data_52_);
v___x_54_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_55_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_53_);
v___x_56_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_54_, v___x_55_, v_dyn_53_, v_x_50_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_insert(lean_object* v_00_u03b1_57_, lean_object* v_x_58_, lean_object* v_inst_59_, lean_object* v_data_60_){
_start:
{
lean_object* v_dyn_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_dyn_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_61_, 0, v_inst_59_);
lean_ctor_set(v_dyn_61_, 1, v_data_60_);
v___x_62_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_63_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_61_);
v___x_64_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_62_, v___x_63_, v_dyn_61_, v_x_58_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove___redArg(lean_object* v_x_65_, lean_object* v_inst_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_68_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_67_, v_inst_66_, v_x_65_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_remove(lean_object* v_x_69_, lean_object* v_00_u03b1_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_73_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_72_, v_inst_71_, v_x_69_);
return v___x_73_;
}
}
uint8_t l_Std_Http_Extensions_contains___redArg(lean_object* v_x_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_77_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_76_, v_inst_75_, v_x_74_);
return v___x_77_;
}
}
LEAN_EXPORT void l_Std_Http_Extensions_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_74_ = stack[0].m_obj;
lean_object* v_inst_75_ = stack[1].m_obj;
uint8_t v_res_78_;
v_res_78_ = l_Std_Http_Extensions_contains___redArg(v_x_74_, v_inst_75_);
stack->m_num = v_res_78_;
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___redArg___boxed(lean_object* v_x_79_, lean_object* v_inst_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_Http_Extensions_contains___redArg(v_x_79_, v_inst_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
uint8_t l_Std_Http_Extensions_contains(lean_object* v_x_83_, lean_object* v_00_u03b1_84_, lean_object* v_inst_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l_Std_Http_Extensions_get___redArg___closed__0));
v___x_87_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_86_, v_inst_85_, v_x_83_);
return v___x_87_;
}
}
LEAN_EXPORT void l_Std_Http_Extensions_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_83_ = stack[0].m_obj;
lean_object* v_inst_85_ = stack[2].m_obj;
uint8_t v_res_88_;
v_res_88_ = l_Std_Http_Extensions_contains(v_x_83_, lean_box(0), v_inst_85_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Std_Http_Extensions_contains___boxed(lean_object* v_x_89_, lean_object* v_00_u03b1_90_, lean_object* v_inst_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Std_Http_Extensions_contains(v_x_89_, v_00_u03b1_90_, v_inst_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap(uint8_t builtin);
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
