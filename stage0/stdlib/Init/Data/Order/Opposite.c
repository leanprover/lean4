// Lean compiler output
// Module: Init.Data.Order.Opposite
// Imports: public import Init.Data.Order.ClassesExtra public import Init.Data.Order.Classes import Init.Data.Order.FactoriesExtra import Init.Data.Order.Lemmas
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
LEAN_EXPORT lean_object* l_LE_opposite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LT_opposite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Min_oppositeMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Max_oppositeMin(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_opposite(lean_object* v_00_u03b1_1_, lean_object* v_le_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_LT_opposite(lean_object* v_00_u03b1_4_, lean_object* v_lt_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg___lam__0(lean_object* v_min_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_2(v_min_7_, v_a_8_, v_b_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg(lean_object* v_min_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(v___f_12_, 0, v_min_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax(lean_object* v_00_u03b1_13_, lean_object* v_min_14_){
_start:
{
lean_object* v___f_15_; 
v___f_15_ = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(v___f_15_, 0, v_min_14_);
return v___f_15_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg___lam__0(lean_object* v_max_16_, lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_apply_2(v_max_16_, v_a_17_, v_b_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg(lean_object* v_max_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_21_, 0, v_max_20_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin(lean_object* v_00_u03b1_22_, lean_object* v_max_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_24_, 0, v_max_23_);
return v___f_24_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(lean_object* v_id_25_, lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_apply_2(v_id_25_, v_b_27_, v_a_26_);
v___x_29_ = lean_unbox(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(lean_object* v_id_30_, lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(v_id_30_, v_a_31_, v_b_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite(lean_object* v_00_u03b1_35_, lean_object* v_i_36_, lean_object* v_id_37_, lean_object* v_a_38_, lean_object* v_b_39_){
_start:
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_apply_2(v_id_37_, v_b_39_, v_a_38_);
v___x_41_ = lean_unbox(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(lean_object* v_00_u03b1_42_, lean_object* v_i_43_, lean_object* v_id_44_, lean_object* v_a_45_, lean_object* v_b_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite(v_00_u03b1_42_, v_i_43_, v_id_44_, v_a_45_, v_b_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(lean_object* v_id_49_, lean_object* v_a_50_, lean_object* v_b_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_apply_2(v_id_49_, v_b_51_, v_a_50_);
v___x_53_ = lean_unbox(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(lean_object* v_id_54_, lean_object* v_a_55_, lean_object* v_b_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(v_id_54_, v_a_55_, v_b_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite(lean_object* v_00_u03b1_59_, lean_object* v_i_60_, lean_object* v_id_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_apply_2(v_id_61_, v_b_63_, v_a_62_);
v___x_65_ = lean_unbox(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(lean_object* v_00_u03b1_66_, lean_object* v_i_67_, lean_object* v_id_68_, lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite(v_00_u03b1_66_, v_i_67_, v_id_68_, v_a_69_, v_b_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite(lean_object* v_00_u03b1_73_, lean_object* v_i_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
lean_object* runtime_initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Order_Opposite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_FactoriesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Order_Opposite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Order_Opposite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_FactoriesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Opposite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Order_Opposite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Order_Opposite(builtin);
}
#ifdef __cplusplus
}
#endif
