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
LEAN_EXPORT lean_object* l_LE_opposite___redArg();
LEAN_EXPORT lean_object* l_LE_opposite___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LE_opposite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LT_opposite___redArg();
LEAN_EXPORT lean_object* l_LT_opposite___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite___redArg();
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_opposite___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_LE_opposite___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_LE_opposite___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_LE_opposite(lean_object* v_00_u03b1_5_, lean_object* v_le_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_LT_opposite___redArg(){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_LT_opposite___redArg___boxed(lean_object* v___dummy_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_LT_opposite___redArg();
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_LT_opposite(lean_object* v_00_u03b1_12_, lean_object* v_lt_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg___lam__0(lean_object* v_min_15_, lean_object* v_a_16_, lean_object* v_b_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_apply_2(v_min_15_, v_a_16_, v_b_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg(lean_object* v_min_19_){
_start:
{
lean_object* v___f_20_; 
v___f_20_ = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(v___f_20_, 0, v_min_19_);
return v___f_20_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax(lean_object* v_00_u03b1_21_, lean_object* v_min_22_){
_start:
{
lean_object* v___f_23_; 
v___f_23_ = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(v___f_23_, 0, v_min_22_);
return v___f_23_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg___lam__0(lean_object* v_max_24_, lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_2(v_max_24_, v_a_25_, v_b_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg(lean_object* v_max_28_){
_start:
{
lean_object* v___f_29_; 
v___f_29_ = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_29_, 0, v_max_28_);
return v___f_29_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin(lean_object* v_00_u03b1_30_, lean_object* v_max_31_){
_start:
{
lean_object* v___f_32_; 
v___f_32_ = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_32_, 0, v_max_31_);
return v___f_32_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(lean_object* v_id_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = lean_apply_2(v_id_33_, v_b_35_, v_a_34_);
v___x_37_ = lean_unbox(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(lean_object* v_id_38_, lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(v_id_38_, v_a_39_, v_b_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite(lean_object* v_00_u03b1_43_, lean_object* v_i_44_, lean_object* v_id_45_, lean_object* v_a_46_, lean_object* v_b_47_){
_start:
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_apply_2(v_id_45_, v_b_47_, v_a_46_);
v___x_49_ = lean_unbox(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(lean_object* v_00_u03b1_50_, lean_object* v_i_51_, lean_object* v_id_52_, lean_object* v_a_53_, lean_object* v_b_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite(v_00_u03b1_50_, v_i_51_, v_id_52_, v_a_53_, v_b_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(lean_object* v_id_57_, lean_object* v_a_58_, lean_object* v_b_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_apply_2(v_id_57_, v_b_59_, v_a_58_);
v___x_61_ = lean_unbox(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(lean_object* v_id_62_, lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(v_id_62_, v_a_63_, v_b_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite(lean_object* v_00_u03b1_67_, lean_object* v_i_68_, lean_object* v_id_69_, lean_object* v_a_70_, lean_object* v_b_71_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_apply_2(v_id_69_, v_b_71_, v_a_70_);
v___x_73_ = lean_unbox(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(lean_object* v_00_u03b1_74_, lean_object* v_i_75_, lean_object* v_id_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite(v_00_u03b1_74_, v_i_75_, v_id_76_, v_a_77_, v_b_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite___redArg(){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_OppositeOrderInstances_instLETransOpposite___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite(lean_object* v_00_u03b1_85_, lean_object* v_i_86_, lean_object* v_inst_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
}
lean_object* runtime_initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Order_Opposite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
