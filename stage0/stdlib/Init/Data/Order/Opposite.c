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
lean_object* l_LE_opposite___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_LE_opposite___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_LE_opposite___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_LE_opposite___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_LE_opposite___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_LE_opposite(lean_object* v_00_u03b1_6_, lean_object* v_le_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
lean_object* l_LT_opposite___redArg(){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT void l_LT_opposite___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_11_;
v_res_11_ = l_LT_opposite___redArg();
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l_LT_opposite___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_LT_opposite___redArg();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_LT_opposite(lean_object* v_00_u03b1_14_, lean_object* v_lt_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg___lam__0(lean_object* v_min_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_apply_2(v_min_17_, v_a_18_, v_b_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg(lean_object* v_min_21_){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(v___f_22_, 0, v_min_21_);
return v___f_22_;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax(lean_object* v_00_u03b1_23_, lean_object* v_min_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(v___f_25_, 0, v_min_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg___lam__0(lean_object* v_max_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_apply_2(v_max_26_, v_a_27_, v_b_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg(lean_object* v_max_30_){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_31_, 0, v_max_30_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin(lean_object* v_00_u03b1_32_, lean_object* v_max_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_34_, 0, v_max_33_);
return v___f_34_;
}
}
uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(lean_object* v_id_35_, lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_apply_2(v_id_35_, v_b_37_, v_a_36_);
v___x_39_ = lean_unbox(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_35_ = stack[0].m_obj;
lean_object* v_a_36_ = stack[1].m_obj;
lean_object* v_b_37_ = stack[2].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(v_id_35_, v_a_36_, v_b_37_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(lean_object* v_id_41_, lean_object* v_a_42_, lean_object* v_b_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(v_id_41_, v_a_42_, v_b_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite(lean_object* v_00_u03b1_46_, lean_object* v_i_47_, lean_object* v_id_48_, lean_object* v_a_49_, lean_object* v_b_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = lean_apply_2(v_id_48_, v_b_50_, v_a_49_);
v___x_52_ = lean_unbox(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT void l_Std_OppositeOrderInstances_instDecidableLEOpposite_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_47_ = stack[1].m_obj;
lean_object* v_id_48_ = stack[2].m_obj;
lean_object* v_a_49_ = stack[3].m_obj;
lean_object* v_b_50_ = stack[4].m_obj;
uint8_t v_res_53_;
v_res_53_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite(lean_box(0), v_i_47_, v_id_48_, v_a_49_, v_b_50_);
stack->m_num = v_res_53_;
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(lean_object* v_00_u03b1_54_, lean_object* v_i_55_, lean_object* v_id_56_, lean_object* v_a_57_, lean_object* v_b_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_OppositeOrderInstances_instDecidableLEOpposite(v_00_u03b1_54_, v_i_55_, v_id_56_, v_a_57_, v_b_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(lean_object* v_id_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_apply_2(v_id_61_, v_b_63_, v_a_62_);
v___x_65_ = lean_unbox(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT void l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_61_ = stack[0].m_obj;
lean_object* v_a_62_ = stack[1].m_obj;
lean_object* v_b_63_ = stack[2].m_obj;
uint8_t v_res_66_;
v_res_66_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(v_id_61_, v_a_62_, v_b_63_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(lean_object* v_id_67_, lean_object* v_a_68_, lean_object* v_b_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(v_id_67_, v_a_68_, v_b_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite(lean_object* v_00_u03b1_72_, lean_object* v_i_73_, lean_object* v_id_74_, lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_apply_2(v_id_74_, v_b_76_, v_a_75_);
v___x_78_ = lean_unbox(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT void l_Std_OppositeOrderInstances_instDecidableLTOpposite_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_73_ = stack[1].m_obj;
lean_object* v_id_74_ = stack[2].m_obj;
lean_object* v_a_75_ = stack[3].m_obj;
lean_object* v_b_76_ = stack[4].m_obj;
uint8_t v_res_79_;
v_res_79_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite(lean_box(0), v_i_73_, v_id_74_, v_a_75_, v_b_76_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(lean_object* v_00_u03b1_80_, lean_object* v_i_81_, lean_object* v_id_82_, lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Std_OppositeOrderInstances_instDecidableLTOpposite(v_00_u03b1_80_, v_i_81_, v_id_82_, v_a_83_, v_b_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
lean_object* l_Std_OppositeOrderInstances_instLETransOpposite___redArg(){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
}
LEAN_EXPORT void l_Std_OppositeOrderInstances_instLETransOpposite___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_89_;
v_res_89_ = l_Std_OppositeOrderInstances_instLETransOpposite___redArg();
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_OppositeOrderInstances_instLETransOpposite___redArg();
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite(lean_object* v_00_u03b1_92_, lean_object* v_i_93_, lean_object* v_inst_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_box(0);
return v___x_95_;
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
