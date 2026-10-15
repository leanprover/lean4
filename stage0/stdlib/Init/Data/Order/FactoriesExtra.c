// Lean compiler output
// Module: Init.Data.Order.FactoriesExtra
// Imports: public import Init.Data.Order.ClassesExtra public import Init.Data.Order.Ord public import Init.Data.Order.Classes import Init.Data.Bool
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_ofOrd___redArg();
LEAN_EXPORT lean_object* l_LE_ofOrd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LE_ofOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_ofOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LT_ofOrd___redArg();
LEAN_EXPORT lean_object* l_LT_ofOrd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LT_ofOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LT_ofOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BEq_ofOrd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BEq_ofOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_ofOrd___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_LE_ofOrd___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_LE_ofOrd___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_LE_ofOrd(lean_object* v_00_u03b1_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_LE_ofOrd___boxed(lean_object* v_00_u03b1_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_LE_ofOrd(v_00_u03b1_8_, v_inst_9_);
lean_dec_ref(v_inst_9_);
return v_res_10_;
}
}
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd___redArg(lean_object* v_inst_11_, lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_apply_2(v_inst_11_, v_a_12_, v_b_13_);
v___x_15_ = lean_unbox(v___x_14_);
if (v___x_15_ == 2)
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = 1;
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___redArg___boxed(lean_object* v_inst_18_, lean_object* v_a_19_, lean_object* v_b_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_DecidableLE_ofOrd___redArg(v_inst_18_, v_a_19_, v_b_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_apply_2(v_inst_25_, v_a_27_, v_b_28_);
v___x_30_ = lean_unbox(v___x_29_);
if (v___x_30_ == 2)
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 1;
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___boxed(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_DecidableLE_ofOrd(v_00_u03b1_33_, v_inst_34_, v_inst_35_, v_inst_36_, v_a_37_, v_b_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd___redArg(){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd___redArg___boxed(lean_object* v___dummy_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_LT_ofOrd___redArg();
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd___boxed(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_LT_ofOrd(v_00_u03b1_48_, v_inst_49_);
lean_dec_ref(v_inst_49_);
return v_res_50_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd___redArg(lean_object* v_inst_51_, lean_object* v_a_52_, lean_object* v_b_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_54_ = lean_apply_2(v_inst_51_, v_a_52_, v_b_53_);
v___x_55_ = lean_obj_tag_nat(v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_nat_dec_eq(v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___redArg___boxed(lean_object* v_inst_58_, lean_object* v_a_59_, lean_object* v_b_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_DecidableLT_ofOrd___redArg(v_inst_58_, v_a_59_, v_b_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_71_ = lean_apply_2(v_inst_66_, v_a_69_, v_b_70_);
v___x_72_ = lean_obj_tag_nat(v___x_71_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_nat_dec_eq(v___x_72_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___boxed(lean_object* v_00_u03b1_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_a_81_, lean_object* v_b_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_DecidableLT_ofOrd(v_00_u03b1_75_, v_inst_76_, v_inst_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_a_81_, v_b_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_BEq_ofOrd___redArg___lam__0(lean_object* v_inst_85_, lean_object* v_a_86_, lean_object* v_b_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_88_ = lean_apply_2(v_inst_85_, v_a_86_, v_b_87_);
v___x_89_ = lean_obj_tag_nat(v___x_88_);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_dec_eq(v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg___lam__0___boxed(lean_object* v_inst_92_, lean_object* v_a_93_, lean_object* v_b_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_BEq_ofOrd___redArg___lam__0(v_inst_92_, v_a_93_, v_b_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg(lean_object* v_inst_97_){
_start:
{
lean_object* v___f_98_; 
v___f_98_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_98_, 0, v_inst_97_);
return v___f_98_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd(lean_object* v_00_u03b1_99_, lean_object* v_inst_100_){
_start:
{
lean_object* v___f_101_; 
v___f_101_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_101_, 0, v_inst_100_);
return v___f_101_;
}
}
lean_object* runtime_initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_FactoriesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Order_FactoriesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Order_FactoriesExtra(builtin);
}
#ifdef __cplusplus
}
#endif
