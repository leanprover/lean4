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
lean_object* l_Ordering_ctorIdx(uint8_t);
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
static lean_once_cell_t l_DecidableLT_ofOrd___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_DecidableLT_ofOrd___redArg___closed__0;
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_BEq_ofOrd___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BEq_ofOrd___redArg___lam__0___closed__0;
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
static lean_object* _init_l_DecidableLT_ofOrd___redArg___closed__0(void){
_start:
{
uint8_t v___x_51_; lean_object* v___x_52_; 
v___x_51_ = 0;
v___x_52_ = l_Ordering_ctorIdx(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd___redArg(lean_object* v_inst_53_, lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_56_ = lean_apply_2(v_inst_53_, v_a_54_, v_b_55_);
v___x_57_ = lean_unbox(v___x_56_);
v___x_58_ = l_Ordering_ctorIdx(v___x_57_);
v___x_59_ = lean_obj_once(&l_DecidableLT_ofOrd___redArg___closed__0, &l_DecidableLT_ofOrd___redArg___closed__0_once, _init_l_DecidableLT_ofOrd___redArg___closed__0);
v___x_60_ = lean_nat_dec_eq(v___x_58_, v___x_59_);
lean_dec(v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___redArg___boxed(lean_object* v_inst_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_DecidableLT_ofOrd___redArg(v_inst_61_, v_a_62_, v_b_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_74_ = lean_apply_2(v_inst_69_, v_a_72_, v_b_73_);
v___x_75_ = lean_unbox(v___x_74_);
v___x_76_ = l_Ordering_ctorIdx(v___x_75_);
v___x_77_ = lean_obj_once(&l_DecidableLT_ofOrd___redArg___closed__0, &l_DecidableLT_ofOrd___redArg___closed__0_once, _init_l_DecidableLT_ofOrd___redArg___closed__0);
v___x_78_ = lean_nat_dec_eq(v___x_76_, v___x_77_);
lean_dec(v___x_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___boxed(lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_DecidableLT_ofOrd(v_00_u03b1_79_, v_inst_80_, v_inst_81_, v_inst_82_, v_inst_83_, v_inst_84_, v_a_85_, v_b_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
static lean_object* _init_l_BEq_ofOrd___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_89_; lean_object* v___x_90_; 
v___x_89_ = 1;
v___x_90_ = l_Ordering_ctorIdx(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT uint8_t l_BEq_ofOrd___redArg___lam__0(lean_object* v_inst_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_94_ = lean_apply_2(v_inst_91_, v_a_92_, v_b_93_);
v___x_95_ = lean_unbox(v___x_94_);
v___x_96_ = l_Ordering_ctorIdx(v___x_95_);
v___x_97_ = lean_obj_once(&l_BEq_ofOrd___redArg___lam__0___closed__0, &l_BEq_ofOrd___redArg___lam__0___closed__0_once, _init_l_BEq_ofOrd___redArg___lam__0___closed__0);
v___x_98_ = lean_nat_dec_eq(v___x_96_, v___x_97_);
lean_dec(v___x_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg___lam__0___boxed(lean_object* v_inst_99_, lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_BEq_ofOrd___redArg___lam__0(v_inst_99_, v_a_100_, v_b_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg(lean_object* v_inst_104_){
_start:
{
lean_object* v___f_105_; 
v___f_105_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_105_, 0, v_inst_104_);
return v___f_105_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_){
_start:
{
lean_object* v___f_108_; 
v___f_108_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_108_, 0, v_inst_107_);
return v___f_108_;
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
