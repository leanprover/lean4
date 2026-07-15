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
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_LE_ofOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_ofOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_LE_ofOrd(lean_object* v_00_u03b1_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_LE_ofOrd___boxed(lean_object* v_00_u03b1_4_, lean_object* v_inst_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_LE_ofOrd(v_00_u03b1_4_, v_inst_5_);
lean_dec_ref(v_inst_5_);
return v_res_6_;
}
}
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd___redArg(lean_object* v_inst_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_apply_2(v_inst_7_, v_a_8_, v_b_9_);
v___x_11_ = lean_unbox(v___x_10_);
if (v___x_11_ == 2)
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 1;
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___redArg___boxed(lean_object* v_inst_14_, lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_DecidableLE_ofOrd___redArg(v_inst_14_, v_a_15_, v_b_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_apply_2(v_inst_21_, v_a_23_, v_b_24_);
v___x_26_ = lean_unbox(v___x_25_);
if (v___x_26_ == 2)
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = 1;
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___boxed(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_DecidableLE_ofOrd(v_00_u03b1_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_a_33_, v_b_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd___boxed(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_LT_ofOrd(v_00_u03b1_40_, v_inst_41_);
lean_dec_ref(v_inst_41_);
return v_res_42_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd___redArg(lean_object* v_inst_43_, lean_object* v_a_44_, lean_object* v_b_45_){
_start:
{
lean_object* v___x_46_; uint8_t v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; 
v___x_46_ = lean_apply_2(v_inst_43_, v_a_44_, v_b_45_);
v___x_47_ = 0;
v___x_48_ = lean_unbox(v___x_46_);
v___x_49_ = l_instDecidableEqOrdering(v___x_48_, v___x_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___redArg___boxed(lean_object* v_inst_50_, lean_object* v_a_51_, lean_object* v_b_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_DecidableLT_ofOrd___redArg(v_inst_50_, v_a_51_, v_b_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; uint8_t v___x_65_; uint8_t v___x_66_; 
v___x_63_ = lean_apply_2(v_inst_58_, v_a_61_, v_b_62_);
v___x_64_ = 0;
v___x_65_ = lean_unbox(v___x_63_);
v___x_66_ = l_instDecidableEqOrdering(v___x_65_, v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___boxed(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_DecidableLT_ofOrd(v_00_u03b1_67_, v_inst_68_, v_inst_69_, v_inst_70_, v_inst_71_, v_inst_72_, v_a_73_, v_b_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_BEq_ofOrd___redArg___lam__0(lean_object* v_inst_77_, lean_object* v_a_78_, lean_object* v_b_79_){
_start:
{
lean_object* v___x_80_; uint8_t v___x_81_; uint8_t v___x_82_; uint8_t v___x_83_; 
v___x_80_ = lean_apply_2(v_inst_77_, v_a_78_, v_b_79_);
v___x_81_ = 1;
v___x_82_ = lean_unbox(v___x_80_);
v___x_83_ = l_instDecidableEqOrdering(v___x_82_, v___x_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg___lam__0___boxed(lean_object* v_inst_84_, lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_BEq_ofOrd___redArg___lam__0(v_inst_84_, v_a_85_, v_b_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg(lean_object* v_inst_89_){
_start:
{
lean_object* v___f_90_; 
v___f_90_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_90_, 0, v_inst_89_);
return v___f_90_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd(lean_object* v_00_u03b1_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v___f_93_; 
v___f_93_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_93_, 0, v_inst_92_);
return v___f_93_;
}
}
lean_object* runtime_initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
