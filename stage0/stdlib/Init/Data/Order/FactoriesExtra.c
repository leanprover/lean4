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
LEAN_EXPORT lean_object* l_LE_ofOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_ofOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DecidableLE_ofOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_DecidableLT_ofOrd___redArg___closed__0(void){
_start:
{
uint8_t v___x_43_; lean_object* v___x_44_; 
v___x_43_ = 0;
v___x_44_ = l_Ordering_ctorIdx(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd___redArg(lean_object* v_inst_45_, lean_object* v_a_46_, lean_object* v_b_47_){
_start:
{
lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_48_ = lean_apply_2(v_inst_45_, v_a_46_, v_b_47_);
v___x_49_ = lean_unbox(v___x_48_);
v___x_50_ = l_Ordering_ctorIdx(v___x_49_);
v___x_51_ = lean_obj_once(&l_DecidableLT_ofOrd___redArg___closed__0, &l_DecidableLT_ofOrd___redArg___closed__0_once, _init_l_DecidableLT_ofOrd___redArg___closed__0);
v___x_52_ = lean_nat_dec_eq(v___x_50_, v___x_51_);
lean_dec(v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___redArg___boxed(lean_object* v_inst_53_, lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_DecidableLT_ofOrd___redArg(v_inst_53_, v_a_54_, v_b_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l_DecidableLT_ofOrd(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_66_ = lean_apply_2(v_inst_61_, v_a_64_, v_b_65_);
v___x_67_ = lean_unbox(v___x_66_);
v___x_68_ = l_Ordering_ctorIdx(v___x_67_);
v___x_69_ = lean_obj_once(&l_DecidableLT_ofOrd___redArg___closed__0, &l_DecidableLT_ofOrd___redArg___closed__0_once, _init_l_DecidableLT_ofOrd___redArg___closed__0);
v___x_70_ = lean_nat_dec_eq(v___x_68_, v___x_69_);
lean_dec(v___x_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___boxed(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_DecidableLT_ofOrd(v_00_u03b1_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_a_77_, v_b_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
static lean_object* _init_l_BEq_ofOrd___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_81_ = 1;
v___x_82_ = l_Ordering_ctorIdx(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT uint8_t l_BEq_ofOrd___redArg___lam__0(lean_object* v_inst_83_, lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_86_ = lean_apply_2(v_inst_83_, v_a_84_, v_b_85_);
v___x_87_ = lean_unbox(v___x_86_);
v___x_88_ = l_Ordering_ctorIdx(v___x_87_);
v___x_89_ = lean_obj_once(&l_BEq_ofOrd___redArg___lam__0___closed__0, &l_BEq_ofOrd___redArg___lam__0___closed__0_once, _init_l_BEq_ofOrd___redArg___lam__0___closed__0);
v___x_90_ = lean_nat_dec_eq(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg___lam__0___boxed(lean_object* v_inst_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_BEq_ofOrd___redArg___lam__0(v_inst_91_, v_a_92_, v_b_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd___redArg(lean_object* v_inst_96_){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_97_, 0, v_inst_96_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_BEq_ofOrd(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v___f_100_; 
v___f_100_ = lean_alloc_closure((void*)(l_BEq_ofOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_100_, 0, v_inst_99_);
return v___f_100_;
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
