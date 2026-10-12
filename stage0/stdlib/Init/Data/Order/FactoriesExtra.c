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
lean_object* l_LE_ofOrd___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_LE_ofOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_LE_ofOrd___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_LE_ofOrd___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_LE_ofOrd___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_LE_ofOrd(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_LE_ofOrd___boxed(lean_object* v_00_u03b1_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_LE_ofOrd(v_00_u03b1_9_, v_inst_10_);
lean_dec_ref(v_inst_10_);
return v_res_11_;
}
}
uint8_t l_DecidableLE_ofOrd___redArg(lean_object* v_inst_12_, lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_apply_2(v_inst_12_, v_a_13_, v_b_14_);
v___x_16_ = lean_unbox(v___x_15_);
if (v___x_16_ == 2)
{
uint8_t v___x_17_; 
v___x_17_ = 0;
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
v___x_18_ = 1;
return v___x_18_;
}
}
}
LEAN_EXPORT void l_DecidableLE_ofOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_12_ = stack[0].m_obj;
lean_object* v_a_13_ = stack[1].m_obj;
lean_object* v_b_14_ = stack[2].m_obj;
uint8_t v_res_19_;
v_res_19_ = l_DecidableLE_ofOrd___redArg(v_inst_12_, v_a_13_, v_b_14_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___redArg___boxed(lean_object* v_inst_20_, lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_DecidableLE_ofOrd___redArg(v_inst_20_, v_a_21_, v_b_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l_DecidableLE_ofOrd(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_apply_2(v_inst_27_, v_a_29_, v_b_30_);
v___x_32_ = lean_unbox(v___x_31_);
if (v___x_32_ == 2)
{
uint8_t v___x_33_; 
v___x_33_ = 0;
return v___x_33_;
}
else
{
uint8_t v___x_34_; 
v___x_34_ = 1;
return v___x_34_;
}
}
}
LEAN_EXPORT void l_DecidableLE_ofOrd_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_26_ = stack[1].m_obj;
lean_object* v_inst_27_ = stack[2].m_obj;
lean_object* v_a_29_ = stack[4].m_obj;
lean_object* v_b_30_ = stack[5].m_obj;
uint8_t v_res_35_;
v_res_35_ = l_DecidableLE_ofOrd(lean_box(0), v_inst_26_, v_inst_27_, lean_box(0), v_a_29_, v_b_30_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_DecidableLE_ofOrd___boxed(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_DecidableLE_ofOrd(v_00_u03b1_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_a_40_, v_b_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
lean_object* l_LT_ofOrd___redArg(){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT void l_LT_ofOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_46_;
v_res_46_ = l_LT_ofOrd___redArg();
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_LT_ofOrd___redArg___boxed(lean_object* v___dummy_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_LT_ofOrd___redArg();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd(lean_object* v_00_u03b1_49_, lean_object* v_inst_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_LT_ofOrd___boxed(lean_object* v_00_u03b1_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_LT_ofOrd(v_00_u03b1_52_, v_inst_53_);
lean_dec_ref(v_inst_53_);
return v_res_54_;
}
}
uint8_t l_DecidableLT_ofOrd___redArg(lean_object* v_inst_55_, lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_58_ = lean_apply_2(v_inst_55_, v_a_56_, v_b_57_);
v___x_59_ = lean_obj_tag_nat(v___x_58_);
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_nat_dec_eq(v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT void l_DecidableLT_ofOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_55_ = stack[0].m_obj;
lean_object* v_a_56_ = stack[1].m_obj;
lean_object* v_b_57_ = stack[2].m_obj;
uint8_t v_res_62_;
v_res_62_ = l_DecidableLT_ofOrd___redArg(v_inst_55_, v_a_56_, v_b_57_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___redArg___boxed(lean_object* v_inst_63_, lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_DecidableLT_ofOrd___redArg(v_inst_63_, v_a_64_, v_b_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
uint8_t l_DecidableLT_ofOrd(lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_76_ = lean_apply_2(v_inst_71_, v_a_74_, v_b_75_);
v___x_77_ = lean_obj_tag_nat(v___x_76_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT void l_DecidableLT_ofOrd_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_69_ = stack[1].m_obj;
lean_object* v_inst_70_ = stack[2].m_obj;
lean_object* v_inst_71_ = stack[3].m_obj;
lean_object* v_a_74_ = stack[6].m_obj;
lean_object* v_b_75_ = stack[7].m_obj;
uint8_t v_res_80_;
v_res_80_ = l_DecidableLT_ofOrd(lean_box(0), v_inst_69_, v_inst_70_, v_inst_71_, lean_box(0), lean_box(0), v_a_74_, v_b_75_);
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l_DecidableLT_ofOrd___boxed(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_a_87_, lean_object* v_b_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_DecidableLT_ofOrd(v_00_u03b1_81_, v_inst_82_, v_inst_83_, v_inst_84_, v_inst_85_, v_inst_86_, v_a_87_, v_b_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
uint8_t l_BEq_ofOrd___redArg___lam__0(lean_object* v_inst_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_94_ = lean_apply_2(v_inst_91_, v_a_92_, v_b_93_);
v___x_95_ = lean_obj_tag_nat(v___x_94_);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_BEq_ofOrd___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_91_ = stack[0].m_obj;
lean_object* v_a_92_ = stack[1].m_obj;
lean_object* v_b_93_ = stack[2].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_BEq_ofOrd___redArg___lam__0(v_inst_91_, v_a_92_, v_b_93_);
stack->m_num = v_res_98_;
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
