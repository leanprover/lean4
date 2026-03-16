// Lean compiler output
// Module: Lake.Util.Task
// Imports: public import Init.Control.Option public import Init.Control.Except
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
lean_object* lean_task_pure(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadTask__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__0 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__0_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__0_value)} };
static const lean_object* l_Lake_instMonadTask__lake___closed__1 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__1_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__2 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__2_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__4, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__0_value)} };
static const lean_object* l_Lake_instMonadTask__lake___closed__3 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__3_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__5, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__4 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__4_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__8, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__4_value)} };
static const lean_object* l_Lake_instMonadTask__lake___closed__5 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__5_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__10, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__6 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__6_value;
static const lean_ctor_object l_Lake_instMonadTask__lake___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__0_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__1_value)}};
static const lean_object* l_Lake_instMonadTask__lake___closed__7 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__7_value;
static const lean_ctor_object l_Lake_instMonadTask__lake___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__7_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__2_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__3_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__5_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__6_value)}};
static const lean_object* l_Lake_instMonadTask__lake___closed__8 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__8_value;
static const lean_ctor_object l_Lake_instMonadTask__lake___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__8_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__4_value)}};
static const lean_object* l_Lake_instMonadTask__lake___closed__9 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadTask__lake = (const lean_object*)&l_Lake_instMonadTask__lake___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadBaseIOTask = (const lean_object*)&l_Lake_instMonadTask__lake___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedOptionIOTask___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedOptionIOTask___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedOptionIOTask(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__0(lean_object* v_00_u03b1_1_, lean_object* v_00_u03b2_2_, lean_object* v_f_3_, lean_object* v_x_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = 0;
v___x_7_ = lean_task_map(v_f_3_, v_x_4_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__1(lean_object* v___f_8_, lean_object* v_00_u03b1_9_, lean_object* v_00_u03b2_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_13_, 0, lean_box(0));
lean_closure_set(v___x_13_, 1, lean_box(0));
lean_closure_set(v___x_13_, 2, v___y_11_);
v___x_14_ = lean_apply_4(v___f_8_, lean_box(0), lean_box(0), v___x_13_, v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__2(lean_object* v_00_u03b1_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_task_pure(v___y_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__3(lean_object* v_x_18_, lean_object* v___f_19_, lean_object* v_y_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_x_18_, v___x_21_);
v___x_23_ = lean_apply_4(v___f_19_, lean_box(0), lean_box(0), v_y_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__4(lean_object* v___f_24_, lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_f_27_, lean_object* v_x_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__3), 3, 2);
lean_closure_set(v___f_29_, 0, v_x_28_);
lean_closure_set(v___f_29_, 1, v___f_24_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = 0;
v___x_32_ = lean_task_bind(v_f_27_, v___f_29_, v___x_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__5(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_x_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; uint8_t v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = 0;
v___x_39_ = lean_task_bind(v_x_35_, v_f_36_, v___x_37_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6(lean_object* v_a_40_, lean_object* v_x_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_task_pure(v_a_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6___boxed(lean_object* v_a_43_, lean_object* v_x_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lake_instMonadTask__lake___lam__6(v_a_43_, v_x_44_);
lean_dec(v_x_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__7(lean_object* v_y_46_, lean_object* v___f_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___f_49_ = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__6___boxed), 2, 1);
lean_closure_set(v___f_49_, 0, v_a_48_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_1(v_y_46_, v___x_50_);
v___x_52_ = lean_apply_4(v___f_47_, lean_box(0), lean_box(0), v___x_51_, v___f_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__8(lean_object* v___f_53_, lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_x_56_, lean_object* v_y_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; 
lean_inc_ref(v___f_53_);
v___f_58_ = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__7), 3, 2);
lean_closure_set(v___f_58_, 0, v_y_57_);
lean_closure_set(v___f_58_, 1, v___f_53_);
v___x_59_ = lean_apply_4(v___f_53_, lean_box(0), lean_box(0), v_x_56_, v___f_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9(lean_object* v_y_60_, lean_object* v_x_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_y_60_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9___boxed(lean_object* v_y_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lake_instMonadTask__lake___lam__9(v_y_64_, v_x_65_);
lean_dec(v_x_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__10(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; 
v___f_71_ = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__9___boxed), 2, 1);
lean_closure_set(v___f_71_, 0, v_y_70_);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = 0;
v___x_74_ = lean_task_bind(v_x_69_, v___f_71_, v___x_72_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask___redArg(lean_object* v_inst_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lake_instMonadTask__lake));
v___x_101_ = l_instInhabitedOfMonad___redArg(v___x_100_, v_inst_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask(lean_object* v_00_u03b1_102_, lean_object* v_inst_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lake_instInhabitedBaseIOTask___redArg(v_inst_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Lake_instInhabitedOptionIOTask___closed__0(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box(0);
v___x_106_ = lean_task_pure(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOptionIOTask(lean_object* v_00_u03b1_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_instInhabitedOptionIOTask___closed__0, &l_Lake_instInhabitedOptionIOTask___closed__0_once, _init_l_Lake_instInhabitedOptionIOTask___closed__0);
return v___x_108_;
}
}
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Task(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Task(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_Control_Except(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Task(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Task(builtin);
}
#ifdef __cplusplus
}
#endif
