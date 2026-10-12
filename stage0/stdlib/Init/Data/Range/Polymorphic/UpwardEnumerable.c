// Lean compiler output
// Module: Init.Data.Range.Polymorphic.UpwardEnumerable
// Imports: public import Init.Data.Order.Classes public import Init.Classical import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___redArg();
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___redArg();
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ___redArg(lean_object* v_inst_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_succ_x3f_3_; lean_object* v___x_4_; lean_object* v_val_5_; 
v_succ_x3f_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_succ_x3f_3_);
lean_dec_ref(v_inst_1_);
v___x_4_ = lean_apply_1(v_succ_x3f_3_, v_a_2_);
v_val_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_val_5_);
lean_dec(v___x_4_);
return v_val_5_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_succ_x3f_10_; lean_object* v___x_11_; lean_object* v_val_12_; 
v_succ_x3f_10_ = lean_ctor_get(v_inst_7_, 0);
lean_inc_ref(v_succ_x3f_10_);
lean_dec_ref(v_inst_7_);
v___x_11_ = lean_apply_1(v_succ_x3f_10_, v_a_9_);
v_val_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_val_12_);
lean_dec(v___x_11_);
return v_val_12_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany___redArg(lean_object* v_inst_13_, lean_object* v_n_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_succMany_x3f_16_; lean_object* v___x_17_; lean_object* v_val_18_; 
v_succMany_x3f_16_ = lean_ctor_get(v_inst_13_, 1);
lean_inc_ref(v_succMany_x3f_16_);
lean_dec_ref(v_inst_13_);
v___x_17_ = lean_apply_2(v_succMany_x3f_16_, v_n_14_, v_a_15_);
v_val_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_val_18_);
lean_dec(v___x_17_);
return v_val_18_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_n_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_succMany_x3f_25_; lean_object* v___x_26_; lean_object* v_val_27_; 
v_succMany_x3f_25_ = lean_ctor_get(v_inst_20_, 1);
lean_inc_ref(v_succMany_x3f_25_);
lean_dec_ref(v_inst_20_);
v___x_26_ = lean_apply_2(v_succMany_x3f_25_, v_n_23_, v_a_24_);
v_val_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_val_27_);
lean_dec(v___x_26_);
return v_val_27_;
}
}
lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___redArg(){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(0);
return v___x_29_;
}
}
LEAN_EXPORT void l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_30_;
v_res_30_ = l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___redArg();
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___redArg___boxed(lean_object* v___dummy_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___redArg();
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___boxed(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(v_00_u03b1_39_, v_inst_40_, v_inst_41_, v_inst_42_, v_inst_43_);
lean_dec_ref(v_inst_41_);
return v_res_44_;
}
}
lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___redArg(){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT void l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_47_;
v_res_47_ = l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___redArg();
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___redArg___boxed(lean_object* v___dummy_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___redArg();
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(0);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___boxed(lean_object* v_00_u03b1_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(v_00_u03b1_56_, v_inst_57_, v_inst_58_, v_inst_59_, v_inst_60_);
lean_dec_ref(v_inst_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg(lean_object* v_inst_62_){
_start:
{
lean_object* v_val_63_; 
v_val_63_ = lean_ctor_get(v_inst_62_, 0);
lean_inc(v_val_63_);
return v_val_63_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg___boxed(lean_object* v_inst_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_PRange_UpwardEnumerable_least___redArg(v_inst_64_);
lean_dec(v_inst_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_hn_70_){
_start:
{
lean_object* v_val_71_; 
v_val_71_ = lean_ctor_get(v_inst_68_, 0);
lean_inc(v_val_71_);
return v_val_71_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___boxed(lean_object* v_00_u03b1_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_hn_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_PRange_UpwardEnumerable_least(v_00_u03b1_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_hn_76_);
lean_dec(v_inst_74_);
lean_dec_ref(v_inst_73_);
return v_res_77_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
}
#ifdef __cplusplus
}
#endif
