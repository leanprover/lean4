// Lean compiler output
// Module: Init.Data.List.Package
// Imports: public import Init.Data.Order.PackageFactories import Init.Data.List.Lex
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
uint8_t l_List_decidableLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidableLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instLinearOrderPackage___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instLinearOrderPackage___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_instLinearOrderPackage___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_List_decidableLE___redArg(v_inst_1_, v_inst_2_, v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_List_instLinearOrderPackage___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_b_4_ = stack[3].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_List_instLinearOrderPackage___redArg___lam__0(v_inst_1_, v_inst_2_, v_a_3_, v_b_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_List_instLinearOrderPackage___redArg___lam__0(v_inst_7_, v_inst_8_, v_a_9_, v_b_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
uint8_t l_List_instLinearOrderPackage___redArg___lam__1(lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_List_decidableLex___redArg(v_inst_13_, v_inst_14_, v_a_15_, v_b_16_);
return v___x_17_;
}
}
LEAN_EXPORT void l_List_instLinearOrderPackage___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_13_ = stack[0].m_obj;
lean_object* v_inst_14_ = stack[1].m_obj;
lean_object* v_a_15_ = stack[2].m_obj;
lean_object* v_b_16_ = stack[3].m_obj;
uint8_t v_res_18_;
v_res_18_ = l_List_instLinearOrderPackage___redArg___lam__1(v_inst_13_, v_inst_14_, v_a_15_, v_b_16_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__1___boxed(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_List_instLinearOrderPackage___redArg___lam__1(v_inst_19_, v_inst_20_, v_a_21_, v_b_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__2(lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
uint8_t v___x_29_; 
lean_inc(v_b_28_);
lean_inc(v_a_27_);
v___x_29_ = l_List_decidableLE___redArg(v_inst_25_, v_inst_26_, v_a_27_, v_b_28_);
if (v___x_29_ == 0)
{
lean_dec(v_a_27_);
return v_b_28_;
}
else
{
lean_dec(v_b_28_);
return v_a_27_;
}
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__3(lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v___x_34_; 
lean_inc(v_a_32_);
lean_inc(v_b_33_);
v___x_34_ = l_List_decidableLE___redArg(v_inst_30_, v_inst_31_, v_b_33_, v_a_32_);
if (v___x_34_ == 0)
{
lean_dec(v_a_32_);
return v_b_33_;
}
else
{
lean_dec(v_b_33_);
return v_a_32_;
}
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg(lean_object* v_inst_35_, lean_object* v_h_36_, lean_object* v_inst_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v_this_39_; lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___f_42_; lean_object* v_this_43_; lean_object* v_this_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_inc_ref_n(v_inst_38_, 3);
lean_inc_ref_n(v_inst_37_, 3);
v_this_39_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v_this_39_, 0, v_inst_37_);
lean_closure_set(v_this_39_, 1, v_inst_38_);
v___f_40_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_40_, 0, v_inst_37_);
lean_closure_set(v___f_40_, 1, v_inst_38_);
v___f_41_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__2), 4, 2);
lean_closure_set(v___f_41_, 0, v_inst_37_);
lean_closure_set(v___f_41_, 1, v_inst_38_);
v___f_42_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__3), 4, 2);
lean_closure_set(v___f_42_, 0, v_inst_37_);
lean_closure_set(v___f_42_, 1, v_inst_38_);
v_this_43_ = lean_box(0);
v_this_44_ = lean_box(0);
v___x_45_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_45_, 0, lean_box(0));
lean_closure_set(v___x_45_, 1, v_h_36_);
v___x_46_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_46_, 0, lean_box(0));
lean_closure_set(v___x_46_, 1, v_inst_35_);
v___x_47_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_47_, 0, v_this_43_);
lean_ctor_set(v___x_47_, 1, v_this_44_);
lean_ctor_set(v___x_47_, 2, v___x_45_);
lean_ctor_set(v___x_47_, 3, v_this_39_);
lean_ctor_set(v___x_47_, 4, v___f_40_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
v___x_49_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v___f_41_);
lean_ctor_set(v___x_49_, 2, v___f_42_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_h_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_List_instLinearOrderPackage___redArg(v_inst_53_, v_h_54_, v_inst_55_, v_inst_56_);
return v___x_61_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Package(builtin);
}
#ifdef __cplusplus
}
#endif
