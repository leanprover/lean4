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
LEAN_EXPORT uint8_t l_List_instLinearOrderPackage___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_List_decidableLE___redArg(v_inst_1_, v_inst_2_, v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__0___boxed(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_List_instLinearOrderPackage___redArg___lam__0(v_inst_6_, v_inst_7_, v_a_8_, v_b_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_List_instLinearOrderPackage___redArg___lam__1(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_List_decidableLex___redArg(v_inst_12_, v_inst_13_, v_a_14_, v_b_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__1___boxed(lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_a_19_, lean_object* v_b_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_List_instLinearOrderPackage___redArg___lam__1(v_inst_17_, v_inst_18_, v_a_19_, v_b_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__2(lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
uint8_t v___x_27_; 
lean_inc(v_b_26_);
lean_inc(v_a_25_);
v___x_27_ = l_List_decidableLE___redArg(v_inst_23_, v_inst_24_, v_a_25_, v_b_26_);
if (v___x_27_ == 0)
{
lean_dec(v_a_25_);
return v_b_26_;
}
else
{
lean_dec(v_b_26_);
return v_a_25_;
}
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg___lam__3(lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_a_30_, lean_object* v_b_31_){
_start:
{
uint8_t v___x_32_; 
lean_inc(v_a_30_);
lean_inc(v_b_31_);
v___x_32_ = l_List_decidableLE___redArg(v_inst_28_, v_inst_29_, v_b_31_, v_a_30_);
if (v___x_32_ == 0)
{
lean_dec(v_a_30_);
return v_b_31_;
}
else
{
lean_dec(v_b_31_);
return v_a_30_;
}
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage___redArg(lean_object* v_inst_33_, lean_object* v_h_34_, lean_object* v_inst_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v_this_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v_this_41_; lean_object* v_this_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_inc_ref_n(v_inst_36_, 3);
lean_inc_ref_n(v_inst_35_, 3);
v_this_37_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v_this_37_, 0, v_inst_35_);
lean_closure_set(v_this_37_, 1, v_inst_36_);
v___f_38_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_38_, 0, v_inst_35_);
lean_closure_set(v___f_38_, 1, v_inst_36_);
v___f_39_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__2), 4, 2);
lean_closure_set(v___f_39_, 0, v_inst_35_);
lean_closure_set(v___f_39_, 1, v_inst_36_);
v___f_40_ = lean_alloc_closure((void*)(l_List_instLinearOrderPackage___redArg___lam__3), 4, 2);
lean_closure_set(v___f_40_, 0, v_inst_35_);
lean_closure_set(v___f_40_, 1, v_inst_36_);
v_this_41_ = lean_box(0);
v_this_42_ = lean_box(0);
v___x_43_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_43_, 0, lean_box(0));
lean_closure_set(v___x_43_, 1, v_h_34_);
v___x_44_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_44_, 0, lean_box(0));
lean_closure_set(v___x_44_, 1, v_inst_33_);
v___x_45_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_45_, 0, v_this_41_);
lean_ctor_set(v___x_45_, 1, v_this_42_);
lean_ctor_set(v___x_45_, 2, v___x_43_);
lean_ctor_set(v___x_45_, 3, v_this_37_);
lean_ctor_set(v___x_45_, 4, v___f_38_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
v___x_47_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___f_39_);
lean_ctor_set(v___x_47_, 2, v___f_40_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_List_instLinearOrderPackage(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_h_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_List_instLinearOrderPackage___redArg(v_inst_51_, v_h_52_, v_inst_53_, v_inst_54_);
return v___x_59_;
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
