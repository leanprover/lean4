// Lean compiler output
// Module: Init.Data.Array.Package
// Imports: public import Init.Data.Order.PackageFactories public import Init.Data.Array.Lex.Lemmas import Init.Data.List.Package
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
uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_instDecidableLTOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instLinearOrderPackage___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instLinearOrderPackage___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instLinearOrderPackage___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_1_, v_inst_2_, v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__0___boxed(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Array_instLinearOrderPackage___redArg___lam__0(v_inst_6_, v_inst_7_, v_a_8_, v_b_9_);
lean_dec_ref(v_b_9_);
lean_dec_ref(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Array_instLinearOrderPackage___redArg___lam__1(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_12_, v_inst_13_, v_a_14_, v_b_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__1___boxed(lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_a_19_, lean_object* v_b_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Array_instLinearOrderPackage___redArg___lam__1(v_inst_17_, v_inst_18_, v_a_19_, v_b_20_);
lean_dec_ref(v_b_20_);
lean_dec_ref(v_a_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__2(lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_23_, v_inst_24_, v_a_25_, v_b_26_);
if (v___x_27_ == 0)
{
lean_inc_ref(v_b_26_);
return v_b_26_;
}
else
{
lean_inc_ref(v_a_25_);
return v_a_25_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__2___boxed(lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_a_30_, lean_object* v_b_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Array_instLinearOrderPackage___redArg___lam__2(v_inst_28_, v_inst_29_, v_a_30_, v_b_31_);
lean_dec_ref(v_b_31_);
lean_dec_ref(v_a_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__3(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_a_35_, lean_object* v_b_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_33_, v_inst_34_, v_b_36_, v_a_35_);
if (v___x_37_ == 0)
{
lean_inc_ref(v_b_36_);
return v_b_36_;
}
else
{
lean_inc_ref(v_a_35_);
return v_a_35_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg___lam__3___boxed(lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Array_instLinearOrderPackage___redArg___lam__3(v_inst_38_, v_inst_39_, v_a_40_, v_b_41_);
lean_dec_ref(v_b_41_);
lean_dec_ref(v_a_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage___redArg(lean_object* v_inst_43_, lean_object* v_h_44_, lean_object* v_inst_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v_this_47_; lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v_this_51_; lean_object* v_this_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
lean_inc_ref_n(v_inst_46_, 3);
lean_inc_ref_n(v_inst_45_, 3);
v_this_47_ = lean_alloc_closure((void*)(l_Array_instLinearOrderPackage___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v_this_47_, 0, v_inst_45_);
lean_closure_set(v_this_47_, 1, v_inst_46_);
v___f_48_ = lean_alloc_closure((void*)(l_Array_instLinearOrderPackage___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_48_, 0, v_inst_45_);
lean_closure_set(v___f_48_, 1, v_inst_46_);
v___f_49_ = lean_alloc_closure((void*)(l_Array_instLinearOrderPackage___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_49_, 0, v_inst_45_);
lean_closure_set(v___f_49_, 1, v_inst_46_);
v___f_50_ = lean_alloc_closure((void*)(l_Array_instLinearOrderPackage___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_50_, 0, v_inst_45_);
lean_closure_set(v___f_50_, 1, v_inst_46_);
v_this_51_ = lean_box(0);
v_this_52_ = lean_box(0);
v___f_53_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_53_, 0, v_h_44_);
v___x_54_ = lean_alloc_closure((void*)(l_Array_compareLex___boxed), 4, 2);
lean_closure_set(v___x_54_, 0, lean_box(0));
lean_closure_set(v___x_54_, 1, v_inst_43_);
v___x_55_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_55_, 0, v_this_51_);
lean_ctor_set(v___x_55_, 1, v_this_52_);
lean_ctor_set(v___x_55_, 2, v___f_53_);
lean_ctor_set(v___x_55_, 3, v_this_47_);
lean_ctor_set(v___x_55_, 4, v___f_48_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
v___x_57_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___f_49_);
lean_ctor_set(v___x_57_, 2, v___f_50_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Array_instLinearOrderPackage(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_h_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Array_instLinearOrderPackage___redArg(v_inst_61_, v_h_62_, v_inst_63_, v_inst_64_);
return v___x_69_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Package(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Package(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Package(builtin);
}
#ifdef __cplusplus
}
#endif
