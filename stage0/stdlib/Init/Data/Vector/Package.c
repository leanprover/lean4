// Lean compiler output
// Module: Init.Data.Vector.Package
// Imports: public import Init.Data.Order.PackageFactories public import Init.Data.Vector.Lex public import Init.Data.Ord.Vector import Init.Data.List.Package
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
uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Vector_instBEq___redArg(lean_object*, lean_object*);
lean_object* l_Vector_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instLinearOrderPackage___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instLinearOrderPackage___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instLinearOrderPackage___redArg___lam__0(lean_object* v_n_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_1_, v_inst_2_, v_inst_3_, v_a_4_, v_b_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__0___boxed(lean_object* v_n_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Vector_instLinearOrderPackage___redArg___lam__0(v_n_7_, v_inst_8_, v_inst_9_, v_a_10_, v_b_11_);
lean_dec_ref(v_b_11_);
lean_dec_ref(v_a_10_);
lean_dec(v_n_7_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Vector_instLinearOrderPackage___redArg___lam__1(lean_object* v_n_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_14_, v_inst_15_, v_inst_16_, v_a_17_, v_b_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__1___boxed(lean_object* v_n_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Vector_instLinearOrderPackage___redArg___lam__1(v_n_20_, v_inst_21_, v_inst_22_, v_a_23_, v_b_24_);
lean_dec_ref(v_b_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_n_20_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__2(lean_object* v_n_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_a_30_, lean_object* v_b_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_27_, v_inst_28_, v_inst_29_, v_a_30_, v_b_31_);
if (v___x_32_ == 0)
{
lean_inc_ref(v_b_31_);
return v_b_31_;
}
else
{
lean_inc_ref(v_a_30_);
return v_a_30_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__2___boxed(lean_object* v_n_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Vector_instLinearOrderPackage___redArg___lam__2(v_n_33_, v_inst_34_, v_inst_35_, v_a_36_, v_b_37_);
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_n_33_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__3(lean_object* v_n_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_a_42_, lean_object* v_b_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_39_, v_inst_40_, v_inst_41_, v_b_43_, v_a_42_);
if (v___x_44_ == 0)
{
lean_inc_ref(v_b_43_);
return v_b_43_;
}
else
{
lean_inc_ref(v_a_42_);
return v_a_42_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__3___boxed(lean_object* v_n_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_a_48_, lean_object* v_b_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Vector_instLinearOrderPackage___redArg___lam__3(v_n_45_, v_inst_46_, v_inst_47_, v_a_48_, v_b_49_);
lean_dec_ref(v_b_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_n_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg(lean_object* v_inst_51_, lean_object* v_h_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_n_55_){
_start:
{
lean_object* v_this_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v_this_60_; lean_object* v_this_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
lean_inc_ref_n(v_inst_54_, 3);
lean_inc_ref_n(v_inst_53_, 3);
lean_inc_n(v_n_55_, 5);
v_this_56_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v_this_56_, 0, v_n_55_);
lean_closure_set(v_this_56_, 1, v_inst_53_);
lean_closure_set(v_this_56_, 2, v_inst_54_);
v___f_57_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_57_, 0, v_n_55_);
lean_closure_set(v___f_57_, 1, v_inst_53_);
lean_closure_set(v___f_57_, 2, v_inst_54_);
v___f_58_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_58_, 0, v_n_55_);
lean_closure_set(v___f_58_, 1, v_inst_53_);
lean_closure_set(v___f_58_, 2, v_inst_54_);
v___f_59_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_59_, 0, v_n_55_);
lean_closure_set(v___f_59_, 1, v_inst_53_);
lean_closure_set(v___f_59_, 2, v_inst_54_);
v_this_60_ = lean_box(0);
v_this_61_ = lean_box(0);
v___x_62_ = l_Vector_instBEq___redArg(v_n_55_, v_h_52_);
v___x_63_ = lean_alloc_closure((void*)(l_Vector_compareLex___boxed), 5, 3);
lean_closure_set(v___x_63_, 0, lean_box(0));
lean_closure_set(v___x_63_, 1, v_n_55_);
lean_closure_set(v___x_63_, 2, v_inst_51_);
v___x_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_64_, 0, v_this_60_);
lean_ctor_set(v___x_64_, 1, v_this_61_);
lean_ctor_set(v___x_64_, 2, v___x_62_);
lean_ctor_set(v___x_64_, 3, v_this_56_);
lean_ctor_set(v___x_64_, 4, v___f_57_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
v___x_66_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___f_58_);
lean_ctor_set(v___x_66_, 2, v___f_59_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_h_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_n_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Vector_instLinearOrderPackage___redArg(v_inst_70_, v_h_71_, v_inst_72_, v_inst_73_, v_n_78_);
return v___x_79_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Vector(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Package(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Vector(uint8_t builtin);
lean_object* initialize_Init_Data_List_Package(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Package(builtin);
}
#ifdef __cplusplus
}
#endif
