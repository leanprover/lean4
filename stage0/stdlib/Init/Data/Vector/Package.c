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
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Vector_instLinearOrderPackage___redArg___lam__0(lean_object* v_n_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_1_, v_inst_2_, v_inst_3_, v_a_4_, v_b_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Vector_instLinearOrderPackage___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
lean_object* v_inst_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_b_5_ = stack[4].m_obj;
uint8_t v_res_7_;
v_res_7_ = l_Vector_instLinearOrderPackage___redArg___lam__0(v_n_1_, v_inst_2_, v_inst_3_, v_a_4_, v_b_5_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__0___boxed(lean_object* v_n_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_a_11_, lean_object* v_b_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Vector_instLinearOrderPackage___redArg___lam__0(v_n_8_, v_inst_9_, v_inst_10_, v_a_11_, v_b_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_Vector_instLinearOrderPackage___redArg___lam__1(lean_object* v_n_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_15_, v_inst_16_, v_inst_17_, v_a_18_, v_b_19_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Vector_instLinearOrderPackage___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_15_ = stack[0].m_obj;
lean_object* v_inst_16_ = stack[1].m_obj;
lean_object* v_inst_17_ = stack[2].m_obj;
lean_object* v_a_18_ = stack[3].m_obj;
lean_object* v_b_19_ = stack[4].m_obj;
uint8_t v_res_21_;
v_res_21_ = l_Vector_instLinearOrderPackage___redArg___lam__1(v_n_15_, v_inst_16_, v_inst_17_, v_a_18_, v_b_19_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__1___boxed(lean_object* v_n_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Vector_instLinearOrderPackage___redArg___lam__1(v_n_22_, v_inst_23_, v_inst_24_, v_a_25_, v_b_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__2(lean_object* v_n_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v___x_34_; 
lean_inc_ref(v_b_33_);
lean_inc_ref(v_a_32_);
v___x_34_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_29_, v_inst_30_, v_inst_31_, v_a_32_, v_b_33_);
if (v___x_34_ == 0)
{
lean_dec_ref(v_a_32_);
return v_b_33_;
}
else
{
lean_dec_ref(v_b_33_);
return v_a_32_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg___lam__3(lean_object* v_n_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_a_38_, lean_object* v_b_39_){
_start:
{
uint8_t v___x_40_; 
lean_inc_ref(v_a_38_);
lean_inc_ref(v_b_39_);
v___x_40_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_35_, v_inst_36_, v_inst_37_, v_b_39_, v_a_38_);
if (v___x_40_ == 0)
{
lean_dec_ref(v_a_38_);
return v_b_39_;
}
else
{
lean_dec_ref(v_b_39_);
return v_a_38_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage___redArg(lean_object* v_inst_41_, lean_object* v_h_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_n_45_){
_start:
{
lean_object* v_this_46_; lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v_this_50_; lean_object* v_this_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
lean_inc_ref_n(v_inst_44_, 3);
lean_inc_ref_n(v_inst_43_, 3);
lean_inc_n(v_n_45_, 5);
v_this_46_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v_this_46_, 0, v_n_45_);
lean_closure_set(v_this_46_, 1, v_inst_43_);
lean_closure_set(v_this_46_, 2, v_inst_44_);
v___f_47_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_47_, 0, v_n_45_);
lean_closure_set(v___f_47_, 1, v_inst_43_);
lean_closure_set(v___f_47_, 2, v_inst_44_);
v___f_48_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__2), 5, 3);
lean_closure_set(v___f_48_, 0, v_n_45_);
lean_closure_set(v___f_48_, 1, v_inst_43_);
lean_closure_set(v___f_48_, 2, v_inst_44_);
v___f_49_ = lean_alloc_closure((void*)(l_Vector_instLinearOrderPackage___redArg___lam__3), 5, 3);
lean_closure_set(v___f_49_, 0, v_n_45_);
lean_closure_set(v___f_49_, 1, v_inst_43_);
lean_closure_set(v___f_49_, 2, v_inst_44_);
v_this_50_ = lean_box(0);
v_this_51_ = lean_box(0);
v___x_52_ = l_Vector_instBEq___redArg(v_n_45_, v_h_42_);
v___x_53_ = lean_alloc_closure((void*)(l_Vector_compareLex___boxed), 5, 3);
lean_closure_set(v___x_53_, 0, lean_box(0));
lean_closure_set(v___x_53_, 1, v_n_45_);
lean_closure_set(v___x_53_, 2, v_inst_41_);
v___x_54_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_54_, 0, v_this_50_);
lean_ctor_set(v___x_54_, 1, v_this_51_);
lean_ctor_set(v___x_54_, 2, v___x_52_);
lean_ctor_set(v___x_54_, 3, v_this_46_);
lean_ctor_set(v___x_54_, 4, v___f_47_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___f_48_);
lean_ctor_set(v___x_56_, 2, v___f_49_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLinearOrderPackage(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_h_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_n_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Vector_instLinearOrderPackage___redArg(v_inst_60_, v_h_61_, v_inst_62_, v_inst_63_, v_n_68_);
return v___x_69_;
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
