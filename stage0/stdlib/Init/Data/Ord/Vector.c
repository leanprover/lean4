// Lean compiler output
// Module: Init.Data.Ord.Vector
// Imports: public import Init.Data.Order.Ord public import Init.Data.Vector.Basic import Init.Data.Vector.Lemmas
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
uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_compareLex___at___00Vector_compareLex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_compareLex___at___00Vector_compareLex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_compareLex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_compareLex___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_compareLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instOrd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(lean_object* v_cmp_1_, lean_object* v_a_u2081_2_, lean_object* v_a_u2082_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_cmp_1_, v_a_u2081_2_, v_a_u2082_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg___boxed(lean_object* v_cmp_6_, lean_object* v_a_u2081_7_, lean_object* v_a_u2082_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(v_cmp_6_, v_a_u2081_7_, v_a_u2082_8_);
lean_dec_ref(v_a_u2082_8_);
lean_dec_ref(v_a_u2081_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l_Array_compareLex___at___00Vector_compareLex_spec__0(lean_object* v_00_u03b1_11_, lean_object* v_cmp_12_, lean_object* v_a_u2081_13_, lean_object* v_a_u2082_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(v_cmp_12_, v_a_u2081_13_, v_a_u2082_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Array_compareLex___at___00Vector_compareLex_spec__0___boxed(lean_object* v_00_u03b1_16_, lean_object* v_cmp_17_, lean_object* v_a_u2081_18_, lean_object* v_a_u2082_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Array_compareLex___at___00Vector_compareLex_spec__0(v_00_u03b1_16_, v_cmp_17_, v_a_u2081_18_, v_a_u2082_19_);
lean_dec_ref(v_a_u2082_19_);
lean_dec_ref(v_a_u2081_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint8_t l_Vector_compareLex___redArg(lean_object* v_cmp_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(v_cmp_22_, v_a_23_, v_b_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Vector_compareLex___redArg___boxed(lean_object* v_cmp_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Vector_compareLex___redArg(v_cmp_26_, v_a_27_, v_b_28_);
lean_dec_ref(v_b_28_);
lean_dec_ref(v_a_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Vector_compareLex(lean_object* v_00_u03b1_31_, lean_object* v_n_32_, lean_object* v_cmp_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(v_cmp_33_, v_a_34_, v_b_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Vector_compareLex___boxed(lean_object* v_00_u03b1_37_, lean_object* v_n_38_, lean_object* v_cmp_39_, lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Vector_compareLex(v_00_u03b1_37_, v_n_38_, v_cmp_39_, v_a_40_, v_b_41_);
lean_dec_ref(v_b_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_n_38_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* l_Vector_instOrd___redArg(lean_object* v_n_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_alloc_closure((void*)(l_Vector_compareLex___boxed), 5, 3);
lean_closure_set(v___x_46_, 0, lean_box(0));
lean_closure_set(v___x_46_, 1, v_n_44_);
lean_closure_set(v___x_46_, 2, v_inst_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Vector_instOrd(lean_object* v_00_u03b1_47_, lean_object* v_n_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_alloc_closure((void*)(l_Vector_compareLex___boxed), 5, 3);
lean_closure_set(v___x_50_, 0, lean_box(0));
lean_closure_set(v___x_50_, 1, v_n_48_);
lean_closure_set(v___x_50_, 2, v_inst_49_);
return v___x_50_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_Vector(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Ord_Vector(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_Vector(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Ord_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Ord_Vector(builtin);
}
#ifdef __cplusplus
}
#endif
