// Lean compiler output
// Module: Init.Data.BitVec.BasicAux
// Imports: public import Init.Grind.Tactics
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOfNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOfNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instAdd(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instSub(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOfNat(lean_object* v_n_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_BitVec_ofNat(v_n_1_, v_i_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOfNat___boxed(lean_object* v_n_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_BitVec_instOfNat(v_n_4_, v_i_5_);
lean_dec(v_i_5_);
lean_dec(v_n_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_BitVec_add(lean_object* v_n_7_, lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_nat_add(v_x_8_, v_y_9_);
v___x_11_ = l_BitVec_ofNat(v_n_7_, v___x_10_);
lean_dec(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_BitVec_add___boxed(lean_object* v_n_12_, lean_object* v_x_13_, lean_object* v_y_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_BitVec_add(v_n_12_, v_x_13_, v_y_14_);
lean_dec(v_y_14_);
lean_dec(v_x_13_);
lean_dec(v_n_12_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAdd(lean_object* v_n_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_closure((void*)(l_BitVec_add___boxed), 3, 1);
lean_closure_set(v___x_17_, 0, v_n_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sub(lean_object* v_n_18_, lean_object* v_x_19_, lean_object* v_y_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = lean_nat_pow(v___x_21_, v_n_18_);
v___x_23_ = lean_nat_sub(v___x_22_, v_y_20_);
lean_dec(v___x_22_);
v___x_24_ = lean_nat_add(v___x_23_, v_x_19_);
lean_dec(v___x_23_);
v___x_25_ = l_BitVec_ofNat(v_n_18_, v___x_24_);
lean_dec(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sub___boxed(lean_object* v_n_26_, lean_object* v_x_27_, lean_object* v_y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_BitVec_sub(v_n_26_, v_x_27_, v_y_28_);
lean_dec(v_y_28_);
lean_dec(v_x_27_);
lean_dec(v_n_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instSub(lean_object* v_n_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_closure((void*)(l_BitVec_sub___boxed), 3, 1);
lean_closure_set(v___x_31_, 0, v_n_30_);
return v___x_31_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_BasicAux(builtin);
}
#ifdef __cplusplus
}
#endif
