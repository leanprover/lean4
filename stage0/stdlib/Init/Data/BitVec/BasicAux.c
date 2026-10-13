// Lean compiler output
// Module: Init.Data.BitVec.BasicAux
// Imports: public import Init.Grind.Tactics import Init.Data.Nat.Basic
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOfNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOfNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNatClamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNatClamp___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_BitVec_ofNatClamp(lean_object* v_w_7_, lean_object* v_n_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_9_ = lean_unsigned_to_nat(2u);
v___x_10_ = lean_nat_pow(v___x_9_, v_w_7_);
v___x_11_ = lean_nat_dec_lt(v_n_8_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_sub(v___x_10_, v___x_12_);
lean_dec(v___x_10_);
return v___x_13_;
}
else
{
lean_dec(v___x_10_);
lean_inc(v_n_8_);
return v_n_8_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofNatClamp___boxed(lean_object* v_w_14_, lean_object* v_n_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_BitVec_ofNatClamp(v_w_14_, v_n_15_);
lean_dec(v_n_15_);
lean_dec(v_w_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_BitVec_add(lean_object* v_n_17_, lean_object* v_x_18_, lean_object* v_y_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_nat_add(v_x_18_, v_y_19_);
v___x_21_ = l_BitVec_ofNat(v_n_17_, v___x_20_);
lean_dec(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_BitVec_add___boxed(lean_object* v_n_22_, lean_object* v_x_23_, lean_object* v_y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_BitVec_add(v_n_22_, v_x_23_, v_y_24_);
lean_dec(v_y_24_);
lean_dec(v_x_23_);
lean_dec(v_n_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAdd(lean_object* v_n_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_closure((void*)(l_BitVec_add___boxed), 3, 1);
lean_closure_set(v___x_27_, 0, v_n_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sub(lean_object* v_n_28_, lean_object* v_x_29_, lean_object* v_y_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_31_ = lean_unsigned_to_nat(2u);
v___x_32_ = lean_nat_pow(v___x_31_, v_n_28_);
v___x_33_ = lean_nat_sub(v___x_32_, v_y_30_);
lean_dec(v___x_32_);
v___x_34_ = lean_nat_add(v___x_33_, v_x_29_);
lean_dec(v___x_33_);
v___x_35_ = l_BitVec_ofNat(v_n_28_, v___x_34_);
lean_dec(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sub___boxed(lean_object* v_n_36_, lean_object* v_x_37_, lean_object* v_y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_BitVec_sub(v_n_36_, v_x_37_, v_y_38_);
lean_dec(v_y_38_);
lean_dec(v_x_37_);
lean_dec(v_n_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instSub(lean_object* v_n_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_closure((void*)(l_BitVec_sub___boxed), 3, 1);
lean_closure_set(v___x_41_, 0, v_n_40_);
return v___x_41_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
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
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
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
