// Lean compiler output
// Module: Init.Data.String.Csimp
// Imports: public import Init.Data.String.Basic import Init.Data.String.Lemmas.Iterate import Init.Data.Iterators.Lemmas.Consumers.Collect
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_revPositions(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toListImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___redArg(lean_object* v___x_1_, lean_object* v_s_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_5_; uint8_t v_decide_6_; 
v___x_5_ = lean_unsigned_to_nat(0u);
v_decide_6_ = lean_nat_dec_eq(v_a_3_, v___x_5_);
if (v_decide_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_prevPos_9_; uint32_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_sub(v_a_3_, v___x_7_);
lean_dec(v_a_3_);
v_prevPos_9_ = l_String_Slice_posLE(v___x_1_, v___x_8_);
v___x_10_ = lean_string_utf8_get_fast(v_s_2_, v_prevPos_9_);
v___x_11_ = lean_box_uint32(v___x_10_);
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v_b_4_);
v_a_3_ = v_prevPos_9_;
v_b_4_ = v___x_12_;
goto _start;
}
else
{
lean_dec(v_a_3_);
return v_b_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___redArg___boxed(lean_object* v___x_14_, lean_object* v_s_15_, lean_object* v_a_16_, lean_object* v_b_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___redArg(v___x_14_, v_s_15_, v_a_16_, v_b_17_);
lean_dec_ref(v_s_15_);
lean_dec_ref(v___x_14_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_String_toListImpl(lean_object* v_s_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_string_utf8_byte_size(v_s_19_);
lean_inc_ref(v_s_19_);
v___x_22_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_22_, 0, v_s_19_);
lean_ctor_set(v___x_22_, 1, v___x_20_);
lean_ctor_set(v___x_22_, 2, v___x_21_);
v___x_23_ = l_String_Slice_revPositions(v___x_22_);
v___x_24_ = lean_box(0);
v___x_25_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___redArg(v___x_22_, v_s_19_, v___x_23_, v___x_24_);
lean_dec_ref(v_s_19_);
lean_dec_ref_known(v___x_22_, 3);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0(lean_object* v___x_26_, lean_object* v_s_27_, lean_object* v_inst_28_, lean_object* v_R_29_, lean_object* v_a_30_, lean_object* v_b_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___redArg(v___x_26_, v_s_27_, v_a_30_, v_b_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0___boxed(lean_object* v___x_33_, lean_object* v_s_34_, lean_object* v_inst_35_, lean_object* v_R_36_, lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toListImpl_spec__0(v___x_33_, v_s_34_, v_inst_35_, v_R_36_, v_a_37_, v_b_38_);
lean_dec_ref(v_s_34_);
lean_dec_ref(v___x_33_);
return v_res_39_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Csimp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Csimp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Csimp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Csimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Csimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Csimp(builtin);
}
#ifdef __cplusplus
}
#endif
