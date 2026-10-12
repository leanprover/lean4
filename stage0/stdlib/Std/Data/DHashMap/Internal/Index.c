// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Index
// Imports: public import Init.Data.UInt.Bitwise import Init.ByCases import Init.Data.UInt.Lemmas
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint64_t l_Std_DHashMap_Internal_scrambleHash(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scrambleHash___boxed(lean_object*);
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Std_DHashMap_Internal_scrambleHash(uint64_t v_hash_1_){
_start:
{
uint64_t v___x_2_; uint64_t v___x_3_; uint64_t v_fold_4_; uint64_t v___x_5_; uint64_t v___x_6_; uint64_t v___x_7_; 
v___x_2_ = 32ULL;
v___x_3_ = lean_uint64_shift_right(v_hash_1_, v___x_2_);
v_fold_4_ = lean_uint64_xor(v_hash_1_, v___x_3_);
v___x_5_ = 16ULL;
v___x_6_ = lean_uint64_shift_right(v_fold_4_, v___x_5_);
v___x_7_ = lean_uint64_xor(v_fold_4_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_scrambleHash_0interp(lean_interpreter_value* stack)
{
uint64_t v_hash_1_ = stack[0].m_num;
uint64_t v_res_8_;
v_res_8_ = l_Std_DHashMap_Internal_scrambleHash(v_hash_1_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scrambleHash___boxed(lean_object* v_hash_9_){
_start:
{
uint64_t v_hash_boxed_10_; uint64_t v_res_11_; lean_object* v_r_12_; 
v_hash_boxed_10_ = lean_unbox_uint64(v_hash_9_);
lean_dec_ref(v_hash_9_);
v_res_11_ = l_Std_DHashMap_Internal_scrambleHash(v_hash_boxed_10_);
v_r_12_ = lean_box_uint64(v_res_11_);
return v_r_12_;
}
}
size_t l_Std_DHashMap_Internal_mkIdx___redArg(lean_object* v_sz_13_, uint64_t v_hash_14_){
_start:
{
uint64_t v___x_15_; uint64_t v___x_16_; uint64_t v_fold_17_; uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v___x_20_; size_t v___x_21_; size_t v___x_22_; size_t v___x_23_; size_t v___x_24_; size_t v___x_25_; 
v___x_15_ = 32ULL;
v___x_16_ = lean_uint64_shift_right(v_hash_14_, v___x_15_);
v_fold_17_ = lean_uint64_xor(v_hash_14_, v___x_16_);
v___x_18_ = 16ULL;
v___x_19_ = lean_uint64_shift_right(v_fold_17_, v___x_18_);
v___x_20_ = lean_uint64_xor(v_fold_17_, v___x_19_);
v___x_21_ = lean_uint64_to_usize(v___x_20_);
v___x_22_ = lean_usize_of_nat(v_sz_13_);
v___x_23_ = ((size_t)1ULL);
v___x_24_ = lean_usize_sub(v___x_22_, v___x_23_);
v___x_25_ = lean_usize_land(v___x_21_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_mkIdx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sz_13_ = stack[0].m_obj;
uint64_t v_hash_14_ = stack[1].m_num;
size_t v_res_26_;
v_res_26_ = l_Std_DHashMap_Internal_mkIdx___redArg(v_sz_13_, v_hash_14_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___redArg___boxed(lean_object* v_sz_27_, lean_object* v_hash_28_){
_start:
{
uint64_t v_hash_boxed_29_; size_t v_res_30_; lean_object* v_r_31_; 
v_hash_boxed_29_ = lean_unbox_uint64(v_hash_28_);
lean_dec_ref(v_hash_28_);
v_res_30_ = l_Std_DHashMap_Internal_mkIdx___redArg(v_sz_27_, v_hash_boxed_29_);
lean_dec(v_sz_27_);
v_r_31_ = lean_box_usize(v_res_30_);
return v_r_31_;
}
}
size_t l_Std_DHashMap_Internal_mkIdx(lean_object* v_sz_32_, lean_object* v_h_33_, uint64_t v_hash_34_){
_start:
{
uint64_t v___x_35_; uint64_t v___x_36_; uint64_t v_fold_37_; uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; size_t v___x_44_; size_t v___x_45_; 
v___x_35_ = 32ULL;
v___x_36_ = lean_uint64_shift_right(v_hash_34_, v___x_35_);
v_fold_37_ = lean_uint64_xor(v_hash_34_, v___x_36_);
v___x_38_ = 16ULL;
v___x_39_ = lean_uint64_shift_right(v_fold_37_, v___x_38_);
v___x_40_ = lean_uint64_xor(v_fold_37_, v___x_39_);
v___x_41_ = lean_uint64_to_usize(v___x_40_);
v___x_42_ = lean_usize_of_nat(v_sz_32_);
v___x_43_ = ((size_t)1ULL);
v___x_44_ = lean_usize_sub(v___x_42_, v___x_43_);
v___x_45_ = lean_usize_land(v___x_41_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_mkIdx_0interp(lean_interpreter_value* stack)
{
lean_object* v_sz_32_ = stack[0].m_obj;
uint64_t v_hash_34_ = stack[2].m_num;
size_t v_res_46_;
v_res_46_ = l_Std_DHashMap_Internal_mkIdx(v_sz_32_, lean_box(0), v_hash_34_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___boxed(lean_object* v_sz_47_, lean_object* v_h_48_, lean_object* v_hash_49_){
_start:
{
uint64_t v_hash_boxed_50_; size_t v_res_51_; lean_object* v_r_52_; 
v_hash_boxed_50_ = lean_unbox_uint64(v_hash_49_);
lean_dec_ref(v_hash_49_);
v_res_51_ = l_Std_DHashMap_Internal_mkIdx(v_sz_47_, v_h_48_, v_hash_boxed_50_);
lean_dec(v_sz_47_);
v_r_52_ = lean_box_usize(v_res_51_);
return v_r_52_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_Index(builtin);
}
#ifdef __cplusplus
}
#endif
