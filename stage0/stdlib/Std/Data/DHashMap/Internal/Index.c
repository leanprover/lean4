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
LEAN_EXPORT uint64_t l_Std_DHashMap_Internal_scrambleHash(uint64_t v_hash_1_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scrambleHash___boxed(lean_object* v_hash_8_){
_start:
{
uint64_t v_hash_boxed_9_; uint64_t v_res_10_; lean_object* v_r_11_; 
v_hash_boxed_9_ = lean_unbox_uint64(v_hash_8_);
lean_dec_ref(v_hash_8_);
v_res_10_ = l_Std_DHashMap_Internal_scrambleHash(v_hash_boxed_9_);
v_r_11_ = lean_box_uint64(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx___redArg(lean_object* v_sz_12_, uint64_t v_hash_13_){
_start:
{
uint64_t v___x_14_; uint64_t v___x_15_; uint64_t v_fold_16_; uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v___x_19_; size_t v___x_20_; size_t v___x_21_; size_t v___x_22_; size_t v___x_23_; size_t v___x_24_; 
v___x_14_ = 32ULL;
v___x_15_ = lean_uint64_shift_right(v_hash_13_, v___x_14_);
v_fold_16_ = lean_uint64_xor(v_hash_13_, v___x_15_);
v___x_17_ = 16ULL;
v___x_18_ = lean_uint64_shift_right(v_fold_16_, v___x_17_);
v___x_19_ = lean_uint64_xor(v_fold_16_, v___x_18_);
v___x_20_ = lean_uint64_to_usize(v___x_19_);
v___x_21_ = lean_usize_of_nat(v_sz_12_);
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_sub(v___x_21_, v___x_22_);
v___x_24_ = lean_usize_land(v___x_20_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___redArg___boxed(lean_object* v_sz_25_, lean_object* v_hash_26_){
_start:
{
uint64_t v_hash_boxed_27_; size_t v_res_28_; lean_object* v_r_29_; 
v_hash_boxed_27_ = lean_unbox_uint64(v_hash_26_);
lean_dec_ref(v_hash_26_);
v_res_28_ = l_Std_DHashMap_Internal_mkIdx___redArg(v_sz_25_, v_hash_boxed_27_);
lean_dec(v_sz_25_);
v_r_29_ = lean_box_usize(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx(lean_object* v_sz_30_, lean_object* v_h_31_, uint64_t v_hash_32_){
_start:
{
uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v_fold_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; 
v___x_33_ = 32ULL;
v___x_34_ = lean_uint64_shift_right(v_hash_32_, v___x_33_);
v_fold_35_ = lean_uint64_xor(v_hash_32_, v___x_34_);
v___x_36_ = 16ULL;
v___x_37_ = lean_uint64_shift_right(v_fold_35_, v___x_36_);
v___x_38_ = lean_uint64_xor(v_fold_35_, v___x_37_);
v___x_39_ = lean_uint64_to_usize(v___x_38_);
v___x_40_ = lean_usize_of_nat(v_sz_30_);
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_sub(v___x_40_, v___x_41_);
v___x_43_ = lean_usize_land(v___x_39_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___boxed(lean_object* v_sz_44_, lean_object* v_h_45_, lean_object* v_hash_46_){
_start:
{
uint64_t v_hash_boxed_47_; size_t v_res_48_; lean_object* v_r_49_; 
v_hash_boxed_47_ = lean_unbox_uint64(v_hash_46_);
lean_dec_ref(v_hash_46_);
v_res_48_ = l_Std_DHashMap_Internal_mkIdx(v_sz_44_, v_h_45_, v_hash_boxed_47_);
lean_dec(v_sz_44_);
v_r_49_ = lean_box_usize(v_res_48_);
return v_r_49_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
