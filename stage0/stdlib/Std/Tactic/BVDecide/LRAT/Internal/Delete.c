// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Delete
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Basic import Init.ByCases
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Delete_0__Std_Tactic_BVDecide_LRAT_Internal_State_deleteOne(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Delete_0__Std_Tactic_BVDecide_LRAT_Internal_State_deleteOne___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Delete_0__Std_Tactic_BVDecide_LRAT_Internal_State_deleteOne(lean_object* v_s_1_, lean_object* v_idx_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_sub(v_idx_2_, v___x_3_);
v___x_5_ = lean_array_get_size(v_s_1_);
v___x_6_ = lean_nat_dec_lt(v___x_4_, v___x_5_);
if (v___x_6_ == 0)
{
lean_dec(v___x_4_);
return v_s_1_;
}
else
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_array_fset(v_s_1_, v___x_4_, v___x_7_);
lean_dec(v___x_4_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Delete_0__Std_Tactic_BVDecide_LRAT_Internal_State_deleteOne___boxed(lean_object* v_s_9_, lean_object* v_idx_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Delete_0__Std_Tactic_BVDecide_LRAT_Internal_State_deleteOne(v_s_9_, v_idx_10_);
lean_dec(v_idx_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany_spec__0(lean_object* v_as_12_, size_t v_i_13_, size_t v_stop_14_, lean_object* v_b_15_){
_start:
{
lean_object* v___y_17_; uint8_t v___x_21_; 
v___x_21_ = lean_usize_dec_eq(v_i_13_, v_stop_14_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_22_ = lean_array_uget_borrowed(v_as_12_, v_i_13_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_sub(v___x_22_, v___x_23_);
v___x_25_ = lean_array_get_size(v_b_15_);
v___x_26_ = lean_nat_dec_lt(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_dec(v___x_24_);
v___y_17_ = v_b_15_;
goto v___jp_16_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_array_fset(v_b_15_, v___x_24_, v___x_27_);
lean_dec(v___x_24_);
v___y_17_ = v___x_28_;
goto v___jp_16_;
}
}
else
{
return v_b_15_;
}
v___jp_16_:
{
size_t v___x_18_; size_t v___x_19_; 
v___x_18_ = ((size_t)1ULL);
v___x_19_ = lean_usize_add(v_i_13_, v___x_18_);
v_i_13_ = v___x_19_;
v_b_15_ = v___y_17_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany_spec__0___boxed(lean_object* v_as_29_, lean_object* v_i_30_, lean_object* v_stop_31_, lean_object* v_b_32_){
_start:
{
size_t v_i_boxed_33_; size_t v_stop_boxed_34_; lean_object* v_res_35_; 
v_i_boxed_33_ = lean_unbox_usize(v_i_30_);
lean_dec(v_i_30_);
v_stop_boxed_34_ = lean_unbox_usize(v_stop_31_);
lean_dec(v_stop_31_);
v_res_35_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany_spec__0(v_as_29_, v_i_boxed_33_, v_stop_boxed_34_, v_b_32_);
lean_dec_ref(v_as_29_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany(lean_object* v_s_36_, lean_object* v_idxs_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_array_get_size(v_idxs_37_);
v___x_40_ = lean_nat_dec_lt(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
return v_s_36_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = lean_nat_dec_le(v___x_39_, v___x_39_);
if (v___x_41_ == 0)
{
if (v___x_40_ == 0)
{
return v_s_36_;
}
else
{
size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((size_t)0ULL);
v___x_43_ = lean_usize_of_nat(v___x_39_);
v___x_44_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany_spec__0(v_idxs_37_, v___x_42_, v___x_43_, v_s_36_);
return v___x_44_;
}
}
else
{
size_t v___x_45_; size_t v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((size_t)0ULL);
v___x_46_ = lean_usize_of_nat(v___x_39_);
v___x_47_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany_spec__0(v_idxs_37_, v___x_45_, v___x_46_, v_s_36_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany___boxed(lean_object* v_s_48_, lean_object* v_idxs_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany(v_s_48_, v_idxs_49_);
lean_dec_ref(v_idxs_49_);
return v_res_50_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(builtin);
}
#ifdef __cplusplus
}
#endif
