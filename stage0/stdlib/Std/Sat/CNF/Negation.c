// Lean compiler output
// Module: Std.Sat.CNF.Negation
// Imports: public import Std.Sat.CNF.Basic public import Std.Sat.CNF.Sat public import Std.Sat.CNF.Entails public import Std.Sat.CNF.Unit import Init.Data.Array.MapIdx
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Std_Sat_CNF_Clause_polarity___redArg(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_Clause_unit___redArg(lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_negate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_negate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg(lean_object* v_c_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_bs_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_5_ == 0)
{
return v_bs_4_;
}
else
{
lean_object* v_v_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; lean_object* v___y_10_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_v_6_ = lean_array_uget(v_bs_4_, v_i_3_);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_4_, v_i_3_, v___x_7_);
v___x_15_ = lean_usize_to_nat(v_i_3_);
v___x_16_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_1_, v___x_15_);
lean_dec(v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = l_Std_Sat_CNF_Clause_unit___redArg(v_v_6_, v___x_5_);
v___y_10_ = v___x_17_;
goto v___jp_9_;
}
else
{
uint8_t v___x_18_; lean_object* v___x_19_; 
v___x_18_ = 0;
v___x_19_ = l_Std_Sat_CNF_Clause_unit___redArg(v_v_6_, v___x_18_);
v___y_10_ = v___x_19_;
goto v___jp_9_;
}
v___jp_9_:
{
size_t v___x_11_; size_t v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((size_t)1ULL);
v___x_12_ = lean_usize_add(v_i_3_, v___x_11_);
v___x_13_ = lean_array_uset(v_bs_x27_8_, v_i_3_, v___y_10_);
v_i_3_ = v___x_12_;
v_bs_4_ = v___x_13_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1_ = stack[0].m_obj;
size_t v_sz_2_ = stack[1].m_num;
size_t v_i_3_ = stack[2].m_num;
lean_object* v_bs_4_ = stack[3].m_obj;
lean_object* v_res_20_;
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg(v_c_1_, v_sz_2_, v_i_3_, v_bs_4_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg___boxed(lean_object* v_c_21_, lean_object* v_sz_22_, lean_object* v_i_23_, lean_object* v_bs_24_){
_start:
{
size_t v_sz_boxed_25_; size_t v_i_boxed_26_; lean_object* v_res_27_; 
v_sz_boxed_25_ = lean_unbox_usize(v_sz_22_);
lean_dec(v_sz_22_);
v_i_boxed_26_ = lean_unbox_usize(v_i_23_);
lean_dec(v_i_23_);
v_res_27_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg(v_c_21_, v_sz_boxed_25_, v_i_boxed_26_, v_bs_24_);
lean_dec_ref(v_c_21_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_negate___redArg(lean_object* v_c_28_){
_start:
{
lean_object* v_atoms_29_; size_t v_sz_30_; size_t v___x_31_; lean_object* v___x_32_; 
v_atoms_29_ = lean_ctor_get(v_c_28_, 0);
lean_inc_ref(v_atoms_29_);
v_sz_30_ = lean_array_size(v_atoms_29_);
v___x_31_ = ((size_t)0ULL);
v___x_32_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg(v_c_28_, v_sz_30_, v___x_31_, v_atoms_29_);
lean_dec_ref(v_c_28_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_negate(lean_object* v_00_u03b1_33_, lean_object* v_c_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Std_Sat_CNF_Clause_negate___redArg(v_c_34_);
return v___x_35_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0(lean_object* v_00_u03b1_36_, lean_object* v_c_37_, lean_object* v_as_38_, size_t v_sz_39_, size_t v_i_40_, lean_object* v_bs_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___redArg(v_c_37_, v_sz_39_, v_i_40_, v_bs_41_);
return v___x_42_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_37_ = stack[1].m_obj;
lean_object* v_as_38_ = stack[2].m_obj;
size_t v_sz_39_ = stack[3].m_num;
size_t v_i_40_ = stack[4].m_num;
lean_object* v_bs_41_ = stack[5].m_obj;
lean_object* v_res_43_;
v_res_43_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0(lean_box(0), v_c_37_, v_as_38_, v_sz_39_, v_i_40_, v_bs_41_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0___boxed(lean_object* v_00_u03b1_44_, lean_object* v_c_45_, lean_object* v_as_46_, lean_object* v_sz_47_, lean_object* v_i_48_, lean_object* v_bs_49_){
_start:
{
size_t v_sz_boxed_50_; size_t v_i_boxed_51_; lean_object* v_res_52_; 
v_sz_boxed_50_ = lean_unbox_usize(v_sz_47_);
lean_dec(v_sz_47_);
v_i_boxed_51_ = lean_unbox_usize(v_i_48_);
lean_dec(v_i_48_);
v_res_52_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Std_Sat_CNF_Clause_negate_spec__0(v_00_u03b1_44_, v_c_45_, v_as_46_, v_sz_boxed_50_, v_i_boxed_51_, v_bs_49_);
lean_dec_ref(v_as_46_);
lean_dec_ref(v_c_45_);
return v_res_52_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Sat(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Unit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Negation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Unit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Negation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Sat(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Unit(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Negation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Unit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Negation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Negation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Negation(builtin);
}
#ifdef __cplusplus
}
#endif
