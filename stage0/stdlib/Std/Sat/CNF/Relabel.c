// Lean compiler output
// Module: Std.Sat.CNF.Relabel
// Imports: public import Std.Sat.CNF.Basic
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
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(lean_object* v_r_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_r_1_);
v___x_4_ = l_List_reverse___redArg(v_a_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_24_; 
v_head_5_ = lean_ctor_get(v_a_2_, 0);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_24_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_24_ == 0)
{
v___x_8_ = v_a_2_;
v_isShared_9_ = v_isSharedCheck_24_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_tail_6_);
lean_inc(v_head_5_);
lean_dec(v_a_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_24_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_23_; 
v_fst_10_ = lean_ctor_get(v_head_5_, 0);
v_snd_11_ = lean_ctor_get(v_head_5_, 1);
v_isSharedCheck_23_ = !lean_is_exclusive(v_head_5_);
if (v_isSharedCheck_23_ == 0)
{
v___x_13_ = v_head_5_;
v_isShared_14_ = v_isSharedCheck_23_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_snd_11_);
lean_inc(v_fst_10_);
lean_dec(v_head_5_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_23_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_r_1_);
v___x_15_ = lean_apply_1(v_r_1_, v_fst_10_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_snd_11_);
v___x_17_ = v_reuseFailAlloc_22_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_19_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_a_3_);
lean_ctor_set(v___x_8_, 0, v___x_17_);
v___x_19_ = v___x_8_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_a_3_);
v___x_19_ = v_reuseFailAlloc_21_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_19_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel___redArg(lean_object* v_r_25_, lean_object* v_c_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_box(0);
v___x_28_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_25_, v_c_26_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_r_31_, lean_object* v_c_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_31_, v_c_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_r_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_36_, v_a_37_, v_a_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(lean_object* v_r_40_, size_t v_sz_41_, size_t v_i_42_, lean_object* v_bs_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = lean_usize_dec_lt(v_i_42_, v_sz_41_);
if (v___x_44_ == 0)
{
lean_dec(v_r_40_);
return v_bs_43_;
}
else
{
lean_object* v_v_45_; lean_object* v___x_46_; lean_object* v_bs_x27_47_; lean_object* v___x_48_; size_t v___x_49_; size_t v___x_50_; lean_object* v___x_51_; 
v_v_45_ = lean_array_uget(v_bs_43_, v_i_42_);
v___x_46_ = lean_unsigned_to_nat(0u);
v_bs_x27_47_ = lean_array_uset(v_bs_43_, v_i_42_, v___x_46_);
lean_inc(v_r_40_);
v___x_48_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_40_, v_v_45_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_42_, v___x_49_);
v___x_51_ = lean_array_uset(v_bs_x27_47_, v_i_42_, v___x_48_);
v_i_42_ = v___x_50_;
v_bs_43_ = v___x_51_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg___boxed(lean_object* v_r_53_, lean_object* v_sz_54_, lean_object* v_i_55_, lean_object* v_bs_56_){
_start:
{
size_t v_sz_boxed_57_; size_t v_i_boxed_58_; lean_object* v_res_59_; 
v_sz_boxed_57_ = lean_unbox_usize(v_sz_54_);
lean_dec(v_sz_54_);
v_i_boxed_58_ = lean_unbox_usize(v_i_55_);
lean_dec(v_i_55_);
v_res_59_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_53_, v_sz_boxed_57_, v_i_boxed_58_, v_bs_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object* v_r_60_, lean_object* v_f_61_){
_start:
{
size_t v_sz_62_; size_t v___x_63_; lean_object* v___x_64_; 
v_sz_62_ = lean_array_size(v_f_61_);
v___x_63_ = ((size_t)0ULL);
v___x_64_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_60_, v_sz_62_, v___x_63_, v_f_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel(lean_object* v_00_u03b1_65_, lean_object* v_00_u03b2_66_, lean_object* v_r_67_, lean_object* v_f_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Std_Sat_CNF_relabel___redArg(v_r_67_, v_f_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_r_72_, size_t v_sz_73_, size_t v_i_74_, lean_object* v_bs_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_72_, v_sz_73_, v_i_74_, v_bs_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___boxed(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_r_79_, lean_object* v_sz_80_, lean_object* v_i_81_, lean_object* v_bs_82_){
_start:
{
size_t v_sz_boxed_83_; size_t v_i_boxed_84_; lean_object* v_res_85_; 
v_sz_boxed_83_ = lean_unbox_usize(v_sz_80_);
lean_dec(v_sz_80_);
v_i_boxed_84_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(v_00_u03b1_77_, v_00_u03b2_78_, v_r_79_, v_sz_boxed_83_, v_i_boxed_84_, v_bs_82_);
return v_res_85_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Relabel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Relabel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Relabel(builtin);
}
#ifdef __cplusplus
}
#endif
