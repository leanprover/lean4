// Lean compiler output
// Module: Std.Sat.CNF.Relabel
// Imports: public import Std.Sat.CNF.Basic public import Std.Sat.CNF.Sat import Init.Data.List.Nat.Range
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
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Relabel_0__instDecidableEqProd_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Relabel_0__instDecidableEqProd_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(lean_object* v_r_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_bs_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_5_ == 0)
{
lean_dec(v_r_1_);
return v_bs_4_;
}
else
{
lean_object* v_v_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; lean_object* v___x_12_; 
v_v_6_ = lean_array_uget(v_bs_4_, v_i_3_);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_4_, v_i_3_, v___x_7_);
lean_inc(v_r_1_);
v___x_9_ = lean_apply_1(v_r_1_, v_v_6_);
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_3_, v___x_10_);
v___x_12_ = lean_array_uset(v_bs_x27_8_, v_i_3_, v___x_9_);
v_i_3_ = v___x_11_;
v_bs_4_ = v___x_12_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg___boxed(lean_object* v_r_14_, lean_object* v_sz_15_, lean_object* v_i_16_, lean_object* v_bs_17_){
_start:
{
size_t v_sz_boxed_18_; size_t v_i_boxed_19_; lean_object* v_res_20_; 
v_sz_boxed_18_ = lean_unbox_usize(v_sz_15_);
lean_dec(v_sz_15_);
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_14_, v_sz_boxed_18_, v_i_boxed_19_, v_bs_17_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel___redArg(lean_object* v_r_21_, lean_object* v_c_22_){
_start:
{
lean_object* v_atoms_23_; lean_object* v_polarities_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_34_; 
v_atoms_23_ = lean_ctor_get(v_c_22_, 0);
v_polarities_24_ = lean_ctor_get(v_c_22_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_c_22_);
if (v_isSharedCheck_34_ == 0)
{
v___x_26_ = v_c_22_;
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_polarities_24_);
lean_inc(v_atoms_23_);
lean_dec(v_c_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
size_t v_sz_28_; size_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v_sz_28_ = lean_array_size(v_atoms_23_);
v___x_29_ = ((size_t)0ULL);
v___x_30_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_21_, v_sz_28_, v___x_29_, v_atoms_23_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_30_);
v___x_32_ = v___x_26_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_polarities_24_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_r_37_, lean_object* v_c_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_37_, v_c_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_r_42_, size_t v_sz_43_, size_t v_i_44_, lean_object* v_bs_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_42_, v_sz_43_, v_i_44_, v_bs_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___boxed(lean_object* v_00_u03b1_47_, lean_object* v_00_u03b2_48_, lean_object* v_r_49_, lean_object* v_sz_50_, lean_object* v_i_51_, lean_object* v_bs_52_){
_start:
{
size_t v_sz_boxed_53_; size_t v_i_boxed_54_; lean_object* v_res_55_; 
v_sz_boxed_53_ = lean_unbox_usize(v_sz_50_);
lean_dec(v_sz_50_);
v_i_boxed_54_ = lean_unbox_usize(v_i_51_);
lean_dec(v_i_51_);
v_res_55_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0(v_00_u03b1_47_, v_00_u03b2_48_, v_r_49_, v_sz_boxed_53_, v_i_boxed_54_, v_bs_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Relabel_0__instDecidableEqProd_match__3_splitter___redArg(lean_object* v_x_56_, lean_object* v_h__1_57_){
_start:
{
lean_object* v_fst_58_; lean_object* v_snd_59_; lean_object* v___x_60_; 
v_fst_58_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_fst_58_);
v_snd_59_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_snd_59_);
lean_dec_ref(v_x_56_);
v___x_60_ = lean_apply_2(v_h__1_57_, v_fst_58_, v_snd_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Relabel_0__instDecidableEqProd_match__3_splitter(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_h__1_65_){
_start:
{
lean_object* v_fst_66_; lean_object* v_snd_67_; lean_object* v___x_68_; 
v_fst_66_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_fst_66_);
v_snd_67_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_snd_67_);
lean_dec_ref(v_x_64_);
v___x_68_ = lean_apply_2(v_h__1_65_, v_fst_66_, v_snd_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(lean_object* v_r_69_, size_t v_sz_70_, size_t v_i_71_, lean_object* v_bs_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_lt(v_i_71_, v_sz_70_);
if (v___x_73_ == 0)
{
lean_dec(v_r_69_);
return v_bs_72_;
}
else
{
lean_object* v_v_74_; lean_object* v___x_75_; lean_object* v_bs_x27_76_; lean_object* v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; 
v_v_74_ = lean_array_uget(v_bs_72_, v_i_71_);
v___x_75_ = lean_unsigned_to_nat(0u);
v_bs_x27_76_ = lean_array_uset(v_bs_72_, v_i_71_, v___x_75_);
lean_inc(v_r_69_);
v___x_77_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_69_, v_v_74_);
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_add(v_i_71_, v___x_78_);
v___x_80_ = lean_array_uset(v_bs_x27_76_, v_i_71_, v___x_77_);
v_i_71_ = v___x_79_;
v_bs_72_ = v___x_80_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg___boxed(lean_object* v_r_82_, lean_object* v_sz_83_, lean_object* v_i_84_, lean_object* v_bs_85_){
_start:
{
size_t v_sz_boxed_86_; size_t v_i_boxed_87_; lean_object* v_res_88_; 
v_sz_boxed_86_ = lean_unbox_usize(v_sz_83_);
lean_dec(v_sz_83_);
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_82_, v_sz_boxed_86_, v_i_boxed_87_, v_bs_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object* v_r_89_, lean_object* v_f_90_){
_start:
{
size_t v_sz_91_; size_t v___x_92_; lean_object* v___x_93_; 
v_sz_91_ = lean_array_size(v_f_90_);
v___x_92_ = ((size_t)0ULL);
v___x_93_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_89_, v_sz_91_, v___x_92_, v_f_90_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel(lean_object* v_00_u03b1_94_, lean_object* v_00_u03b2_95_, lean_object* v_r_96_, lean_object* v_f_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Std_Sat_CNF_relabel___redArg(v_r_96_, v_f_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_r_101_, size_t v_sz_102_, size_t v_i_103_, lean_object* v_bs_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_101_, v_sz_102_, v_i_103_, v_bs_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___boxed(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_r_108_, lean_object* v_sz_109_, lean_object* v_i_110_, lean_object* v_bs_111_){
_start:
{
size_t v_sz_boxed_112_; size_t v_i_boxed_113_; lean_object* v_res_114_; 
v_sz_boxed_112_ = lean_unbox_usize(v_sz_109_);
lean_dec(v_sz_109_);
v_i_boxed_113_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(v_00_u03b1_106_, v_00_u03b2_107_, v_r_108_, v_sz_boxed_112_, v_i_boxed_113_, v_bs_111_);
return v_res_114_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Sat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Relabel(uint8_t builtin) {
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
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
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
lean_object* initialize_Std_Sat_CNF_Sat(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
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
