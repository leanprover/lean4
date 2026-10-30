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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(lean_object* v_r_56_, size_t v_sz_57_, size_t v_i_58_, lean_object* v_bs_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = lean_usize_dec_lt(v_i_58_, v_sz_57_);
if (v___x_60_ == 0)
{
lean_dec(v_r_56_);
return v_bs_59_;
}
else
{
lean_object* v_v_61_; lean_object* v___x_62_; lean_object* v_bs_x27_63_; lean_object* v___x_64_; size_t v___x_65_; size_t v___x_66_; lean_object* v___x_67_; 
v_v_61_ = lean_array_uget(v_bs_59_, v_i_58_);
v___x_62_ = lean_unsigned_to_nat(0u);
v_bs_x27_63_ = lean_array_uset(v_bs_59_, v_i_58_, v___x_62_);
lean_inc(v_r_56_);
v___x_64_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_56_, v_v_61_);
v___x_65_ = ((size_t)1ULL);
v___x_66_ = lean_usize_add(v_i_58_, v___x_65_);
v___x_67_ = lean_array_uset(v_bs_x27_63_, v_i_58_, v___x_64_);
v_i_58_ = v___x_66_;
v_bs_59_ = v___x_67_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg___boxed(lean_object* v_r_69_, lean_object* v_sz_70_, lean_object* v_i_71_, lean_object* v_bs_72_){
_start:
{
size_t v_sz_boxed_73_; size_t v_i_boxed_74_; lean_object* v_res_75_; 
v_sz_boxed_73_ = lean_unbox_usize(v_sz_70_);
lean_dec(v_sz_70_);
v_i_boxed_74_ = lean_unbox_usize(v_i_71_);
lean_dec(v_i_71_);
v_res_75_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_69_, v_sz_boxed_73_, v_i_boxed_74_, v_bs_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object* v_r_76_, lean_object* v_f_77_){
_start:
{
size_t v_sz_78_; size_t v___x_79_; lean_object* v___x_80_; 
v_sz_78_ = lean_array_size(v_f_77_);
v___x_79_ = ((size_t)0ULL);
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_76_, v_sz_78_, v___x_79_, v_f_77_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_r_83_, lean_object* v_f_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_Sat_CNF_relabel___redArg(v_r_83_, v_f_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(lean_object* v_00_u03b1_86_, lean_object* v_00_u03b2_87_, lean_object* v_r_88_, size_t v_sz_89_, size_t v_i_90_, lean_object* v_bs_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_88_, v_sz_89_, v_i_90_, v_bs_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___boxed(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_r_95_, lean_object* v_sz_96_, lean_object* v_i_97_, lean_object* v_bs_98_){
_start:
{
size_t v_sz_boxed_99_; size_t v_i_boxed_100_; lean_object* v_res_101_; 
v_sz_boxed_99_ = lean_unbox_usize(v_sz_96_);
lean_dec(v_sz_96_);
v_i_boxed_100_ = lean_unbox_usize(v_i_97_);
lean_dec(v_i_97_);
v_res_101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(v_00_u03b1_93_, v_00_u03b2_94_, v_r_95_, v_sz_boxed_99_, v_i_boxed_100_, v_bs_98_);
return v_res_101_;
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
