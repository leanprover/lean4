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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(lean_object* v_r_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_bs_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1_ = stack[0].m_obj;
size_t v_sz_2_ = stack[1].m_num;
size_t v_i_3_ = stack[2].m_num;
lean_object* v_bs_4_ = stack[3].m_obj;
lean_object* v_res_14_;
v_res_14_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_1_, v_sz_2_, v_i_3_, v_bs_4_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg___boxed(lean_object* v_r_15_, lean_object* v_sz_16_, lean_object* v_i_17_, lean_object* v_bs_18_){
_start:
{
size_t v_sz_boxed_19_; size_t v_i_boxed_20_; lean_object* v_res_21_; 
v_sz_boxed_19_ = lean_unbox_usize(v_sz_16_);
lean_dec(v_sz_16_);
v_i_boxed_20_ = lean_unbox_usize(v_i_17_);
lean_dec(v_i_17_);
v_res_21_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_15_, v_sz_boxed_19_, v_i_boxed_20_, v_bs_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel___redArg(lean_object* v_r_22_, lean_object* v_c_23_){
_start:
{
lean_object* v_atoms_24_; lean_object* v_polarities_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_35_; 
v_atoms_24_ = lean_ctor_get(v_c_23_, 0);
v_polarities_25_ = lean_ctor_get(v_c_23_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v_c_23_);
if (v_isSharedCheck_35_ == 0)
{
v___x_27_ = v_c_23_;
v_isShared_28_ = v_isSharedCheck_35_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_polarities_25_);
lean_inc(v_atoms_24_);
lean_dec(v_c_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_35_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
size_t v_sz_29_; size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v_sz_29_ = lean_array_size(v_atoms_24_);
v___x_30_ = ((size_t)0ULL);
v___x_31_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_22_, v_sz_29_, v___x_30_, v_atoms_24_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_31_);
v___x_33_ = v___x_27_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_polarities_25_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_relabel(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_r_38_, lean_object* v_c_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_38_, v_c_39_);
return v___x_40_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_r_43_, size_t v_sz_44_, size_t v_i_45_, lean_object* v_bs_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(v_r_43_, v_sz_44_, v_i_45_, v_bs_46_);
return v___x_47_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_43_ = stack[2].m_obj;
size_t v_sz_44_ = stack[3].m_num;
size_t v_i_45_ = stack[4].m_num;
lean_object* v_bs_46_ = stack[5].m_obj;
lean_object* v_res_48_;
v_res_48_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0(lean_box(0), lean_box(0), v_r_43_, v_sz_44_, v_i_45_, v_bs_46_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0___boxed(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_r_51_, lean_object* v_sz_52_, lean_object* v_i_53_, lean_object* v_bs_54_){
_start:
{
size_t v_sz_boxed_55_; size_t v_i_boxed_56_; lean_object* v_res_57_; 
v_sz_boxed_55_ = lean_unbox_usize(v_sz_52_);
lean_dec(v_sz_52_);
v_i_boxed_56_ = lean_unbox_usize(v_i_53_);
lean_dec(v_i_53_);
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_Clause_relabel_spec__0(v_00_u03b1_49_, v_00_u03b2_50_, v_r_51_, v_sz_boxed_55_, v_i_boxed_56_, v_bs_54_);
return v_res_57_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(lean_object* v_r_58_, size_t v_sz_59_, size_t v_i_60_, lean_object* v_bs_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = lean_usize_dec_lt(v_i_60_, v_sz_59_);
if (v___x_62_ == 0)
{
lean_dec(v_r_58_);
return v_bs_61_;
}
else
{
lean_object* v_v_63_; lean_object* v___x_64_; lean_object* v_bs_x27_65_; lean_object* v___x_66_; size_t v___x_67_; size_t v___x_68_; lean_object* v___x_69_; 
v_v_63_ = lean_array_uget(v_bs_61_, v_i_60_);
v___x_64_ = lean_unsigned_to_nat(0u);
v_bs_x27_65_ = lean_array_uset(v_bs_61_, v_i_60_, v___x_64_);
lean_inc(v_r_58_);
v___x_66_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_58_, v_v_63_);
v___x_67_ = ((size_t)1ULL);
v___x_68_ = lean_usize_add(v_i_60_, v___x_67_);
v___x_69_ = lean_array_uset(v_bs_x27_65_, v_i_60_, v___x_66_);
v_i_60_ = v___x_68_;
v_bs_61_ = v___x_69_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_58_ = stack[0].m_obj;
size_t v_sz_59_ = stack[1].m_num;
size_t v_i_60_ = stack[2].m_num;
lean_object* v_bs_61_ = stack[3].m_obj;
lean_object* v_res_71_;
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_58_, v_sz_59_, v_i_60_, v_bs_61_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg___boxed(lean_object* v_r_72_, lean_object* v_sz_73_, lean_object* v_i_74_, lean_object* v_bs_75_){
_start:
{
size_t v_sz_boxed_76_; size_t v_i_boxed_77_; lean_object* v_res_78_; 
v_sz_boxed_76_ = lean_unbox_usize(v_sz_73_);
lean_dec(v_sz_73_);
v_i_boxed_77_ = lean_unbox_usize(v_i_74_);
lean_dec(v_i_74_);
v_res_78_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_72_, v_sz_boxed_76_, v_i_boxed_77_, v_bs_75_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object* v_r_79_, lean_object* v_f_80_){
_start:
{
size_t v_sz_81_; size_t v___x_82_; lean_object* v___x_83_; 
v_sz_81_ = lean_array_size(v_f_80_);
v___x_82_ = ((size_t)0ULL);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_79_, v_sz_81_, v___x_82_, v_f_80_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabel(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_r_86_, lean_object* v_f_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Std_Sat_CNF_relabel___redArg(v_r_86_, v_f_87_);
return v___x_88_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_r_91_, size_t v_sz_92_, size_t v_i_93_, lean_object* v_bs_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_91_, v_sz_92_, v_i_93_, v_bs_94_);
return v___x_95_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_91_ = stack[2].m_obj;
size_t v_sz_92_ = stack[3].m_num;
size_t v_i_93_ = stack[4].m_num;
lean_object* v_bs_94_ = stack[5].m_obj;
lean_object* v_res_96_;
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(lean_box(0), lean_box(0), v_r_91_, v_sz_92_, v_i_93_, v_bs_94_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___boxed(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_r_99_, lean_object* v_sz_100_, lean_object* v_i_101_, lean_object* v_bs_102_){
_start:
{
size_t v_sz_boxed_103_; size_t v_i_boxed_104_; lean_object* v_res_105_; 
v_sz_boxed_103_ = lean_unbox_usize(v_sz_100_);
lean_dec(v_sz_100_);
v_i_boxed_104_ = lean_unbox_usize(v_i_101_);
lean_dec(v_i_101_);
v_res_105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(v_00_u03b1_97_, v_00_u03b2_98_, v_r_99_, v_sz_boxed_103_, v_i_boxed_104_, v_bs_102_);
return v_res_105_;
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
