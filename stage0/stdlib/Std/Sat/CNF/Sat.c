// Lean compiler output
// Module: Std.Sat.CNF.Sat
// Imports: public import Std.Sat.CNF.Basic import Init.ByCases
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
lean_object* l_Std_Sat_CNF_Clause_literals___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
lean_dec_ref(v_a_1_);
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_5_);
lean_dec_ref_known(v_x_2_, 2);
v_fst_6_ = lean_ctor_get(v_head_4_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_head_4_, 1);
lean_inc(v_snd_7_);
lean_dec(v_head_4_);
lean_inc_ref(v_a_1_);
v___x_8_ = lean_apply_1(v_a_1_, v_fst_6_);
v___x_9_ = lean_unbox(v_snd_7_);
lean_dec(v_snd_7_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = lean_unbox(v___x_8_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
lean_dec(v_tail_5_);
lean_dec_ref(v_a_1_);
v___x_11_ = 1;
return v___x_11_;
}
else
{
v_x_2_ = v_tail_5_;
goto _start;
}
}
else
{
uint8_t v___x_13_; 
v___x_13_ = lean_unbox(v___x_8_);
if (v___x_13_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
uint8_t v___x_15_; 
lean_dec(v_tail_5_);
lean_dec_ref(v_a_1_);
v___x_15_ = lean_unbox(v___x_8_);
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_16_;
v_res_16_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg___boxed(lean_object* v_a_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_17_, v_x_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object* v_a_21_, lean_object* v_c_22_){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = l_Std_Sat_CNF_Clause_literals___redArg(v_c_22_);
v___x_24_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_21_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_eval___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_21_ = stack[0].m_obj;
lean_object* v_c_22_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_21_, v_c_22_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object* v_a_26_, lean_object* v_c_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_26_, v_c_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
uint8_t l_Std_Sat_CNF_Clause_eval(lean_object* v_00_u03b1_30_, lean_object* v_a_31_, lean_object* v_c_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_31_, v_c_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_31_ = stack[1].m_obj;
lean_object* v_c_32_ = stack[2].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_Std_Sat_CNF_Clause_eval(lean_box(0), v_a_31_, v_c_32_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object* v_00_u03b1_35_, lean_object* v_a_36_, lean_object* v_c_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Std_Sat_CNF_Clause_eval(v_00_u03b1_35_, v_a_36_, v_c_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(lean_object* v_00_u03b1_40_, lean_object* v_a_41_, lean_object* v_x_42_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_41_, v_x_42_);
return v___x_43_;
}
}
LEAN_EXPORT void l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_41_ = stack[1].m_obj;
lean_object* v_x_42_ = stack[2].m_obj;
uint8_t v_res_44_;
v_res_44_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(lean_box(0), v_a_41_, v_x_42_);
stack->m_num = v_res_44_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___boxed(lean_object* v_00_u03b1_45_, lean_object* v_a_46_, lean_object* v_x_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(v_00_u03b1_45_, v_a_46_, v_x_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(lean_object* v_a_50_, lean_object* v_as_51_, size_t v_i_52_, size_t v_stop_53_){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = lean_usize_dec_eq(v_i_52_, v_stop_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_array_uget_borrowed(v_as_51_, v_i_52_);
lean_inc(v___x_55_);
lean_inc_ref(v_a_50_);
v___x_56_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_50_, v___x_55_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
lean_dec_ref(v_a_50_);
v___x_57_ = 1;
return v___x_57_;
}
else
{
size_t v___x_58_; size_t v___x_59_; 
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_add(v_i_52_, v___x_58_);
v_i_52_ = v___x_59_;
goto _start;
}
}
else
{
uint8_t v___x_61_; 
lean_dec_ref(v_a_50_);
v___x_61_ = 0;
return v___x_61_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_50_ = stack[0].m_obj;
lean_object* v_as_51_ = stack[1].m_obj;
size_t v_i_52_ = stack[2].m_num;
size_t v_stop_53_ = stack[3].m_num;
uint8_t v_res_62_;
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_50_, v_as_51_, v_i_52_, v_stop_53_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(lean_object* v_a_63_, lean_object* v_as_64_, lean_object* v_i_65_, lean_object* v_stop_66_){
_start:
{
size_t v_i_boxed_67_; size_t v_stop_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v_i_boxed_67_ = lean_unbox_usize(v_i_65_);
lean_dec(v_i_65_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_66_);
lean_dec(v_stop_66_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_63_, v_as_64_, v_i_boxed_67_, v_stop_boxed_68_);
lean_dec_ref(v_as_64_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
uint8_t l_Std_Sat_CNF_eval___redArg(lean_object* v_a_71_, lean_object* v_f_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_array_get_size(v_f_72_);
v___x_75_ = lean_nat_dec_lt(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
lean_dec_ref(v_a_71_);
v___x_76_ = 1;
return v___x_76_;
}
else
{
if (v___x_75_ == 0)
{
lean_dec_ref(v_a_71_);
return v___x_75_;
}
else
{
size_t v___x_77_; size_t v___x_78_; uint8_t v___x_79_; 
v___x_77_ = ((size_t)0ULL);
v___x_78_ = lean_usize_of_nat(v___x_74_);
v___x_79_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_71_, v_f_72_, v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
return v___x_75_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Sat_CNF_eval___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_71_ = stack[0].m_obj;
lean_object* v_f_72_ = stack[1].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Std_Sat_CNF_eval___redArg(v_a_71_, v_f_72_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object* v_a_82_, lean_object* v_f_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Std_Sat_CNF_eval___redArg(v_a_82_, v_f_83_);
lean_dec_ref(v_f_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint8_t l_Std_Sat_CNF_eval(lean_object* v_00_u03b1_86_, lean_object* v_a_87_, lean_object* v_f_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = l_Std_Sat_CNF_eval___redArg(v_a_87_, v_f_88_);
return v___x_89_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_87_ = stack[1].m_obj;
lean_object* v_f_88_ = stack[2].m_obj;
uint8_t v_res_90_;
v_res_90_ = l_Std_Sat_CNF_eval(lean_box(0), v_a_87_, v_f_88_);
stack->m_num = v_res_90_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object* v_00_u03b1_91_, lean_object* v_a_92_, lean_object* v_f_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_Sat_CNF_eval(v_00_u03b1_91_, v_a_92_, v_f_93_);
lean_dec_ref(v_f_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object* v_00_u03b1_96_, lean_object* v_a_97_, lean_object* v_as_98_, size_t v_i_99_, size_t v_stop_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_97_, v_as_98_, v_i_99_, v_stop_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_97_ = stack[1].m_obj;
lean_object* v_as_98_ = stack[2].m_obj;
size_t v_i_99_ = stack[3].m_num;
size_t v_stop_100_ = stack[4].m_num;
uint8_t v_res_102_;
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_box(0), v_a_97_, v_as_98_, v_i_99_, v_stop_100_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object* v_00_u03b1_103_, lean_object* v_a_104_, lean_object* v_as_105_, lean_object* v_i_106_, lean_object* v_stop_107_){
_start:
{
size_t v_i_boxed_108_; size_t v_stop_boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_i_boxed_108_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_stop_boxed_109_ = lean_unbox_usize(v_stop_107_);
lean_dec(v_stop_107_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(v_00_u03b1_103_, v_a_104_, v_as_105_, v_i_boxed_108_, v_stop_boxed_109_);
lean_dec_ref(v_as_105_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Sat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Sat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Sat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Sat(builtin);
}
#ifdef __cplusplus
}
#endif
