// Lean compiler output
// Module: Init.Data.Array.DecidableEq
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Basic public import Init.Data.Nat.Lemmas import Init.ByCases import Init.Classical import Init.Data.BEq import Init.Data.Bool import Init.Data.List.Nat.BEq import Init.RCases
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
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___boxed(lean_object*, lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_a_2_, v_b_3_);
v___x_5_ = lean_unbox(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Array_instDecidableEqImpl___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_b_3_ = stack[2].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Array_instDecidableEqImpl___redArg___lam__0(v_inst_1_, v_a_2_, v_b_3_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Array_instDecidableEqImpl___redArg___lam__0(v_inst_7_, v_a_8_, v_b_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object* v_inst_12_, lean_object* v_xs_13_, lean_object* v_ys_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_15_ = lean_array_get_size(v_xs_13_);
v___x_16_ = lean_array_get_size(v_ys_14_);
v___x_17_ = lean_nat_dec_eq(v___x_15_, v___x_16_);
if (v___x_17_ == 0)
{
lean_dec_ref(v_inst_12_);
return v___x_17_;
}
else
{
lean_object* v___f_18_; uint8_t v___x_19_; 
v___f_18_ = lean_alloc_closure((void*)(l_Array_instDecidableEqImpl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_18_, 0, v_inst_12_);
v___x_19_ = l_Array_isEqvAux___redArg(v_xs_13_, v_ys_14_, v___f_18_, v___x_15_);
return v___x_19_;
}
}
}
LEAN_EXPORT void l_Array_instDecidableEqImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_12_ = stack[0].m_obj;
lean_object* v_xs_13_ = stack[1].m_obj;
lean_object* v_ys_14_ = stack[2].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Array_instDecidableEqImpl___redArg(v_inst_12_, v_xs_13_, v_ys_14_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___boxed(lean_object* v_inst_21_, lean_object* v_xs_22_, lean_object* v_ys_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Array_instDecidableEqImpl___redArg(v_inst_21_, v_xs_22_, v_ys_23_);
lean_dec_ref(v_ys_23_);
lean_dec_ref(v_xs_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
uint8_t l_Array_instDecidableEqImpl(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_xs_28_, lean_object* v_ys_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = l_Array_instDecidableEqImpl___redArg(v_inst_27_, v_xs_28_, v_ys_29_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Array_instDecidableEqImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_27_ = stack[1].m_obj;
lean_object* v_xs_28_ = stack[2].m_obj;
lean_object* v_ys_29_ = stack[3].m_obj;
uint8_t v_res_31_;
v_res_31_ = l_Array_instDecidableEqImpl(lean_box(0), v_inst_27_, v_xs_28_, v_ys_29_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___boxed(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_, lean_object* v_xs_34_, lean_object* v_ys_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Array_instDecidableEqImpl(v_00_u03b1_32_, v_inst_33_, v_xs_34_, v_ys_35_);
lean_dec_ref(v_ys_35_);
lean_dec_ref(v_xs_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
uint8_t l_Array_instDecidableEq___redArg(lean_object* v_inst_38_, lean_object* v_xs_39_, lean_object* v_ys_40_){
_start:
{
lean_object* v_toList_41_; 
lean_inc_ref(v_xs_39_);
v_toList_41_ = lean_array_to_list(v_xs_39_);
if (lean_obj_tag(v_toList_41_) == 0)
{
lean_object* v_toList_42_; 
lean_dec_ref(v_xs_39_);
lean_dec_ref(v_inst_38_);
v_toList_42_ = lean_array_to_list(v_ys_40_);
if (lean_obj_tag(v_toList_42_) == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 1;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
lean_dec_ref_known(v_toList_42_, 2);
v___x_44_ = 0;
return v___x_44_;
}
}
else
{
lean_object* v_toList_45_; 
lean_dec_ref_known(v_toList_41_, 2);
lean_inc_ref(v_ys_40_);
v_toList_45_ = lean_array_to_list(v_ys_40_);
if (lean_obj_tag(v_toList_45_) == 0)
{
uint8_t v___x_46_; 
lean_dec_ref(v_ys_40_);
lean_dec_ref(v_xs_39_);
lean_dec_ref(v_inst_38_);
v___x_46_ = 0;
return v___x_46_;
}
else
{
uint8_t v___x_47_; 
lean_dec_ref_known(v_toList_45_, 2);
v___x_47_ = l_Array_instDecidableEqImpl___redArg(v_inst_38_, v_xs_39_, v_ys_40_);
lean_dec_ref(v_ys_40_);
lean_dec_ref(v_xs_39_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT void l_Array_instDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_38_ = stack[0].m_obj;
lean_object* v_xs_39_ = stack[1].m_obj;
lean_object* v_ys_40_ = stack[2].m_obj;
uint8_t v_res_48_;
v_res_48_ = l_Array_instDecidableEq___redArg(v_inst_38_, v_xs_39_, v_ys_40_);
stack->m_num = v_res_48_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___redArg___boxed(lean_object* v_inst_49_, lean_object* v_xs_50_, lean_object* v_ys_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Array_instDecidableEq___redArg(v_inst_49_, v_xs_50_, v_ys_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
uint8_t l_Array_instDecidableEq(lean_object* v_00_u03b1_54_, lean_object* v_inst_55_, lean_object* v_xs_56_, lean_object* v_ys_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = l_Array_instDecidableEq___redArg(v_inst_55_, v_xs_56_, v_ys_57_);
return v___x_58_;
}
}
LEAN_EXPORT void l_Array_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_55_ = stack[1].m_obj;
lean_object* v_xs_56_ = stack[2].m_obj;
lean_object* v_ys_57_ = stack[3].m_obj;
uint8_t v_res_59_;
v_res_59_ = l_Array_instDecidableEq(lean_box(0), v_inst_55_, v_xs_56_, v_ys_57_);
stack->m_num = v_res_59_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___boxed(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_xs_62_, lean_object* v_ys_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Array_instDecidableEq(v_00_u03b1_60_, v_inst_61_, v_xs_62_, v_ys_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
uint8_t l_Array_instDecidableEqEmp___redArg(lean_object* v_xs_66_){
_start:
{
lean_object* v_toList_67_; 
v_toList_67_ = lean_array_to_list(v_xs_66_);
if (lean_obj_tag(v_toList_67_) == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
lean_dec_ref_known(v_toList_67_, 2);
v___x_69_ = 0;
return v___x_69_;
}
}
}
LEAN_EXPORT void l_Array_instDecidableEqEmp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_66_ = stack[0].m_obj;
uint8_t v_res_70_;
v_res_70_ = l_Array_instDecidableEqEmp___redArg(v_xs_66_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___redArg___boxed(lean_object* v_xs_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Array_instDecidableEqEmp___redArg(v_xs_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
uint8_t l_Array_instDecidableEqEmp(lean_object* v_00_u03b1_74_, lean_object* v_xs_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Array_instDecidableEqEmp___redArg(v_xs_75_);
return v___x_76_;
}
}
LEAN_EXPORT void l_Array_instDecidableEqEmp_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_75_ = stack[1].m_obj;
uint8_t v_res_77_;
v_res_77_ = l_Array_instDecidableEqEmp(lean_box(0), v_xs_75_);
stack->m_num = v_res_77_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___boxed(lean_object* v_00_u03b1_78_, lean_object* v_xs_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Array_instDecidableEqEmp(v_00_u03b1_78_, v_xs_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
uint8_t l_Array_instDecidableEmpEq___redArg(lean_object* v_ys_82_){
_start:
{
lean_object* v_toList_83_; 
v_toList_83_ = lean_array_to_list(v_ys_82_);
if (lean_obj_tag(v_toList_83_) == 0)
{
uint8_t v___x_84_; 
v___x_84_ = 1;
return v___x_84_;
}
else
{
uint8_t v___x_85_; 
lean_dec_ref_known(v_toList_83_, 2);
v___x_85_ = 0;
return v___x_85_;
}
}
}
LEAN_EXPORT void l_Array_instDecidableEmpEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_82_ = stack[0].m_obj;
uint8_t v_res_86_;
v_res_86_ = l_Array_instDecidableEmpEq___redArg(v_ys_82_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___redArg___boxed(lean_object* v_ys_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Array_instDecidableEmpEq___redArg(v_ys_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
uint8_t l_Array_instDecidableEmpEq(lean_object* v_00_u03b1_90_, lean_object* v_ys_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l_Array_instDecidableEmpEq___redArg(v_ys_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Array_instDecidableEmpEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_91_ = stack[1].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_Array_instDecidableEmpEq(lean_box(0), v_ys_91_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___boxed(lean_object* v_00_u03b1_94_, lean_object* v_ys_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Array_instDecidableEmpEq(v_00_u03b1_94_, v_ys_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
uint8_t l_Array_instDecidableEqEmpImpl___redArg(lean_object* v_xs_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_array_get_size(v_xs_98_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_nat_dec_eq(v___x_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l_Array_instDecidableEqEmpImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_98_ = stack[0].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Array_instDecidableEqEmpImpl___redArg(v_xs_98_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___redArg___boxed(lean_object* v_xs_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Array_instDecidableEqEmpImpl___redArg(v_xs_103_);
lean_dec_ref(v_xs_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
uint8_t l_Array_instDecidableEqEmpImpl(lean_object* v_00_u03b1_106_, lean_object* v_xs_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = lean_array_get_size(v_xs_107_);
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_nat_dec_eq(v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT void l_Array_instDecidableEqEmpImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_107_ = stack[1].m_obj;
uint8_t v_res_111_;
v_res_111_ = l_Array_instDecidableEqEmpImpl(lean_box(0), v_xs_107_);
stack->m_num = v_res_111_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___boxed(lean_object* v_00_u03b1_112_, lean_object* v_xs_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Array_instDecidableEqEmpImpl(v_00_u03b1_112_, v_xs_113_);
lean_dec_ref(v_xs_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
uint8_t l_Array_instDecidableEmpEqImpl___redArg(lean_object* v_xs_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_array_get_size(v_xs_116_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Array_instDecidableEmpEqImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_116_ = stack[0].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Array_instDecidableEmpEqImpl___redArg(v_xs_116_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___redArg___boxed(lean_object* v_xs_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Array_instDecidableEmpEqImpl___redArg(v_xs_121_);
lean_dec_ref(v_xs_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
uint8_t l_Array_instDecidableEmpEqImpl(lean_object* v_00_u03b1_124_, lean_object* v_xs_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = lean_array_get_size(v_xs_125_);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_nat_dec_eq(v___x_126_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT void l_Array_instDecidableEmpEqImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_125_ = stack[1].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Array_instDecidableEmpEqImpl(lean_box(0), v_xs_125_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___boxed(lean_object* v_00_u03b1_130_, lean_object* v_xs_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Array_instDecidableEmpEqImpl(v_00_u03b1_130_, v_xs_131_);
lean_dec_ref(v_xs_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_BEq(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_DecidableEq(builtin);
}
#ifdef __cplusplus
}
#endif
