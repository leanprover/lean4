// Lean compiler output
// Module: Init.Data.Vector.Algebra
// Imports: public import Init.Grind public import Init.Data.Vector.Basic import Init.Data.Vector.Lemmas
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Grind_IntModule_toNatModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_zero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instZero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_add___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Vector_add___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_add___redArg___closed__0 = (const lean_object*)&l_Vector_add___redArg___closed__0_value;
static const lean_closure_object l_Vector_add___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_add___redArg___closed__1 = (const lean_object*)&l_Vector_add___redArg___closed__1_value;
static const lean_closure_object l_Vector_add___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_add___redArg___closed__2 = (const lean_object*)&l_Vector_add___redArg___closed__2_value;
static const lean_closure_object l_Vector_add___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_add___redArg___closed__3 = (const lean_object*)&l_Vector_add___redArg___closed__3_value;
static const lean_closure_object l_Vector_add___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_add___redArg___closed__4 = (const lean_object*)&l_Vector_add___redArg___closed__4_value;
static const lean_closure_object l_Vector_add___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_add___redArg___closed__5 = (const lean_object*)&l_Vector_add___redArg___closed__5_value;
static const lean_closure_object l_Vector_add___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_add___redArg___closed__6 = (const lean_object*)&l_Vector_add___redArg___closed__6_value;
static const lean_ctor_object l_Vector_add___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_add___redArg___closed__0_value),((lean_object*)&l_Vector_add___redArg___closed__1_value)}};
static const lean_object* l_Vector_add___redArg___closed__7 = (const lean_object*)&l_Vector_add___redArg___closed__7_value;
static const lean_ctor_object l_Vector_add___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_add___redArg___closed__7_value),((lean_object*)&l_Vector_add___redArg___closed__2_value),((lean_object*)&l_Vector_add___redArg___closed__3_value),((lean_object*)&l_Vector_add___redArg___closed__4_value),((lean_object*)&l_Vector_add___redArg___closed__5_value)}};
static const lean_object* l_Vector_add___redArg___closed__8 = (const lean_object*)&l_Vector_add___redArg___closed__8_value;
static const lean_ctor_object l_Vector_add___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_add___redArg___closed__8_value),((lean_object*)&l_Vector_add___redArg___closed__6_value)}};
static const lean_object* l_Vector_add___redArg___closed__9 = (const lean_object*)&l_Vector_add___redArg___closed__9_value;
static const lean_array_object l_Vector_add___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Vector_add___redArg___closed__10 = (const lean_object*)&l_Vector_add___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Vector_add___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instAdd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_neg___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_neg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_neg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_neg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instNeg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instNeg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sub___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instSub___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instSub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_hmul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_hmul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_hmul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_hmul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instHMul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instHMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_smul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_smul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_smul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instSMul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instSMul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instAddCommMonoid___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instAddCommMonoid(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instAddCommGroup___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instAddCommGroup(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instNatModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instNatModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instIntModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instIntModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zero___redArg(lean_object* v_n_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_mk_array(v_n_1_, v_inst_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Vector_zero(lean_object* v_00_u03b1_4_, lean_object* v_n_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_mk_array(v_n_5_, v_inst_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Vector_instZero___redArg(lean_object* v_n_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_mk_array(v_n_8_, v_inst_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Vector_instZero(lean_object* v_00_u03b1_11_, lean_object* v_n_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_mk_array(v_n_12_, v_inst_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Vector_add___redArg___lam__0(lean_object* v_inst_15_, lean_object* v_x1_16_, lean_object* v_x2_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_apply_2(v_inst_15_, v_x1_16_, v_x2_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Vector_add___redArg(lean_object* v_inst_40_, lean_object* v_xs_41_, lean_object* v_ys_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_43_ = lean_alloc_closure((void*)(l_Vector_add___redArg___lam__0), 3, 1);
lean_closure_set(v___f_43_, 0, v_inst_40_);
v___x_44_ = ((lean_object*)(l_Vector_add___redArg___closed__9));
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = ((lean_object*)(l_Vector_add___redArg___closed__10));
v___x_47_ = l_Array_zipWithMAux___redArg(v___x_44_, v_xs_41_, v_ys_42_, v___f_43_, v___x_45_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Vector_add(lean_object* v_00_u03b1_48_, lean_object* v_n_49_, lean_object* v_inst_50_, lean_object* v_xs_51_, lean_object* v_ys_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Vector_add___redArg(v_inst_50_, v_xs_51_, v_ys_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Vector_add___boxed(lean_object* v_00_u03b1_54_, lean_object* v_n_55_, lean_object* v_inst_56_, lean_object* v_xs_57_, lean_object* v_ys_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Vector_add(v_00_u03b1_54_, v_n_55_, v_inst_56_, v_xs_57_, v_ys_58_);
lean_dec(v_n_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Vector_instAdd___redArg(lean_object* v_n_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_closure((void*)(l_Vector_add___boxed), 5, 3);
lean_closure_set(v___x_62_, 0, lean_box(0));
lean_closure_set(v___x_62_, 1, v_n_60_);
lean_closure_set(v___x_62_, 2, v_inst_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Vector_instAdd(lean_object* v_00_u03b1_63_, lean_object* v_n_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_alloc_closure((void*)(l_Vector_add___boxed), 5, 3);
lean_closure_set(v___x_66_, 0, lean_box(0));
lean_closure_set(v___x_66_, 1, v_n_64_);
lean_closure_set(v___x_66_, 2, v_inst_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Vector_neg___redArg___lam__0(lean_object* v_inst_67_, lean_object* v_x_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_apply_1(v_inst_67_, v_x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Vector_neg___redArg(lean_object* v_inst_70_, lean_object* v_xs_71_){
_start:
{
lean_object* v___f_72_; lean_object* v___x_73_; size_t v_sz_74_; size_t v___x_75_; lean_object* v___x_76_; 
v___f_72_ = lean_alloc_closure((void*)(l_Vector_neg___redArg___lam__0), 2, 1);
lean_closure_set(v___f_72_, 0, v_inst_70_);
v___x_73_ = ((lean_object*)(l_Vector_add___redArg___closed__9));
v_sz_74_ = lean_array_size(v_xs_71_);
v___x_75_ = ((size_t)0ULL);
v___x_76_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_73_, v___f_72_, v_sz_74_, v___x_75_, v_xs_71_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Vector_neg(lean_object* v_00_u03b1_77_, lean_object* v_n_78_, lean_object* v_inst_79_, lean_object* v_xs_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Vector_neg___redArg(v_inst_79_, v_xs_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Vector_neg___boxed(lean_object* v_00_u03b1_82_, lean_object* v_n_83_, lean_object* v_inst_84_, lean_object* v_xs_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Vector_neg(v_00_u03b1_82_, v_n_83_, v_inst_84_, v_xs_85_);
lean_dec(v_n_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Vector_instNeg___redArg(lean_object* v_n_87_, lean_object* v_inst_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_closure((void*)(l_Vector_neg___boxed), 4, 3);
lean_closure_set(v___x_89_, 0, lean_box(0));
lean_closure_set(v___x_89_, 1, v_n_87_);
lean_closure_set(v___x_89_, 2, v_inst_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Vector_instNeg(lean_object* v_00_u03b1_90_, lean_object* v_n_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_closure((void*)(l_Vector_neg___boxed), 4, 3);
lean_closure_set(v___x_93_, 0, lean_box(0));
lean_closure_set(v___x_93_, 1, v_n_91_);
lean_closure_set(v___x_93_, 2, v_inst_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Vector_sub___redArg(lean_object* v_inst_94_, lean_object* v_xs_95_, lean_object* v_ys_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___f_97_ = lean_alloc_closure((void*)(l_Vector_add___redArg___lam__0), 3, 1);
lean_closure_set(v___f_97_, 0, v_inst_94_);
v___x_98_ = ((lean_object*)(l_Vector_add___redArg___closed__9));
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = ((lean_object*)(l_Vector_add___redArg___closed__10));
v___x_101_ = l_Array_zipWithMAux___redArg(v___x_98_, v_xs_95_, v_ys_96_, v___f_97_, v___x_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Vector_sub(lean_object* v_00_u03b1_102_, lean_object* v_n_103_, lean_object* v_inst_104_, lean_object* v_xs_105_, lean_object* v_ys_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Vector_sub___redArg(v_inst_104_, v_xs_105_, v_ys_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Vector_sub___boxed(lean_object* v_00_u03b1_108_, lean_object* v_n_109_, lean_object* v_inst_110_, lean_object* v_xs_111_, lean_object* v_ys_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Vector_sub(v_00_u03b1_108_, v_n_109_, v_inst_110_, v_xs_111_, v_ys_112_);
lean_dec(v_n_109_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Vector_instSub___redArg(lean_object* v_n_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_closure((void*)(l_Vector_sub___boxed), 5, 3);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, v_n_114_);
lean_closure_set(v___x_116_, 2, v_inst_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Vector_instSub(lean_object* v_00_u03b1_117_, lean_object* v_n_118_, lean_object* v_inst_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_closure((void*)(l_Vector_sub___boxed), 5, 3);
lean_closure_set(v___x_120_, 0, lean_box(0));
lean_closure_set(v___x_120_, 1, v_n_118_);
lean_closure_set(v___x_120_, 2, v_inst_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Vector_mul___redArg(lean_object* v_inst_121_, lean_object* v_xs_122_, lean_object* v_ys_123_){
_start:
{
lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___f_124_ = lean_alloc_closure((void*)(l_Vector_add___redArg___lam__0), 3, 1);
lean_closure_set(v___f_124_, 0, v_inst_121_);
v___x_125_ = ((lean_object*)(l_Vector_add___redArg___closed__9));
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = ((lean_object*)(l_Vector_add___redArg___closed__10));
v___x_128_ = l_Array_zipWithMAux___redArg(v___x_125_, v_xs_122_, v_ys_123_, v___f_124_, v___x_126_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Vector_mul(lean_object* v_00_u03b1_129_, lean_object* v_n_130_, lean_object* v_inst_131_, lean_object* v_xs_132_, lean_object* v_ys_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Vector_mul___redArg(v_inst_131_, v_xs_132_, v_ys_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Vector_mul___boxed(lean_object* v_00_u03b1_135_, lean_object* v_n_136_, lean_object* v_inst_137_, lean_object* v_xs_138_, lean_object* v_ys_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Vector_mul(v_00_u03b1_135_, v_n_136_, v_inst_137_, v_xs_138_, v_ys_139_);
lean_dec(v_n_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMul___redArg(lean_object* v_n_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_closure((void*)(l_Vector_mul___boxed), 5, 3);
lean_closure_set(v___x_143_, 0, lean_box(0));
lean_closure_set(v___x_143_, 1, v_n_141_);
lean_closure_set(v___x_143_, 2, v_inst_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMul(lean_object* v_00_u03b1_144_, lean_object* v_n_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_closure((void*)(l_Vector_mul___boxed), 5, 3);
lean_closure_set(v___x_147_, 0, lean_box(0));
lean_closure_set(v___x_147_, 1, v_n_145_);
lean_closure_set(v___x_147_, 2, v_inst_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Vector_hmul___redArg___lam__0(lean_object* v_inst_148_, lean_object* v_c_149_, lean_object* v_x_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_apply_2(v_inst_148_, v_c_149_, v_x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Vector_hmul___redArg(lean_object* v_inst_152_, lean_object* v_c_153_, lean_object* v_xs_154_){
_start:
{
lean_object* v___f_155_; lean_object* v___x_156_; size_t v_sz_157_; size_t v___x_158_; lean_object* v___x_159_; 
v___f_155_ = lean_alloc_closure((void*)(l_Vector_hmul___redArg___lam__0), 3, 2);
lean_closure_set(v___f_155_, 0, v_inst_152_);
lean_closure_set(v___f_155_, 1, v_c_153_);
v___x_156_ = ((lean_object*)(l_Vector_add___redArg___closed__9));
v_sz_157_ = lean_array_size(v_xs_154_);
v___x_158_ = ((size_t)0ULL);
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_156_, v___f_155_, v_sz_157_, v___x_158_, v_xs_154_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Vector_hmul(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_00_u03b3_162_, lean_object* v_n_163_, lean_object* v_inst_164_, lean_object* v_c_165_, lean_object* v_xs_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Vector_hmul___redArg(v_inst_164_, v_c_165_, v_xs_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Vector_hmul___boxed(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_00_u03b3_170_, lean_object* v_n_171_, lean_object* v_inst_172_, lean_object* v_c_173_, lean_object* v_xs_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Vector_hmul(v_00_u03b1_168_, v_00_u03b2_169_, v_00_u03b3_170_, v_n_171_, v_inst_172_, v_c_173_, v_xs_174_);
lean_dec(v_n_171_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHMul___redArg(lean_object* v_n_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_closure((void*)(l_Vector_hmul___boxed), 7, 5);
lean_closure_set(v___x_178_, 0, lean_box(0));
lean_closure_set(v___x_178_, 1, lean_box(0));
lean_closure_set(v___x_178_, 2, lean_box(0));
lean_closure_set(v___x_178_, 3, v_n_176_);
lean_closure_set(v___x_178_, 4, v_inst_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHMul(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_00_u03b3_181_, lean_object* v_n_182_, lean_object* v_inst_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_closure((void*)(l_Vector_hmul___boxed), 7, 5);
lean_closure_set(v___x_184_, 0, lean_box(0));
lean_closure_set(v___x_184_, 1, lean_box(0));
lean_closure_set(v___x_184_, 2, lean_box(0));
lean_closure_set(v___x_184_, 3, v_n_182_);
lean_closure_set(v___x_184_, 4, v_inst_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Vector_smul___redArg(lean_object* v_inst_185_, lean_object* v_c_186_, lean_object* v_xs_187_){
_start:
{
lean_object* v___f_188_; lean_object* v___x_189_; size_t v_sz_190_; size_t v___x_191_; lean_object* v___x_192_; 
v___f_188_ = lean_alloc_closure((void*)(l_Vector_hmul___redArg___lam__0), 3, 2);
lean_closure_set(v___f_188_, 0, v_inst_185_);
lean_closure_set(v___f_188_, 1, v_c_186_);
v___x_189_ = ((lean_object*)(l_Vector_add___redArg___closed__9));
v_sz_190_ = lean_array_size(v_xs_187_);
v___x_191_ = ((size_t)0ULL);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_189_, v___f_188_, v_sz_190_, v___x_191_, v_xs_187_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Vector_smul(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_n_195_, lean_object* v_inst_196_, lean_object* v_c_197_, lean_object* v_xs_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Vector_smul___redArg(v_inst_196_, v_c_197_, v_xs_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Vector_smul___boxed(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_n_202_, lean_object* v_inst_203_, lean_object* v_c_204_, lean_object* v_xs_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Vector_smul(v_00_u03b1_200_, v_00_u03b2_201_, v_n_202_, v_inst_203_, v_c_204_, v_xs_205_);
lean_dec(v_n_202_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Vector_instSMul___redArg(lean_object* v_n_207_, lean_object* v_inst_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_closure((void*)(l_Vector_smul___boxed), 6, 4);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, lean_box(0));
lean_closure_set(v___x_209_, 2, v_n_207_);
lean_closure_set(v___x_209_, 3, v_inst_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Vector_instSMul(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_n_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_closure((void*)(l_Vector_smul___boxed), 6, 4);
lean_closure_set(v___x_214_, 0, lean_box(0));
lean_closure_set(v___x_214_, 1, lean_box(0));
lean_closure_set(v___x_214_, 2, v_n_212_);
lean_closure_set(v___x_214_, 3, v_inst_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Vector_instAddCommMonoid___redArg(lean_object* v_n_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v_toZero_217_; lean_object* v_toAdd_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_227_; 
v_toZero_217_ = lean_ctor_get(v_inst_216_, 0);
v_toAdd_218_ = lean_ctor_get(v_inst_216_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v_inst_216_);
if (v_isSharedCheck_227_ == 0)
{
v___x_220_ = v_inst_216_;
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_toAdd_218_);
lean_inc(v_toZero_217_);
lean_dec(v_inst_216_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
lean_inc(v_n_215_);
v___x_222_ = lean_mk_array(v_n_215_, v_toZero_217_);
v___x_223_ = lean_alloc_closure((void*)(l_Vector_add___boxed), 5, 3);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, v_n_215_);
lean_closure_set(v___x_223_, 2, v_toAdd_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_223_);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_instAddCommMonoid(lean_object* v_00_u03b1_228_, lean_object* v_n_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Vector_instAddCommMonoid___redArg(v_n_229_, v_inst_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Vector_instAddCommGroup___redArg(lean_object* v_n_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v_toAddCommMonoid_234_; lean_object* v_toNeg_235_; lean_object* v_toSub_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_246_; 
v_toAddCommMonoid_234_ = lean_ctor_get(v_inst_233_, 0);
v_toNeg_235_ = lean_ctor_get(v_inst_233_, 1);
v_toSub_236_ = lean_ctor_get(v_inst_233_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_inst_233_);
if (v_isSharedCheck_246_ == 0)
{
v___x_238_ = v_inst_233_;
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toSub_236_);
lean_inc(v_toNeg_235_);
lean_inc(v_toAddCommMonoid_234_);
lean_dec(v_inst_233_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
lean_inc_n(v_n_232_, 2);
v___x_240_ = l_Vector_instAddCommMonoid___redArg(v_n_232_, v_toAddCommMonoid_234_);
v___x_241_ = lean_alloc_closure((void*)(l_Vector_neg___boxed), 4, 3);
lean_closure_set(v___x_241_, 0, lean_box(0));
lean_closure_set(v___x_241_, 1, v_n_232_);
lean_closure_set(v___x_241_, 2, v_toNeg_235_);
v___x_242_ = lean_alloc_closure((void*)(l_Vector_sub___boxed), 5, 3);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, v_n_232_);
lean_closure_set(v___x_242_, 2, v_toSub_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 2, v___x_242_);
lean_ctor_set(v___x_238_, 1, v___x_241_);
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_244_ = v___x_238_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_instAddCommGroup(lean_object* v_00_u03b1_247_, lean_object* v_n_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Vector_instAddCommGroup___redArg(v_n_248_, v_inst_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Vector_instNatModule___redArg(lean_object* v_n_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v_toAddCommMonoid_253_; lean_object* v_nsmul_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_263_; 
v_toAddCommMonoid_253_ = lean_ctor_get(v_inst_252_, 0);
v_nsmul_254_ = lean_ctor_get(v_inst_252_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v_inst_252_);
if (v_isSharedCheck_263_ == 0)
{
v___x_256_ = v_inst_252_;
v_isShared_257_ = v_isSharedCheck_263_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_nsmul_254_);
lean_inc(v_toAddCommMonoid_253_);
lean_dec(v_inst_252_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_263_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
lean_inc(v_n_251_);
v___x_258_ = l_Vector_instAddCommMonoid___redArg(v_n_251_, v_toAddCommMonoid_253_);
v___x_259_ = lean_alloc_closure((void*)(l_Vector_smul___boxed), 6, 4);
lean_closure_set(v___x_259_, 0, lean_box(0));
lean_closure_set(v___x_259_, 1, lean_box(0));
lean_closure_set(v___x_259_, 2, v_n_251_);
lean_closure_set(v___x_259_, 3, v_nsmul_254_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_259_);
lean_ctor_set(v___x_256_, 0, v___x_258_);
v___x_261_ = v___x_256_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_instNatModule(lean_object* v_00_u03b1_264_, lean_object* v_n_265_, lean_object* v_inst_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Vector_instNatModule___redArg(v_n_265_, v_inst_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Vector_instIntModule___redArg(lean_object* v_n_268_, lean_object* v_inst_269_){
_start:
{
lean_object* v_toAddCommGroup_270_; lean_object* v_zsmul_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_283_; 
v_toAddCommGroup_270_ = lean_ctor_get(v_inst_269_, 0);
v_zsmul_271_ = lean_ctor_get(v_inst_269_, 2);
lean_inc(v_zsmul_271_);
lean_inc_ref(v_toAddCommGroup_270_);
lean_inc(v_n_268_);
v___x_272_ = l_Vector_instAddCommGroup___redArg(v_n_268_, v_toAddCommGroup_270_);
v___x_273_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_269_);
v_isSharedCheck_283_ = !lean_is_exclusive(v_inst_269_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; 
v_unused_284_ = lean_ctor_get(v_inst_269_, 2);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_inst_269_, 1);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_inst_269_, 0);
lean_dec(v_unused_286_);
v___x_275_ = v_inst_269_;
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_inst_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_nsmul_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v_nsmul_277_ = lean_ctor_get(v___x_273_, 1);
lean_inc(v_nsmul_277_);
lean_dec_ref(v___x_273_);
lean_inc(v_n_268_);
v___x_278_ = lean_alloc_closure((void*)(l_Vector_smul___boxed), 6, 4);
lean_closure_set(v___x_278_, 0, lean_box(0));
lean_closure_set(v___x_278_, 1, lean_box(0));
lean_closure_set(v___x_278_, 2, v_n_268_);
lean_closure_set(v___x_278_, 3, v_nsmul_277_);
v___x_279_ = lean_alloc_closure((void*)(l_Vector_smul___boxed), 6, 4);
lean_closure_set(v___x_279_, 0, lean_box(0));
lean_closure_set(v___x_279_, 1, lean_box(0));
lean_closure_set(v___x_279_, 2, v_n_268_);
lean_closure_set(v___x_279_, 3, v_zsmul_271_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 2, v___x_279_);
lean_ctor_set(v___x_275_, 1, v___x_278_);
lean_ctor_set(v___x_275_, 0, v___x_272_);
v___x_281_ = v___x_275_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_instIntModule(lean_object* v_00_u03b1_287_, lean_object* v_n_288_, lean_object* v_inst_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Vector_instIntModule___redArg(v_n_288_, v_inst_289_);
return v___x_290_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Algebra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Algebra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Algebra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Algebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Algebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Algebra(builtin);
}
#ifdef __cplusplus
}
#endif
