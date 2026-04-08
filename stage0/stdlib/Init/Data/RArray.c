// Lean compiler output
// Module: Init.Data.RArray
// Imports: public import Init.GetElem import Init.PropLemmas
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_branch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_branch_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instGetElemRArrayNatTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instGetElemRArrayNatTrue___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instGetElemRArrayNatTrue___closed__0 = (const lean_object*)&l_Lean_instGetElemRArrayNatTrue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_RArray_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx(lean_object* v_00_u03b1_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_RArray_ctorIdx___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___boxed(lean_object* v_00_u03b1_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_RArray_ctorIdx(v_00_u03b1_9_, v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
if (lean_obj_tag(v_t_12_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v_t_12_);
v___x_15_ = lean_apply_1(v_k_13_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_16_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v_t_12_, 1);
lean_inc_ref(v_a_17_);
v_a_18_ = lean_ctor_get(v_t_12_, 2);
lean_inc_ref(v_a_18_);
lean_dec_ref(v_t_12_);
v___x_19_ = lean_apply_3(v_k_13_, v_a_16_, v_a_17_, v_a_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim(lean_object* v_00_u03b1_20_, lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_RArray_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim___boxed(lean_object* v_00_u03b1_27_, lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_RArray_ctorElim(v_00_u03b1_27_, v_motive_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_leaf_elim___redArg(lean_object* v_t_34_, lean_object* v_leaf_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_RArray_ctorElim___redArg(v_t_34_, v_leaf_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_leaf_elim(lean_object* v_00_u03b1_37_, lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_leaf_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_RArray_ctorElim___redArg(v_t_39_, v_leaf_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_branch_elim___redArg(lean_object* v_t_43_, lean_object* v_branch_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_RArray_ctorElim___redArg(v_t_43_, v_branch_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_branch_elim(lean_object* v_00_u03b1_46_, lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_branch_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_RArray_ctorElim___redArg(v_t_48_, v_branch_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___redArg(lean_object* v_a_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_a_52_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_54_);
v_a_55_ = lean_ctor_get(v_a_52_, 0);
lean_inc(v_a_55_);
lean_dec_ref(v_a_52_);
v___x_56_ = lean_apply_1(v_h__1_53_, v_a_55_);
return v___x_56_;
}
else
{
lean_object* v_a_57_; lean_object* v_a_58_; lean_object* v_a_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_53_);
v_a_57_ = lean_ctor_get(v_a_52_, 0);
lean_inc(v_a_57_);
v_a_58_ = lean_ctor_get(v_a_52_, 1);
lean_inc_ref(v_a_58_);
v_a_59_ = lean_ctor_get(v_a_52_, 2);
lean_inc_ref(v_a_59_);
lean_dec_ref(v_a_52_);
v___x_60_ = lean_apply_3(v_h__2_54_, v_a_57_, v_a_58_, v_a_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter(lean_object* v_00_u03b1_61_, lean_object* v_motive_62_, lean_object* v_a_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_a_63_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_65_);
v_a_66_ = lean_ctor_get(v_a_63_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v_a_63_);
v___x_67_ = lean_apply_1(v_h__1_64_, v_a_66_);
return v___x_67_;
}
else
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_64_);
v_a_68_ = lean_ctor_get(v_a_63_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v_a_63_, 1);
lean_inc_ref(v_a_69_);
v_a_70_ = lean_ctor_get(v_a_63_, 2);
lean_inc_ref(v_a_70_);
lean_dec_ref(v_a_63_);
v___x_71_ = lean_apply_3(v_h__2_65_, v_a_68_, v_a_69_, v_a_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg(lean_object* v_a_72_, lean_object* v_n_73_){
_start:
{
if (lean_obj_tag(v_a_72_) == 0)
{
lean_object* v_a_74_; 
v_a_74_ = lean_ctor_get(v_a_72_, 0);
lean_inc(v_a_74_);
return v_a_74_;
}
else
{
lean_object* v_a_75_; lean_object* v_a_76_; lean_object* v_a_77_; uint8_t v___x_78_; 
v_a_75_ = lean_ctor_get(v_a_72_, 0);
v_a_76_ = lean_ctor_get(v_a_72_, 1);
v_a_77_ = lean_ctor_get(v_a_72_, 2);
v___x_78_ = lean_nat_dec_lt(v_n_73_, v_a_75_);
if (v___x_78_ == 0)
{
v_a_72_ = v_a_77_;
goto _start;
}
else
{
v_a_72_ = v_a_76_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg___boxed(lean_object* v_a_81_, lean_object* v_n_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_RArray_getImpl___redArg(v_a_81_, v_n_82_);
lean_dec(v_n_82_);
lean_dec_ref(v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl(lean_object* v_00_u03b1_84_, lean_object* v_a_85_, lean_object* v_n_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_RArray_getImpl___redArg(v_a_85_, v_n_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___boxed(lean_object* v_00_u03b1_88_, lean_object* v_a_89_, lean_object* v_n_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_RArray_getImpl(v_00_u03b1_88_, v_a_89_, v_n_90_);
lean_dec(v_n_90_);
lean_dec_ref(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(lean_object* v_a_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
if (lean_obj_tag(v_a_92_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_94_);
v_a_95_ = lean_ctor_get(v_a_92_, 0);
lean_inc(v_a_95_);
lean_dec_ref(v_a_92_);
v___x_96_ = lean_apply_1(v_h__1_93_, v_a_95_);
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v___x_100_; 
lean_dec(v_h__1_93_);
v_a_97_ = lean_ctor_get(v_a_92_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v_a_92_, 1);
lean_inc_ref(v_a_98_);
v_a_99_ = lean_ctor_get(v_a_92_, 2);
lean_inc_ref(v_a_99_);
lean_dec_ref(v_a_92_);
v___x_100_ = lean_apply_3(v_h__2_94_, v_a_97_, v_a_98_, v_a_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(lean_object* v_00_u03b1_101_, lean_object* v_motive_102_, lean_object* v_a_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_){
_start:
{
if (lean_obj_tag(v_a_103_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_h__2_105_);
v_a_106_ = lean_ctor_get(v_a_103_, 0);
lean_inc(v_a_106_);
lean_dec_ref(v_a_103_);
v___x_107_ = lean_apply_1(v_h__1_104_, v_a_106_);
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v___x_111_; 
lean_dec(v_h__1_104_);
v_a_108_ = lean_ctor_get(v_a_103_, 0);
lean_inc(v_a_108_);
v_a_109_ = lean_ctor_get(v_a_103_, 1);
lean_inc_ref(v_a_109_);
v_a_110_ = lean_ctor_get(v_a_103_, 2);
lean_inc_ref(v_a_110_);
lean_dec_ref(v_a_103_);
v___x_111_ = lean_apply_3(v_h__2_105_, v_a_108_, v_a_109_, v_a_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___lam__0(lean_object* v_a_112_, lean_object* v_n_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_RArray_getImpl___redArg(v_a_112_, v_n_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___lam__0___boxed(lean_object* v_a_116_, lean_object* v_n_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_instGetElemRArrayNatTrue___lam__0(v_a_116_, v_n_117_, v_x_118_);
lean_dec(v_n_117_);
lean_dec_ref(v_a_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue(lean_object* v_00_u03b1_121_){
_start:
{
lean_object* v___f_122_; 
v___f_122_ = ((lean_object*)(l_Lean_instGetElemRArrayNatTrue___closed__0));
return v___f_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg(lean_object* v_x_123_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(1u);
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_a_125_ = lean_ctor_get(v_x_123_, 1);
v_a_126_ = lean_ctor_get(v_x_123_, 2);
v___x_127_ = l_Lean_RArray_size___redArg(v_a_125_);
v___x_128_ = l_Lean_RArray_size___redArg(v_a_126_);
v___x_129_ = lean_nat_add(v___x_127_, v___x_128_);
lean_dec(v___x_128_);
lean_dec(v___x_127_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg___boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_RArray_size___redArg(v_x_130_);
lean_dec_ref(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size(lean_object* v_00_u03b1_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_RArray_size___redArg(v_x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___boxed(lean_object* v_00_u03b1_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_RArray_size(v_00_u03b1_135_, v_x_136_);
lean_dec_ref(v_x_136_);
return v_res_137_;
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_RArray(builtin);
}
#ifdef __cplusplus
}
#endif
