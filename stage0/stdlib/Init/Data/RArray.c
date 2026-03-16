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
lean_object* v___x_66_; 
v___x_66_ = l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___redArg(v_a_63_, v_h__1_64_, v_h__2_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg(lean_object* v_a_67_, lean_object* v_n_68_){
_start:
{
if (lean_obj_tag(v_a_67_) == 0)
{
lean_object* v_a_69_; 
v_a_69_ = lean_ctor_get(v_a_67_, 0);
lean_inc(v_a_69_);
return v_a_69_;
}
else
{
lean_object* v_a_70_; lean_object* v_a_71_; lean_object* v_a_72_; uint8_t v___x_73_; 
v_a_70_ = lean_ctor_get(v_a_67_, 0);
v_a_71_ = lean_ctor_get(v_a_67_, 1);
v_a_72_ = lean_ctor_get(v_a_67_, 2);
v___x_73_ = lean_nat_dec_lt(v_n_68_, v_a_70_);
if (v___x_73_ == 0)
{
v_a_67_ = v_a_72_;
goto _start;
}
else
{
v_a_67_ = v_a_71_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg___boxed(lean_object* v_a_76_, lean_object* v_n_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_RArray_getImpl___redArg(v_a_76_, v_n_77_);
lean_dec(v_n_77_);
lean_dec_ref(v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl(lean_object* v_00_u03b1_79_, lean_object* v_a_80_, lean_object* v_n_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_RArray_getImpl___redArg(v_a_80_, v_n_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___boxed(lean_object* v_00_u03b1_83_, lean_object* v_a_84_, lean_object* v_n_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_RArray_getImpl(v_00_u03b1_83_, v_a_84_, v_n_85_);
lean_dec(v_n_85_);
lean_dec_ref(v_a_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(lean_object* v_a_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_){
_start:
{
if (lean_obj_tag(v_a_87_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_89_);
v_a_90_ = lean_ctor_get(v_a_87_, 0);
lean_inc(v_a_90_);
lean_dec_ref(v_a_87_);
v___x_91_ = lean_apply_1(v_h__1_88_, v_a_90_);
return v___x_91_;
}
else
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v_a_94_; lean_object* v___x_95_; 
lean_dec(v_h__1_88_);
v_a_92_ = lean_ctor_get(v_a_87_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v_a_87_, 1);
lean_inc_ref(v_a_93_);
v_a_94_ = lean_ctor_get(v_a_87_, 2);
lean_inc_ref(v_a_94_);
lean_dec_ref(v_a_87_);
v___x_95_ = lean_apply_3(v_h__2_89_, v_a_92_, v_a_93_, v_a_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(lean_object* v_00_u03b1_96_, lean_object* v_motive_97_, lean_object* v_a_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(v_a_98_, v_h__1_99_, v_h__2_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___lam__0(lean_object* v_a_102_, lean_object* v_n_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_RArray_getImpl___redArg(v_a_102_, v_n_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___lam__0___boxed(lean_object* v_a_106_, lean_object* v_n_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_instGetElemRArrayNatTrue___lam__0(v_a_106_, v_n_107_, v_x_108_);
lean_dec(v_n_107_);
lean_dec_ref(v_a_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue(lean_object* v_00_u03b1_111_){
_start:
{
lean_object* v___f_112_; 
v___f_112_ = ((lean_object*)(l_Lean_instGetElemRArrayNatTrue___closed__0));
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg(lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_unsigned_to_nat(1u);
return v___x_114_;
}
else
{
lean_object* v_a_115_; lean_object* v_a_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_115_ = lean_ctor_get(v_x_113_, 1);
v_a_116_ = lean_ctor_get(v_x_113_, 2);
v___x_117_ = l_Lean_RArray_size___redArg(v_a_115_);
v___x_118_ = l_Lean_RArray_size___redArg(v_a_116_);
v___x_119_ = lean_nat_add(v___x_117_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_117_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg___boxed(lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_RArray_size___redArg(v_x_120_);
lean_dec_ref(v_x_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size(lean_object* v_00_u03b1_122_, lean_object* v_x_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_RArray_size___redArg(v_x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___boxed(lean_object* v_00_u03b1_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_RArray_size(v_00_u03b1_125_, v_x_126_);
lean_dec_ref(v_x_126_);
return v_res_127_;
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
