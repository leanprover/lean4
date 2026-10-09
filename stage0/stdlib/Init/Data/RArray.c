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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instGetElemRArrayNatTrue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instGetElemRArrayNatTrue___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instGetElemRArrayNatTrue___redArg___closed__0 = (const lean_object*)&l_Lean_instGetElemRArrayNatTrue___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___redArg();
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_RArray_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_RArray_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_16_);
v_a_17_ = lean_ctor_get(v_t_11_, 2);
lean_inc_ref(v_a_17_);
lean_dec_ref_known(v_t_11_, 3);
v___x_18_ = lean_apply_3(v_k_12_, v_a_15_, v_a_16_, v_a_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim(lean_object* v_00_u03b1_19_, lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_RArray_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ctorElim___boxed(lean_object* v_00_u03b1_26_, lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_RArray_ctorElim(v_00_u03b1_26_, v_motive_27_, v_ctorIdx_28_, v_t_29_, v_h_30_, v_k_31_);
lean_dec(v_ctorIdx_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_leaf_elim___redArg(lean_object* v_t_33_, lean_object* v_leaf_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_RArray_ctorElim___redArg(v_t_33_, v_leaf_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_leaf_elim(lean_object* v_00_u03b1_36_, lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_leaf_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_RArray_ctorElim___redArg(v_t_38_, v_leaf_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_branch_elim___redArg(lean_object* v_t_42_, lean_object* v_branch_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_RArray_ctorElim___redArg(v_t_42_, v_branch_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_branch_elim(lean_object* v_00_u03b1_45_, lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_branch_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_RArray_ctorElim___redArg(v_t_47_, v_branch_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___redArg(lean_object* v_a_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_a_51_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_53_);
v_a_54_ = lean_ctor_get(v_a_51_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v_a_51_, 1);
v___x_55_ = lean_apply_1(v_h__1_52_, v_a_54_);
return v___x_55_;
}
else
{
lean_object* v_a_56_; lean_object* v_a_57_; lean_object* v_a_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_52_);
v_a_56_ = lean_ctor_get(v_a_51_, 0);
lean_inc(v_a_56_);
v_a_57_ = lean_ctor_get(v_a_51_, 1);
lean_inc_ref(v_a_57_);
v_a_58_ = lean_ctor_get(v_a_51_, 2);
lean_inc_ref(v_a_58_);
lean_dec_ref_known(v_a_51_, 3);
v___x_59_ = lean_apply_3(v_h__2_53_, v_a_56_, v_a_57_, v_a_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter(lean_object* v_00_u03b1_60_, lean_object* v_motive_61_, lean_object* v_a_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_66_; 
lean_dec(v_h__2_64_);
v_a_65_ = lean_ctor_get(v_a_62_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v_a_62_, 1);
v___x_66_ = lean_apply_1(v_h__1_63_, v_a_65_);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_70_; 
lean_dec(v_h__1_63_);
v_a_67_ = lean_ctor_get(v_a_62_, 0);
lean_inc(v_a_67_);
v_a_68_ = lean_ctor_get(v_a_62_, 1);
lean_inc_ref(v_a_68_);
v_a_69_ = lean_ctor_get(v_a_62_, 2);
lean_inc_ref(v_a_69_);
lean_dec_ref_known(v_a_62_, 3);
v___x_70_ = lean_apply_3(v_h__2_64_, v_a_67_, v_a_68_, v_a_69_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg(lean_object* v_a_71_, lean_object* v_n_72_){
_start:
{
if (lean_obj_tag(v_a_71_) == 0)
{
lean_object* v_a_73_; 
v_a_73_ = lean_ctor_get(v_a_71_, 0);
lean_inc(v_a_73_);
return v_a_73_;
}
else
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v_a_76_; uint8_t v___x_77_; 
v_a_74_ = lean_ctor_get(v_a_71_, 0);
v_a_75_ = lean_ctor_get(v_a_71_, 1);
v_a_76_ = lean_ctor_get(v_a_71_, 2);
v___x_77_ = lean_nat_dec_lt(v_n_72_, v_a_74_);
if (v___x_77_ == 0)
{
v_a_71_ = v_a_76_;
goto _start;
}
else
{
v_a_71_ = v_a_75_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___redArg___boxed(lean_object* v_a_80_, lean_object* v_n_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_RArray_getImpl___redArg(v_a_80_, v_n_81_);
lean_dec(v_n_81_);
lean_dec_ref(v_a_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl(lean_object* v_00_u03b1_83_, lean_object* v_a_84_, lean_object* v_n_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_RArray_getImpl___redArg(v_a_84_, v_n_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_getImpl___boxed(lean_object* v_00_u03b1_87_, lean_object* v_a_88_, lean_object* v_n_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_RArray_getImpl(v_00_u03b1_87_, v_a_88_, v_n_89_);
lean_dec(v_n_89_);
lean_dec_ref(v_a_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___redArg___lam__0(lean_object* v_a_91_, lean_object* v_n_92_, lean_object* v_x_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_RArray_getImpl___redArg(v_a_91_, v_n_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___redArg___lam__0___boxed(lean_object* v_a_95_, lean_object* v_n_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_instGetElemRArrayNatTrue___redArg___lam__0(v_a_95_, v_n_96_, v_x_97_);
lean_dec(v_n_96_);
lean_dec_ref(v_a_95_);
return v_res_98_;
}
}
lean_object* l_Lean_instGetElemRArrayNatTrue___redArg(){
_start:
{
lean_object* v___f_101_; 
v___f_101_ = ((lean_object*)(l_Lean_instGetElemRArrayNatTrue___redArg___closed__0));
return v___f_101_;
}
}
LEAN_EXPORT void l_Lean_instGetElemRArrayNatTrue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_102_;
v_res_102_ = l_Lean_instGetElemRArrayNatTrue___redArg();
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue___redArg___boxed(lean_object* v___dummy_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_instGetElemRArrayNatTrue___redArg();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemRArrayNatTrue(lean_object* v_00_u03b1_105_){
_start:
{
lean_object* v___f_106_; 
v___f_106_ = ((lean_object*)(l_Lean_instGetElemRArrayNatTrue___redArg___closed__0));
return v___f_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg(lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_unsigned_to_nat(1u);
return v___x_108_;
}
else
{
lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_a_109_ = lean_ctor_get(v_x_107_, 1);
v_a_110_ = lean_ctor_get(v_x_107_, 2);
v___x_111_ = l_Lean_RArray_size___redArg(v_a_109_);
v___x_112_ = l_Lean_RArray_size___redArg(v_a_110_);
v___x_113_ = lean_nat_add(v___x_111_, v___x_112_);
lean_dec(v___x_112_);
lean_dec(v___x_111_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___redArg___boxed(lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_RArray_size___redArg(v_x_114_);
lean_dec_ref(v_x_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size(lean_object* v_00_u03b1_116_, lean_object* v_x_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_RArray_size___redArg(v_x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_size___boxed(lean_object* v_00_u03b1_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_RArray_size(v_00_u03b1_119_, v_x_120_);
lean_dec_ref(v_x_120_);
return v_res_121_;
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
