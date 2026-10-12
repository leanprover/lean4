// Lean compiler output
// Module: Init.Data.Vector.Lex
// Imports: import all Init.Data.Vector.Basic import all Init.Data.Array.Lex.Basic import Init.Data.Range.Polymorphic.Lemmas public import Init.Data.Array.Lex.Basic public import Init.Data.BEq public import Init.Data.Vector.Basic import Init.Data.Array.Lex.Lemmas import Init.Data.Vector.Lemmas
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Vector_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLt___redArg();
LEAN_EXPORT lean_object* l_Vector_instTransLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLTOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__2_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
lean_object* l_Vector_instTransLt___redArg(){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT void l_Vector_instTransLt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_19_;
v_res_19_ = l_Vector_instTransLt___redArg();
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Vector_instTransLt___redArg___boxed(lean_object* v___dummy_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Vector_instTransLt___redArg();
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt(lean_object* v_00_u03b1_22_, lean_object* v_n_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLt___boxed(lean_object* v_00_u03b1_27_, lean_object* v_n_28_, lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Vector_instTransLt(v_00_u03b1_27_, v_n_28_, v_inst_29_, v_inst_30_);
lean_dec(v_n_28_);
return v_res_31_;
}
}
lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg(){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
LEAN_EXPORT void l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_34_;
v_res_34_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg___boxed(lean_object* v___dummy_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object* v_00_u03b1_37_, lean_object* v_n_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___boxed(lean_object* v_00_u03b1_44_, lean_object* v_n_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(v_00_u03b1_44_, v_n_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_inst_49_);
lean_dec(v_n_45_);
return v_res_50_;
}
}
uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object* v_inst_51_, lean_object* v_x1_52_, lean_object* v_x2_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_apply_2(v_inst_51_, v_x1_52_, v_x2_53_);
v___x_55_ = lean_unbox(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_51_ = stack[0].m_obj;
lean_object* v_x1_52_ = stack[1].m_obj;
lean_object* v_x2_53_ = stack[2].m_obj;
uint8_t v_res_56_;
v_res_56_ = l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_51_, v_x1_52_, v_x2_53_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_57_, lean_object* v_x1_58_, lean_object* v_x2_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_57_, v_x1_58_, v_x2_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
uint8_t l_Vector_instDecidableLTOfDecidableEq___redArg(lean_object* v_n_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_xs_65_, lean_object* v_ys_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___f_68_; uint8_t v___x_69_; 
v___f_67_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_67_, 0, v_inst_64_);
v___f_68_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_68_, 0, v_inst_63_);
v___x_69_ = l_Vector_lex___redArg(v_n_62_, v___f_68_, v_xs_65_, v_ys_66_, v___f_67_);
return v___x_69_;
}
}
LEAN_EXPORT void l_Vector_instDecidableLTOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_62_ = stack[0].m_obj;
lean_object* v_inst_63_ = stack[1].m_obj;
lean_object* v_inst_64_ = stack[2].m_obj;
lean_object* v_xs_65_ = stack[3].m_obj;
lean_object* v_ys_66_ = stack[4].m_obj;
uint8_t v_res_70_;
v_res_70_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_62_, v_inst_63_, v_inst_64_, v_xs_65_, v_ys_66_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___redArg___boxed(lean_object* v_n_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_xs_74_, lean_object* v_ys_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_71_, v_inst_72_, v_inst_73_, v_xs_74_, v_ys_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
uint8_t l_Vector_instDecidableLTOfDecidableEq(lean_object* v_00_u03b1_78_, lean_object* v_n_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_xs_83_, lean_object* v_ys_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = l_Vector_instDecidableLTOfDecidableEq___redArg(v_n_79_, v_inst_80_, v_inst_82_, v_xs_83_, v_ys_84_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Vector_instDecidableLTOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_79_ = stack[1].m_obj;
lean_object* v_inst_80_ = stack[2].m_obj;
lean_object* v_inst_81_ = stack[3].m_obj;
lean_object* v_inst_82_ = stack[4].m_obj;
lean_object* v_xs_83_ = stack[5].m_obj;
lean_object* v_ys_84_ = stack[6].m_obj;
uint8_t v_res_86_;
v_res_86_ = l_Vector_instDecidableLTOfDecidableEq(lean_box(0), v_n_79_, v_inst_80_, v_inst_81_, v_inst_82_, v_xs_83_, v_ys_84_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLTOfDecidableEq___boxed(lean_object* v_00_u03b1_87_, lean_object* v_n_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_xs_92_, lean_object* v_ys_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Vector_instDecidableLTOfDecidableEq(v_00_u03b1_87_, v_n_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_xs_92_, v_ys_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object* v_n_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_xs_99_, lean_object* v_ys_100_){
_start:
{
lean_object* v___f_101_; lean_object* v___f_102_; uint8_t v___x_103_; 
v___f_101_ = lean_alloc_closure((void*)(l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_101_, 0, v_inst_98_);
v___f_102_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_102_, 0, v_inst_97_);
v___x_103_ = l_Vector_lex___redArg(v_n_96_, v___f_102_, v_ys_100_, v_xs_99_, v___f_101_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; 
v___x_104_ = 1;
return v___x_104_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
LEAN_EXPORT void l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_96_ = stack[0].m_obj;
lean_object* v_inst_97_ = stack[1].m_obj;
lean_object* v_inst_98_ = stack[2].m_obj;
lean_object* v_xs_99_ = stack[3].m_obj;
lean_object* v_ys_100_ = stack[4].m_obj;
uint8_t v_res_106_;
v_res_106_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_96_, v_inst_97_, v_inst_98_, v_xs_99_, v_ys_100_);
stack->m_num = v_res_106_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object* v_n_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_xs_110_, lean_object* v_ys_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_107_, v_inst_108_, v_inst_109_, v_xs_110_, v_ys_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint8_t l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(lean_object* v_00_u03b1_114_, lean_object* v_n_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_xs_119_, lean_object* v_ys_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_n_115_, v_inst_116_, v_inst_118_, v_xs_119_, v_ys_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l_Vector_instDecidableLEOfDecidableEqOfDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_115_ = stack[1].m_obj;
lean_object* v_inst_116_ = stack[2].m_obj;
lean_object* v_inst_117_ = stack[3].m_obj;
lean_object* v_inst_118_ = stack[4].m_obj;
lean_object* v_xs_119_ = stack[5].m_obj;
lean_object* v_ys_120_ = stack[6].m_obj;
uint8_t v_res_122_;
v_res_122_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(lean_box(0), v_n_115_, v_inst_116_, v_inst_117_, v_inst_118_, v_xs_119_, v_ys_120_);
stack->m_num = v_res_122_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object* v_00_u03b1_123_, lean_object* v_n_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_xs_128_, lean_object* v_ys_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(v_00_u03b1_123_, v_n_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_xs_128_, v_ys_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Lex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Lex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Lex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Lex(builtin);
}
#ifdef __cplusplus
}
#endif
