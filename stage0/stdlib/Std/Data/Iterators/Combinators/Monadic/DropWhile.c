// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.DropWhile
// Imports: public import Init.Data.Nat.Lemmas public import Init.Data.Iterators.Consumers.Monadic.Collect public import Init.Data.Iterators.Consumers.Monadic.Loop public import Init.Data.Iterators.PostconditionMonad
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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(uint8_t v_dropping_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3_, 0, v_it_2_);
lean_ctor_set_uint8(v___x_3_, sizeof(void*)*1, v_dropping_1_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_dropping_1_ = stack[0].m_num;
lean_object* v_it_2_ = stack[1].m_obj;
lean_object* v_res_4_;
v_res_4_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(v_dropping_1_, v_it_2_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg___boxed(lean_object* v_dropping_5_, lean_object* v_it_6_){
_start:
{
uint8_t v_dropping_boxed_7_; lean_object* v_res_8_; 
v_dropping_boxed_7_ = lean_unbox(v_dropping_5_);
v_res_8_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(v_dropping_boxed_7_, v_it_6_);
return v_res_8_;
}
}
lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition(lean_object* v_00_u03b1_9_, lean_object* v_m_10_, lean_object* v_00_u03b2_11_, lean_object* v_P_12_, uint8_t v_dropping_13_, lean_object* v_it_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_15_, 0, v_it_14_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*1, v_dropping_13_);
return v___x_15_;
}
}
LEAN_EXPORT void l_Std_IterM_Intermediate_dropWhileWithPostcondition_0interp(lean_interpreter_value* stack)
{
lean_object* v_P_12_ = stack[3].m_obj;
uint8_t v_dropping_13_ = stack[4].m_num;
lean_object* v_it_14_ = stack[5].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition(lean_box(0), lean_box(0), lean_box(0), v_P_12_, v_dropping_13_, v_it_14_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___boxed(lean_object* v_00_u03b1_17_, lean_object* v_m_18_, lean_object* v_00_u03b2_19_, lean_object* v_P_20_, lean_object* v_dropping_21_, lean_object* v_it_22_){
_start:
{
uint8_t v_dropping_boxed_23_; lean_object* v_res_24_; 
v_dropping_boxed_23_ = lean_unbox(v_dropping_21_);
v_res_24_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition(v_00_u03b1_17_, v_m_18_, v_00_u03b2_19_, v_P_20_, v_dropping_boxed_23_, v_it_22_);
lean_dec(v_P_20_);
return v_res_24_;
}
}
lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg(uint8_t v_dropping_25_, lean_object* v_it_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_27_, 0, v_it_26_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*1, v_dropping_25_);
return v___x_27_;
}
}
LEAN_EXPORT void l_Std_IterM_Intermediate_dropWhileM___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_dropping_25_ = stack[0].m_num;
lean_object* v_it_26_ = stack[1].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Std_IterM_Intermediate_dropWhileM___redArg(v_dropping_25_, v_it_26_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg___boxed(lean_object* v_dropping_29_, lean_object* v_it_30_){
_start:
{
uint8_t v_dropping_boxed_31_; lean_object* v_res_32_; 
v_dropping_boxed_31_ = lean_unbox(v_dropping_29_);
v_res_32_ = l_Std_IterM_Intermediate_dropWhileM___redArg(v_dropping_boxed_31_, v_it_30_);
return v_res_32_;
}
}
lean_object* l_Std_IterM_Intermediate_dropWhileM(lean_object* v_00_u03b1_33_, lean_object* v_m_34_, lean_object* v_00_u03b2_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_P_38_, uint8_t v_dropping_39_, lean_object* v_it_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_41_, 0, v_it_40_);
lean_ctor_set_uint8(v___x_41_, sizeof(void*)*1, v_dropping_39_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Std_IterM_Intermediate_dropWhileM_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_36_ = stack[3].m_obj;
lean_object* v_inst_37_ = stack[4].m_obj;
lean_object* v_P_38_ = stack[5].m_obj;
uint8_t v_dropping_39_ = stack[6].m_num;
lean_object* v_it_40_ = stack[7].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Std_IterM_Intermediate_dropWhileM(lean_box(0), lean_box(0), lean_box(0), v_inst_36_, v_inst_37_, v_P_38_, v_dropping_39_, v_it_40_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___boxed(lean_object* v_00_u03b1_43_, lean_object* v_m_44_, lean_object* v_00_u03b2_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_P_48_, lean_object* v_dropping_49_, lean_object* v_it_50_){
_start:
{
uint8_t v_dropping_boxed_51_; lean_object* v_res_52_; 
v_dropping_boxed_51_ = lean_unbox(v_dropping_49_);
v_res_52_ = l_Std_IterM_Intermediate_dropWhileM(v_00_u03b1_43_, v_m_44_, v_00_u03b2_45_, v_inst_46_, v_inst_47_, v_P_48_, v_dropping_boxed_51_, v_it_50_);
lean_dec(v_P_48_);
lean_dec(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_52_;
}
}
lean_object* l_Std_IterM_Intermediate_dropWhile___redArg(uint8_t v_dropping_53_, lean_object* v_it_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_55_, 0, v_it_54_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*1, v_dropping_53_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Std_IterM_Intermediate_dropWhile___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_dropping_53_ = stack[0].m_num;
lean_object* v_it_54_ = stack[1].m_obj;
lean_object* v_res_56_;
v_res_56_ = l_Std_IterM_Intermediate_dropWhile___redArg(v_dropping_53_, v_it_54_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___redArg___boxed(lean_object* v_dropping_57_, lean_object* v_it_58_){
_start:
{
uint8_t v_dropping_boxed_59_; lean_object* v_res_60_; 
v_dropping_boxed_59_ = lean_unbox(v_dropping_57_);
v_res_60_ = l_Std_IterM_Intermediate_dropWhile___redArg(v_dropping_boxed_59_, v_it_58_);
return v_res_60_;
}
}
lean_object* l_Std_IterM_Intermediate_dropWhile(lean_object* v_00_u03b1_61_, lean_object* v_m_62_, lean_object* v_00_u03b2_63_, lean_object* v_inst_64_, lean_object* v_P_65_, uint8_t v_dropping_66_, lean_object* v_it_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_68_, 0, v_it_67_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*1, v_dropping_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Std_IterM_Intermediate_dropWhile_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_64_ = stack[3].m_obj;
lean_object* v_P_65_ = stack[4].m_obj;
uint8_t v_dropping_66_ = stack[5].m_num;
lean_object* v_it_67_ = stack[6].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Std_IterM_Intermediate_dropWhile(lean_box(0), lean_box(0), lean_box(0), v_inst_64_, v_P_65_, v_dropping_66_, v_it_67_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___boxed(lean_object* v_00_u03b1_70_, lean_object* v_m_71_, lean_object* v_00_u03b2_72_, lean_object* v_inst_73_, lean_object* v_P_74_, lean_object* v_dropping_75_, lean_object* v_it_76_){
_start:
{
uint8_t v_dropping_boxed_77_; lean_object* v_res_78_; 
v_dropping_boxed_77_ = lean_unbox(v_dropping_75_);
v_res_78_ = l_Std_IterM_Intermediate_dropWhile(v_00_u03b1_70_, v_m_71_, v_00_u03b2_72_, v_inst_73_, v_P_74_, v_dropping_boxed_77_, v_it_76_);
lean_dec_ref(v_P_74_);
lean_dec_ref(v_inst_73_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___redArg(lean_object* v_it_79_){
_start:
{
uint8_t v___x_80_; lean_object* v___x_81_; 
v___x_80_ = 1;
v___x_81_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_81_, 0, v_it_79_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition(lean_object* v_00_u03b1_82_, lean_object* v_m_83_, lean_object* v_00_u03b2_84_, lean_object* v_P_85_, lean_object* v_it_86_){
_start:
{
uint8_t v___x_87_; lean_object* v___x_88_; 
v___x_87_ = 1;
v___x_88_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_88_, 0, v_it_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___boxed(lean_object* v_00_u03b1_89_, lean_object* v_m_90_, lean_object* v_00_u03b2_91_, lean_object* v_P_92_, lean_object* v_it_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_IterM_dropWhileWithPostcondition(v_00_u03b1_89_, v_m_90_, v_00_u03b2_91_, v_P_92_, v_it_93_);
lean_dec(v_P_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___redArg(lean_object* v_it_95_){
_start:
{
uint8_t v___x_96_; lean_object* v___x_97_; 
v___x_96_ = 1;
v___x_97_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_97_, 0, v_it_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM(lean_object* v_00_u03b1_98_, lean_object* v_m_99_, lean_object* v_00_u03b2_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_P_103_, lean_object* v_it_104_){
_start:
{
uint8_t v___x_105_; lean_object* v___x_106_; 
v___x_105_ = 1;
v___x_106_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_106_, 0, v_it_104_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___boxed(lean_object* v_00_u03b1_107_, lean_object* v_m_108_, lean_object* v_00_u03b2_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_P_112_, lean_object* v_it_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_IterM_dropWhileM(v_00_u03b1_107_, v_m_108_, v_00_u03b2_109_, v_inst_110_, v_inst_111_, v_P_112_, v_it_113_);
lean_dec(v_P_112_);
lean_dec(v_inst_111_);
lean_dec_ref(v_inst_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___redArg(lean_object* v_it_115_){
_start:
{
uint8_t v___x_116_; lean_object* v___x_117_; 
v___x_116_ = 1;
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v_it_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile(lean_object* v_00_u03b1_118_, lean_object* v_m_119_, lean_object* v_00_u03b2_120_, lean_object* v_inst_121_, lean_object* v_P_122_, lean_object* v_it_123_){
_start:
{
uint8_t v___x_124_; lean_object* v___x_125_; 
v___x_124_ = 1;
v___x_125_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_125_, 0, v_it_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___boxed(lean_object* v_00_u03b1_126_, lean_object* v_m_127_, lean_object* v_00_u03b2_128_, lean_object* v_inst_129_, lean_object* v_P_130_, lean_object* v_it_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_IterM_dropWhile(v_00_u03b1_126_, v_m_127_, v_00_u03b2_128_, v_inst_129_, v_P_130_, v_it_131_);
lean_dec_ref(v_P_130_);
lean_dec_ref(v_inst_129_);
return v_res_132_;
}
}
lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(lean_object* v_it_133_, lean_object* v_out_134_, lean_object* v_toPure_135_, uint8_t v_dropping_136_, uint8_t v_____do__lift_137_){
_start:
{
if (v_____do__lift_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_138_, 0, v_it_133_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v_____do__lift_137_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_out_134_);
v___x_140_ = lean_apply_2(v_toPure_135_, lean_box(0), v___x_139_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_out_134_);
v___x_141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_141_, 0, v_it_133_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v_dropping_136_);
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
v___x_143_ = lean_apply_2(v_toPure_135_, lean_box(0), v___x_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT void l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_133_ = stack[0].m_obj;
lean_object* v_out_134_ = stack[1].m_obj;
lean_object* v_toPure_135_ = stack[2].m_obj;
uint8_t v_dropping_136_ = stack[3].m_num;
uint8_t v_____do__lift_137_ = stack[4].m_num;
lean_object* v_res_144_;
v_res_144_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(v_it_133_, v_out_134_, v_toPure_135_, v_dropping_136_, v_____do__lift_137_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed(lean_object* v_it_145_, lean_object* v_out_146_, lean_object* v_toPure_147_, lean_object* v_dropping_148_, lean_object* v_____do__lift_149_){
_start:
{
uint8_t v_dropping_boxed_150_; uint8_t v_____do__lift_247__boxed_151_; lean_object* v_res_152_; 
v_dropping_boxed_150_ = lean_unbox(v_dropping_148_);
v_____do__lift_247__boxed_151_ = lean_unbox(v_____do__lift_149_);
v_res_152_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(v_it_145_, v_out_146_, v_toPure_147_, v_dropping_boxed_150_, v_____do__lift_247__boxed_151_);
return v_res_152_;
}
}
lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(uint8_t v_dropping_153_, lean_object* v_toPure_154_, lean_object* v_P_155_, lean_object* v_toBind_156_, lean_object* v_____do__lift_157_){
_start:
{
switch(lean_obj_tag(v_____do__lift_157_))
{
case 0:
{
if (v_dropping_153_ == 0)
{
lean_object* v_it_158_; lean_object* v_out_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_168_; 
lean_dec(v_toBind_156_);
lean_dec(v_P_155_);
v_it_158_ = lean_ctor_get(v_____do__lift_157_, 0);
v_out_159_ = lean_ctor_get(v_____do__lift_157_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_____do__lift_157_);
if (v_isSharedCheck_168_ == 0)
{
v___x_161_ = v_____do__lift_157_;
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_out_159_);
lean_inc(v_it_158_);
lean_dec(v_____do__lift_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_163_, 0, v_it_158_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v_dropping_153_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_out_159_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; 
v___x_166_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_165_);
return v___x_166_;
}
}
}
else
{
lean_object* v_it_169_; lean_object* v_out_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_it_169_ = lean_ctor_get(v_____do__lift_157_, 0);
lean_inc(v_it_169_);
v_out_170_ = lean_ctor_get(v_____do__lift_157_, 1);
lean_inc_n(v_out_170_, 2);
lean_dec_ref_known(v_____do__lift_157_, 2);
v___x_171_ = lean_box(v_dropping_153_);
v___f_172_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_172_, 0, v_it_169_);
lean_closure_set(v___f_172_, 1, v_out_170_);
lean_closure_set(v___f_172_, 2, v_toPure_154_);
lean_closure_set(v___f_172_, 3, v___x_171_);
v___x_173_ = lean_apply_1(v_P_155_, v_out_170_);
v___x_174_ = lean_apply_4(v_toBind_156_, lean_box(0), lean_box(0), v___x_173_, v___f_172_);
return v___x_174_;
}
}
case 1:
{
lean_object* v_it_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_toBind_156_);
lean_dec(v_P_155_);
v_it_175_ = lean_ctor_get(v_____do__lift_157_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v_____do__lift_157_);
if (v_isSharedCheck_184_ == 0)
{
v___x_177_ = v_____do__lift_157_;
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_it_175_);
lean_dec(v_____do__lift_157_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_179_, 0, v_it_175_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v_dropping_153_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_181_);
return v___x_182_;
}
}
}
default: 
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_toBind_156_);
lean_dec(v_P_155_);
v___x_185_ = lean_box(2);
v___x_186_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_185_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT void l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_dropping_153_ = stack[0].m_num;
lean_object* v_toPure_154_ = stack[1].m_obj;
lean_object* v_P_155_ = stack[2].m_obj;
lean_object* v_toBind_156_ = stack[3].m_obj;
lean_object* v_____do__lift_157_ = stack[4].m_obj;
lean_object* v_res_187_;
v_res_187_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(v_dropping_153_, v_toPure_154_, v_P_155_, v_toBind_156_, v_____do__lift_157_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed(lean_object* v_dropping_188_, lean_object* v_toPure_189_, lean_object* v_P_190_, lean_object* v_toBind_191_, lean_object* v_____do__lift_192_){
_start:
{
uint8_t v_dropping_boxed_193_; lean_object* v_res_194_; 
v_dropping_boxed_193_ = lean_unbox(v_dropping_188_);
v_res_194_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(v_dropping_boxed_193_, v_toPure_189_, v_P_190_, v_toBind_191_, v_____do__lift_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2(lean_object* v_toPure_195_, lean_object* v_P_196_, lean_object* v_toBind_197_, lean_object* v_inst_198_, lean_object* v_it_199_){
_start:
{
uint8_t v_dropping_200_; lean_object* v_inner_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_dropping_200_ = lean_ctor_get_uint8(v_it_199_, sizeof(void*)*1);
v_inner_201_ = lean_ctor_get(v_it_199_, 0);
lean_inc(v_inner_201_);
lean_dec_ref(v_it_199_);
v___x_202_ = lean_box(v_dropping_200_);
lean_inc(v_toBind_197_);
v___f_203_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_203_, 0, v___x_202_);
lean_closure_set(v___f_203_, 1, v_toPure_195_);
lean_closure_set(v___f_203_, 2, v_P_196_);
lean_closure_set(v___f_203_, 3, v_toBind_197_);
v___x_204_ = lean_apply_1(v_inst_198_, v_inner_201_);
v___x_205_ = lean_apply_4(v_toBind_197_, lean_box(0), lean_box(0), v___x_204_, v___f_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_P_208_){
_start:
{
lean_object* v_toApplicative_209_; lean_object* v_toBind_210_; lean_object* v_toPure_211_; lean_object* v___f_212_; 
v_toApplicative_209_ = lean_ctor_get(v_inst_206_, 0);
lean_inc_ref(v_toApplicative_209_);
v_toBind_210_ = lean_ctor_get(v_inst_206_, 1);
lean_inc(v_toBind_210_);
lean_dec_ref(v_inst_206_);
v_toPure_211_ = lean_ctor_get(v_toApplicative_209_, 1);
lean_inc(v_toPure_211_);
lean_dec_ref(v_toApplicative_209_);
v___f_212_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2), 5, 4);
lean_closure_set(v___f_212_, 0, v_toPure_211_);
lean_closure_set(v___f_212_, 1, v_P_208_);
lean_closure_set(v___f_212_, 2, v_toBind_210_);
lean_closure_set(v___f_212_, 3, v_inst_207_);
return v___f_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator(lean_object* v_00_u03b1_213_, lean_object* v_m_214_, lean_object* v_00_u03b2_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_P_218_){
_start:
{
lean_object* v_toApplicative_219_; lean_object* v_toBind_220_; lean_object* v_toPure_221_; lean_object* v___f_222_; 
v_toApplicative_219_ = lean_ctor_get(v_inst_216_, 0);
lean_inc_ref(v_toApplicative_219_);
v_toBind_220_ = lean_ctor_get(v_inst_216_, 1);
lean_inc(v_toBind_220_);
lean_dec_ref(v_inst_216_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_inc(v_toPure_221_);
lean_dec_ref(v_toApplicative_219_);
v___f_222_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2), 5, 4);
lean_closure_set(v___f_222_, 0, v_toPure_221_);
lean_closure_set(v___f_222_, 1, v_P_218_);
lean_closure_set(v___f_222_, 2, v_toBind_220_);
lean_closure_set(v___f_222_, 3, v_inst_217_);
return v___f_222_;
}
}
lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_225_;
v_res_225_ = l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg();
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(lean_object* v_00_u03b1_228_, lean_object* v_m_229_, lean_object* v_00_u03b2_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_P_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_box(0);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___boxed(lean_object* v_00_u03b1_236_, lean_object* v_m_237_, lean_object* v_00_u03b2_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_P_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(v_00_u03b1_236_, v_m_237_, v_00_u03b2_238_, v_inst_239_, v_inst_240_, v_inst_241_, v_P_242_);
lean_dec(v_P_242_);
lean_dec(v_inst_240_);
lean_dec_ref(v_inst_239_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_244_, lean_object* v_recur_245_, lean_object* v_it_246_, lean_object* v_____do__lift_247_){
_start:
{
if (lean_obj_tag(v_____do__lift_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; 
lean_dec_ref(v_it_246_);
lean_dec(v_recur_245_);
v_a_248_ = lean_ctor_get(v_____do__lift_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v_____do__lift_247_, 1);
v___x_249_ = lean_apply_2(v_toPure_244_, lean_box(0), v_a_248_);
return v___x_249_;
}
else
{
lean_object* v_a_250_; lean_object* v___x_251_; 
lean_dec(v_toPure_244_);
v_a_250_ = lean_ctor_get(v_____do__lift_247_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v_____do__lift_247_, 1);
v___x_251_ = lean_apply_4(v_recur_245_, v_it_246_, v_a_250_, lean_box(0), lean_box(0));
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_252_, lean_object* v_recur_253_, lean_object* v___y_254_, lean_object* v_acc_255_, lean_object* v_toBind_256_, lean_object* v_s_257_){
_start:
{
switch(lean_obj_tag(v_s_257_))
{
case 0:
{
lean_object* v_it_258_; lean_object* v_out_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_it_258_ = lean_ctor_get(v_s_257_, 0);
lean_inc(v_it_258_);
v_out_259_ = lean_ctor_get(v_s_257_, 1);
lean_inc(v_out_259_);
lean_dec_ref_known(v_s_257_, 2);
v___f_260_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_260_, 0, v_toPure_252_);
lean_closure_set(v___f_260_, 1, v_recur_253_);
lean_closure_set(v___f_260_, 2, v_it_258_);
v___x_261_ = lean_apply_3(v___y_254_, v_out_259_, lean_box(0), v_acc_255_);
v___x_262_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v___x_261_, v___f_260_);
return v___x_262_;
}
case 1:
{
lean_object* v_it_263_; lean_object* v___x_264_; 
lean_dec(v_toBind_256_);
lean_dec(v___y_254_);
lean_dec(v_toPure_252_);
v_it_263_ = lean_ctor_get(v_s_257_, 0);
lean_inc(v_it_263_);
lean_dec_ref_known(v_s_257_, 1);
v___x_264_ = lean_apply_4(v_recur_253_, v_it_263_, v_acc_255_, lean_box(0), lean_box(0));
return v___x_264_;
}
default: 
{
lean_object* v___x_265_; 
lean_dec(v_toBind_256_);
lean_dec(v___y_254_);
lean_dec(v_recur_253_);
v___x_265_ = lean_apply_2(v_toPure_252_, lean_box(0), v_acc_255_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4(lean_object* v_inst_266_, lean_object* v_toPure_267_, lean_object* v___y_268_, lean_object* v_toBind_269_, lean_object* v_P_270_, lean_object* v_inst_271_, lean_object* v_lift_272_, lean_object* v_it_273_, lean_object* v_acc_274_, lean_object* v_hP_275_, lean_object* v_recur_276_){
_start:
{
lean_object* v_toApplicative_277_; lean_object* v_toBind_278_; lean_object* v_toPure_279_; uint8_t v_dropping_280_; lean_object* v_inner_281_; lean_object* v___f_282_; lean_object* v___x_283_; lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_toApplicative_277_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_toApplicative_277_);
v_toBind_278_ = lean_ctor_get(v_inst_266_, 1);
lean_inc_n(v_toBind_278_, 2);
lean_dec_ref(v_inst_266_);
v_toPure_279_ = lean_ctor_get(v_toApplicative_277_, 1);
lean_inc(v_toPure_279_);
lean_dec_ref(v_toApplicative_277_);
v_dropping_280_ = lean_ctor_get_uint8(v_it_273_, sizeof(void*)*1);
v_inner_281_ = lean_ctor_get(v_it_273_, 0);
lean_inc(v_inner_281_);
lean_dec_ref(v_it_273_);
v___f_282_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_282_, 0, v_toPure_267_);
lean_closure_set(v___f_282_, 1, v_recur_276_);
lean_closure_set(v___f_282_, 2, v___y_268_);
lean_closure_set(v___f_282_, 3, v_acc_274_);
lean_closure_set(v___f_282_, 4, v_toBind_269_);
v___x_283_ = lean_box(v_dropping_280_);
v___f_284_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_284_, 0, v___x_283_);
lean_closure_set(v___f_284_, 1, v_toPure_279_);
lean_closure_set(v___f_284_, 2, v_P_270_);
lean_closure_set(v___f_284_, 3, v_toBind_278_);
v___x_285_ = lean_apply_1(v_inst_271_, v_inner_281_);
v___x_286_ = lean_apply_4(v_toBind_278_, lean_box(0), lean_box(0), v___x_285_, v___f_284_);
v___x_287_ = lean_apply_4(v_lift_272_, lean_box(0), lean_box(0), v___f_282_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2(lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_P_290_, lean_object* v_inst_291_, lean_object* v_lift_292_, lean_object* v_00_u03b3_293_, lean_object* v_Pl_294_, lean_object* v_it_295_, lean_object* v_init_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_toApplicative_298_; lean_object* v_toBind_299_; lean_object* v_toPure_300_; lean_object* v___f_301_; lean_object* v___x_302_; 
v_toApplicative_298_ = lean_ctor_get(v_inst_288_, 0);
lean_inc_ref(v_toApplicative_298_);
v_toBind_299_ = lean_ctor_get(v_inst_288_, 1);
lean_inc(v_toBind_299_);
lean_dec_ref(v_inst_288_);
v_toPure_300_ = lean_ctor_get(v_toApplicative_298_, 1);
lean_inc(v_toPure_300_);
lean_dec_ref(v_toApplicative_298_);
v___f_301_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_301_, 0, v_inst_289_);
lean_closure_set(v___f_301_, 1, v_toPure_300_);
lean_closure_set(v___f_301_, 2, v___y_297_);
lean_closure_set(v___f_301_, 3, v_toBind_299_);
lean_closure_set(v___f_301_, 4, v_P_290_);
lean_closure_set(v___f_301_, 5, v_inst_291_);
lean_closure_set(v___f_301_, 6, v_lift_292_);
v___x_302_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_301_, v_it_295_, v_init_296_, lean_box(0));
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg(lean_object* v_P_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_){
_start:
{
lean_object* v___f_307_; 
v___f_307_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_307_, 0, v_inst_305_);
lean_closure_set(v___f_307_, 1, v_inst_304_);
lean_closure_set(v___f_307_, 2, v_P_303_);
lean_closure_set(v___f_307_, 3, v_inst_306_);
return v___f_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop(lean_object* v_00_u03b1_308_, lean_object* v_m_309_, lean_object* v_00_u03b2_310_, lean_object* v_n_311_, lean_object* v_P_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_){
_start:
{
lean_object* v___f_316_; 
v___f_316_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_316_, 0, v_inst_314_);
lean_closure_set(v___f_316_, 1, v_inst_313_);
lean_closure_set(v___f_316_, 2, v_P_312_);
lean_closure_set(v___f_316_, 3, v_inst_315_);
return v___f_316_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
}
#ifdef __cplusplus
}
#endif
