// Lean compiler output
// Module: Init.Control.Reader
// Imports: public import Init.Control.Except
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
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadControlReaderT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlReaderT___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadControlReaderT___closed__0 = (const lean_object*)&l_instMonadControlReaderT___closed__0_value;
static const lean_closure_object l_instMonadControlReaderT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlReaderT___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadControlReaderT___closed__1 = (const lean_object*)&l_instMonadControlReaderT___closed__1_value;
static const lean_ctor_object l_instMonadControlReaderT___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadControlReaderT___closed__0_value),((lean_object*)&l_instMonadControlReaderT___closed__1_value)}};
static const lean_object* l_instMonadControlReaderT___closed__2 = (const lean_object*)&l_instMonadControlReaderT___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachReaderTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachReaderTOfMonad___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachReaderTOfMonad___redArg___closed__0 = (const lean_object*)&l_instMonadAttachReaderTOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg___lam__0(lean_object* v_x_u2082_1_, lean_object* v_s_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_2(v_x_u2082_1_, v___x_4_, v_s_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg(lean_object* v_inst_6_, lean_object* v_x_u2081_7_, lean_object* v_x_u2082_8_, lean_object* v_s_9_){
_start:
{
lean_object* v_orElse_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_orElse_10_ = lean_ctor_get(v_inst_6_, 2);
lean_inc(v_orElse_10_);
lean_dec_ref(v_inst_6_);
lean_inc(v_s_9_);
v___f_11_ = lean_alloc_closure((void*)(l_ReaderT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_x_u2082_8_);
lean_closure_set(v___f_11_, 1, v_s_9_);
v___x_12_ = lean_apply_1(v_x_u2081_7_, v_s_9_);
v___x_13_ = lean_apply_3(v_orElse_10_, lean_box(0), v___x_12_, v___f_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse(lean_object* v_m_14_, lean_object* v_00_u03c1_15_, lean_object* v_00_u03b1_16_, lean_object* v_inst_17_, lean_object* v_x_u2081_18_, lean_object* v_x_u2082_19_, lean_object* v_s_20_){
_start:
{
lean_object* v_orElse_21_; lean_object* v___f_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_orElse_21_ = lean_ctor_get(v_inst_17_, 2);
lean_inc(v_orElse_21_);
lean_dec_ref(v_inst_17_);
lean_inc(v_s_20_);
v___f_22_ = lean_alloc_closure((void*)(l_ReaderT_orElse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v_x_u2082_19_);
lean_closure_set(v___f_22_, 1, v_s_20_);
v___x_23_ = lean_apply_1(v_x_u2081_18_, v_s_20_);
v___x_24_ = lean_apply_3(v_orElse_21_, lean_box(0), v___x_23_, v___f_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure___redArg(lean_object* v_inst_25_){
_start:
{
lean_object* v_failure_26_; lean_object* v___x_27_; 
v_failure_26_ = lean_ctor_get(v_inst_25_, 1);
lean_inc(v_failure_26_);
lean_dec_ref(v_inst_25_);
v___x_27_ = lean_apply_1(v_failure_26_, lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure(lean_object* v_m_28_, lean_object* v_00_u03c1_29_, lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_failure_33_; lean_object* v___x_34_; 
v_failure_33_ = lean_ctor_get(v_inst_31_, 1);
lean_inc(v_failure_33_);
lean_dec_ref(v_inst_31_);
v___x_34_ = lean_apply_1(v_failure_33_, lean_box(0));
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure___boxed(lean_object* v_m_35_, lean_object* v_00_u03c1_36_, lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_ReaderT_failure(v_m_35_, v_00_u03c1_36_, v_00_u03b1_37_, v_inst_38_, v_x_39_);
lean_dec(v_x_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0(lean_object* v_inst_41_, lean_object* v_00_u03b1_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_failure_44_; lean_object* v___x_45_; 
v_failure_44_ = lean_ctor_get(v_inst_41_, 1);
lean_inc(v_failure_44_);
lean_dec_ref(v_inst_41_);
v___x_45_ = lean_apply_1(v_failure_44_, lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object* v_inst_46_, lean_object* v_00_u03b1_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_ReaderT_instAlternativeOfMonad___redArg___lam__0(v_inst_46_, v_00_u03b1_47_, v___y_48_);
lean_dec(v___y_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__1(lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v_x_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_2(v___y_50_, v___x_53_, v___y_51_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__2(lean_object* v_inst_55_, lean_object* v_00_u03b1_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_orElse_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_orElse_60_ = lean_ctor_get(v_inst_55_, 2);
lean_inc(v_orElse_60_);
lean_dec_ref(v_inst_55_);
lean_inc(v___y_59_);
v___f_61_ = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(v___f_61_, 0, v___y_58_);
lean_closure_set(v___f_61_, 1, v___y_59_);
v___x_62_ = lean_apply_1(v___y_57_, v___y_59_);
v___x_63_ = lean_apply_3(v_orElse_60_, lean_box(0), v___x_62_, v___f_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object* v_inst_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v_toApplicative_66_; lean_object* v_toFunctor_67_; lean_object* v_toSeq_68_; lean_object* v_toSeqLeft_69_; lean_object* v_toSeqRight_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_87_; 
v_toApplicative_66_ = lean_ctor_get(v_inst_65_, 0);
lean_inc_ref(v_toApplicative_66_);
v_toFunctor_67_ = lean_ctor_get(v_toApplicative_66_, 0);
v_toSeq_68_ = lean_ctor_get(v_toApplicative_66_, 2);
v_toSeqLeft_69_ = lean_ctor_get(v_toApplicative_66_, 3);
v_toSeqRight_70_ = lean_ctor_get(v_toApplicative_66_, 4);
v_isSharedCheck_87_ = !lean_is_exclusive(v_toApplicative_66_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v_toApplicative_66_, 1);
lean_dec(v_unused_88_);
v___x_72_ = v_toApplicative_66_;
v_isShared_73_ = v_isSharedCheck_87_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_toSeqRight_70_);
lean_inc(v_toSeqLeft_69_);
lean_inc(v_toSeq_68_);
lean_inc(v_toFunctor_67_);
lean_dec(v_toApplicative_66_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_87_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_inc_ref(v_inst_64_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_74_, 0, v_inst_64_);
v___f_75_ = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_75_, 0, v_inst_64_);
v___f_76_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_76_, 0, v_toSeqRight_70_);
v___f_77_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_77_, 0, v_toSeqLeft_69_);
v___f_78_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_78_, 0, v_toSeq_68_);
lean_inc_ref(v_toFunctor_67_);
v___f_79_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_79_, 0, v_toFunctor_67_);
v___f_80_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_80_, 0, v_toFunctor_67_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___f_79_);
lean_ctor_set(v___x_81_, 1, v___f_80_);
v___x_82_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_82_, 0, lean_box(0));
lean_closure_set(v___x_82_, 1, lean_box(0));
lean_closure_set(v___x_82_, 2, v_inst_65_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 4, v___f_76_);
lean_ctor_set(v___x_72_, 3, v___f_77_);
lean_ctor_set(v___x_72_, 2, v___f_78_);
lean_ctor_set(v___x_72_, 1, v___x_82_);
lean_ctor_set(v___x_72_, 0, v___x_81_);
v___x_84_ = v___x_72_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v___f_78_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v___f_77_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v___f_76_);
v___x_84_ = v_reuseFailAlloc_86_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___f_74_);
lean_ctor_set(v___x_85_, 2, v___f_75_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad(lean_object* v_m_89_, lean_object* v_00_u03c1_90_, lean_object* v_inst_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_ReaderT_instAlternativeOfMonad___redArg(v_inst_91_, v_inst_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__0(lean_object* v_ctx_94_, lean_object* v_00_u03b2_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_1(v_x_96_, v_ctx_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__1(lean_object* v_00_u03b1_98_, lean_object* v_f_99_, lean_object* v_ctx_100_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_101_ = lean_alloc_closure((void*)(l_instMonadControlReaderT___lam__0), 3, 1);
lean_closure_set(v___f_101_, 0, v_ctx_100_);
v___x_102_ = lean_apply_1(v_f_99_, v___f_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2(lean_object* v_00_u03b1_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_inc(v_x_104_);
return v_x_104_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2___boxed(lean_object* v_00_u03b1_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_instMonadControlReaderT___lam__2(v_00_u03b1_106_, v_x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec(v_x_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT(lean_object* v_m_115_, lean_object* v_00_u03c1_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = ((lean_object*)(l_instMonadControlReaderT___closed__2));
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__0(lean_object* v_h_118_, lean_object* v_ctx_119_, lean_object* v_a_x3f_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_apply_2(v_h_118_, v_a_x3f_120_, v_ctx_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object* v_inst_122_, lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_x_125_, lean_object* v_h_126_, lean_object* v_ctx_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_inc(v_ctx_127_);
v___f_128_ = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__0), 3, 2);
lean_closure_set(v___f_128_, 0, v_h_126_);
lean_closure_set(v___f_128_, 1, v_ctx_127_);
v___x_129_ = lean_apply_1(v_x_125_, v_ctx_127_);
v___x_130_ = lean_apply_4(v_inst_122_, lean_box(0), lean_box(0), v___x_129_, v___f_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg(lean_object* v_inst_131_){
_start:
{
lean_object* v___f_132_; 
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(v___f_132_, 0, v_inst_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally(lean_object* v_m_133_, lean_object* v_00_u03c1_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v___f_136_; 
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(v___f_136_, 0, v_inst_135_);
return v___f_136_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg___lam__0(lean_object* v_x_137_){
_start:
{
lean_inc(v_x_137_);
return v_x_137_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg___lam__0___boxed(lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_instMonadAttachReaderTOfMonad___redArg___lam__0(v_x_138_);
lean_dec(v_x_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg___lam__1(lean_object* v_toFunctor_140_, lean_object* v_inst_141_, lean_object* v___f_142_, lean_object* v_00_u03b1_143_, lean_object* v_x_144_, lean_object* v_r_145_){
_start:
{
lean_object* v_map_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_map_146_ = lean_ctor_get(v_toFunctor_140_, 0);
lean_inc(v_map_146_);
lean_dec_ref(v_toFunctor_140_);
v___x_147_ = lean_apply_1(v_x_144_, v_r_145_);
v___x_148_ = lean_apply_2(v_inst_141_, lean_box(0), v___x_147_);
v___x_149_ = lean_apply_4(v_map_146_, lean_box(0), lean_box(0), v___f_142_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad___redArg(lean_object* v_inst_151_, lean_object* v_inst_152_){
_start:
{
lean_object* v_toApplicative_153_; lean_object* v_toFunctor_154_; lean_object* v___f_155_; lean_object* v___f_156_; 
v_toApplicative_153_ = lean_ctor_get(v_inst_151_, 0);
lean_inc_ref(v_toApplicative_153_);
lean_dec_ref(v_inst_151_);
v_toFunctor_154_ = lean_ctor_get(v_toApplicative_153_, 0);
lean_inc_ref(v_toFunctor_154_);
lean_dec_ref(v_toApplicative_153_);
v___f_155_ = ((lean_object*)(l_instMonadAttachReaderTOfMonad___redArg___closed__0));
v___f_156_ = lean_alloc_closure((void*)(l_instMonadAttachReaderTOfMonad___redArg___lam__1), 6, 3);
lean_closure_set(v___f_156_, 0, v_toFunctor_154_);
lean_closure_set(v___f_156_, 1, v_inst_152_);
lean_closure_set(v___f_156_, 2, v___f_155_);
return v___f_156_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachReaderTOfMonad(lean_object* v_m_157_, lean_object* v_00_u03c1_158_, lean_object* v_inst_159_, lean_object* v_inst_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_instMonadAttachReaderTOfMonad___redArg(v_inst_159_, v_inst_160_);
return v___x_161_;
}
}
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Reader(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Reader(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Except(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Reader(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Reader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Reader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Reader(builtin);
}
#ifdef __cplusplus
}
#endif
