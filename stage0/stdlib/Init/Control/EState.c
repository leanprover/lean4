// Lean compiler output
// Module: Init.Control.EState
// Imports: public import Init.Data.ToString.Basic public import Init.Control.State
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static const lean_string_object l_EStateM_instToStringResult___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ok: "};
static const lean_object* l_EStateM_instToStringResult___redArg___lam__0___closed__0 = (const lean_object*)&l_EStateM_instToStringResult___redArg___lam__0___closed__0_value;
static const lean_string_object l_EStateM_instToStringResult___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_EStateM_instToStringResult___redArg___lam__0___closed__1 = (const lean_object*)&l_EStateM_instToStringResult___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_EStateM_instReprResult___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "EStateM.Result.ok "};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__0 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_EStateM_instReprResult___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__0_value)}};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__1 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__1_value;
static const lean_string_object l_EStateM_instReprResult___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "EStateM.Result.error "};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__2 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_EStateM_instReprResult___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__2_value)}};
static const lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__3 = (const lean_object*)&l_EStateM_instReprResult___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_EStateM_instMonadAttach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonadAttach___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_EStateM_instMonadAttach___closed__0 = (const lean_object*)&l_EStateM_instMonadAttach___closed__0_value;
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_EStateM_instMonadFinally___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonadFinally___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_EStateM_instMonadFinally___closed__0 = (const lean_object*)&l_EStateM_instMonadFinally___closed__0_value;
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_fromStateM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg___lam__0(lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_x_5_){
_start:
{
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_dec_ref(v_inst_4_);
v_a_6_ = lean_ctor_get(v_x_5_, 0);
lean_inc(v_a_6_);
lean_dec_ref(v_x_5_);
v___x_7_ = ((lean_object*)(l_EStateM_instToStringResult___redArg___lam__0___closed__0));
v___x_8_ = lean_apply_1(v_inst_3_, v_a_6_);
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
lean_dec_ref(v___x_8_);
return v___x_9_;
}
else
{
lean_object* v_a_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec_ref(v_inst_3_);
v_a_10_ = lean_ctor_get(v_x_5_, 0);
lean_inc(v_a_10_);
lean_dec_ref(v_x_5_);
v___x_11_ = ((lean_object*)(l_EStateM_instToStringResult___redArg___lam__0___closed__1));
v___x_12_ = lean_apply_1(v_inst_4_, v_a_10_);
v___x_13_ = lean_string_append(v___x_11_, v___x_12_);
lean_dec_ref(v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = lean_alloc_closure((void*)(l_EStateM_instToStringResult___redArg___lam__0), 3, 2);
lean_closure_set(v___f_16_, 0, v_inst_15_);
lean_closure_set(v___f_16_, 1, v_inst_14_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object* v_00_u03b5_17_, lean_object* v_00_u03c3_18_, lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = lean_alloc_closure((void*)(l_EStateM_instToStringResult___redArg___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v_inst_21_);
lean_closure_set(v___f_22_, 1, v_inst_20_);
return v___f_22_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_44_; 
lean_dec_ref(v_inst_30_);
v_a_33_ = lean_ctor_get(v_x_31_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; 
v_unused_45_ = lean_ctor_get(v_x_31_, 1);
lean_dec(v_unused_45_);
v___x_35_ = v_x_31_;
v_isShared_36_ = v_isSharedCheck_44_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v_x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_44_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_37_ = ((lean_object*)(l_EStateM_instReprResult___redArg___lam__0___closed__1));
v___x_38_ = lean_unsigned_to_nat(1024u);
v___x_39_ = lean_apply_2(v_inst_29_, v_a_33_, v___x_38_);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 5);
lean_ctor_set(v___x_35_, 1, v___x_39_);
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_41_ = v___x_35_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_39_);
v___x_41_ = v_reuseFailAlloc_43_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; 
v___x_42_ = l_Repr_addAppParen(v___x_41_, v_x_32_);
return v___x_42_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_57_; 
lean_dec_ref(v_inst_29_);
v_a_46_ = lean_ctor_get(v_x_31_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v_x_31_, 1);
lean_dec(v_unused_58_);
v___x_48_ = v_x_31_;
v_isShared_49_ = v_isSharedCheck_57_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v_x_31_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_57_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_50_ = ((lean_object*)(l_EStateM_instReprResult___redArg___lam__0___closed__3));
v___x_51_ = lean_unsigned_to_nat(1024u);
v___x_52_ = lean_apply_2(v_inst_30_, v_a_46_, v___x_51_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 5);
lean_ctor_set(v___x_48_, 1, v___x_52_);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_54_ = v___x_48_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_56_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; 
v___x_55_ = l_Repr_addAppParen(v___x_54_, v_x_32_);
return v___x_55_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0___boxed(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_EStateM_instReprResult___redArg___lam__0(v_inst_59_, v_inst_60_, v_x_61_, v_x_62_);
lean_dec(v_x_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg(lean_object* v_inst_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___f_66_; 
v___f_66_ = lean_alloc_closure((void*)(l_EStateM_instReprResult___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_66_, 0, v_inst_65_);
lean_closure_set(v___f_66_, 1, v_inst_64_);
return v___f_66_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object* v_00_u03b5_67_, lean_object* v_00_u03c3_68_, lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___f_72_; 
v___f_72_ = lean_alloc_closure((void*)(l_EStateM_instReprResult___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_72_, 0, v_inst_71_);
lean_closure_set(v___f_72_, 1, v_inst_70_);
return v___f_72_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach___lam__0(lean_object* v_00_u03b1_73_, lean_object* v_x_74_, lean_object* v_s_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_apply_1(v_x_74_, v_s_75_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_a_78_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_77_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
else
{
lean_object* v_a_86_; lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_86_ = lean_ctor_get(v___x_76_, 0);
v_a_87_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_76_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_inc(v_a_86_);
lean_dec(v___x_76_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_86_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadAttach(lean_object* v_00_u03b5_96_, lean_object* v_00_u03c3_97_){
_start:
{
lean_object* v___f_98_; 
v___f_98_ = ((lean_object*)(l_EStateM_instMonadAttach___closed__0));
return v___f_98_;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg(lean_object* v_inst_99_, lean_object* v_x_u2081_100_, lean_object* v_x_u2082_101_, uint8_t v_useFirstEx_102_, lean_object* v_s_103_){
_start:
{
lean_object* v_save_104_; lean_object* v_restore_105_; lean_object* v_d_106_; lean_object* v___x_107_; 
v_save_104_ = lean_ctor_get(v_inst_99_, 0);
lean_inc(v_save_104_);
v_restore_105_ = lean_ctor_get(v_inst_99_, 1);
lean_inc(v_restore_105_);
lean_dec_ref(v_inst_99_);
lean_inc(v_s_103_);
v_d_106_ = lean_apply_1(v_save_104_, v_s_103_);
v___x_107_ = lean_apply_1(v_x_u2081_100_, v_s_103_);
if (lean_obj_tag(v___x_107_) == 1)
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
v_a_109_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_a_109_);
lean_dec_ref(v___x_107_);
v___x_110_ = lean_apply_2(v_restore_105_, v_a_109_, v_d_106_);
v___x_111_ = lean_apply_1(v_x_u2082_101_, v___x_110_);
if (lean_obj_tag(v___x_111_) == 1)
{
if (v_useFirstEx_102_ == 0)
{
lean_dec(v_a_108_);
return v___x_111_;
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_111_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v___x_111_, 0);
lean_dec(v_unused_120_);
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v_a_108_);
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_108_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_dec(v_a_108_);
return v___x_111_;
}
}
else
{
lean_dec(v_d_106_);
lean_dec(v_restore_105_);
lean_dec_ref(v_x_u2082_101_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg___boxed(lean_object* v_inst_121_, lean_object* v_x_u2081_122_, lean_object* v_x_u2082_123_, lean_object* v_useFirstEx_124_, lean_object* v_s_125_){
_start:
{
uint8_t v_useFirstEx_boxed_126_; lean_object* v_res_127_; 
v_useFirstEx_boxed_126_ = lean_unbox(v_useFirstEx_124_);
v_res_127_ = l_EStateM_orElse_x27___redArg(v_inst_121_, v_x_u2081_122_, v_x_u2082_123_, v_useFirstEx_boxed_126_, v_s_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object* v_00_u03b5_128_, lean_object* v_00_u03c3_129_, lean_object* v_00_u03b1_130_, lean_object* v_00_u03b4_131_, lean_object* v_inst_132_, lean_object* v_x_u2081_133_, lean_object* v_x_u2082_134_, uint8_t v_useFirstEx_135_, lean_object* v_s_136_){
_start:
{
lean_object* v_save_137_; lean_object* v_restore_138_; lean_object* v_d_139_; lean_object* v___x_140_; 
v_save_137_ = lean_ctor_get(v_inst_132_, 0);
lean_inc(v_save_137_);
v_restore_138_ = lean_ctor_get(v_inst_132_, 1);
lean_inc(v_restore_138_);
lean_dec_ref(v_inst_132_);
lean_inc(v_s_136_);
v_d_139_ = lean_apply_1(v_save_137_, v_s_136_);
v___x_140_ = lean_apply_1(v_x_u2081_133_, v_s_136_);
if (lean_obj_tag(v___x_140_) == 1)
{
lean_object* v_a_141_; lean_object* v_a_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
v_a_142_ = lean_ctor_get(v___x_140_, 1);
lean_inc(v_a_142_);
lean_dec_ref(v___x_140_);
v___x_143_ = lean_apply_2(v_restore_138_, v_a_142_, v_d_139_);
v___x_144_ = lean_apply_1(v_x_u2082_134_, v___x_143_);
if (lean_obj_tag(v___x_144_) == 1)
{
if (v_useFirstEx_135_ == 0)
{
lean_dec(v_a_141_);
return v___x_144_;
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_145_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; 
v_unused_153_ = lean_ctor_get(v___x_144_, 0);
lean_dec(v_unused_153_);
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_a_141_);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_141_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_dec(v_a_141_);
return v___x_144_;
}
}
else
{
lean_dec(v_d_139_);
lean_dec(v_restore_138_);
lean_dec_ref(v_x_u2082_134_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___boxed(lean_object* v_00_u03b5_154_, lean_object* v_00_u03c3_155_, lean_object* v_00_u03b1_156_, lean_object* v_00_u03b4_157_, lean_object* v_inst_158_, lean_object* v_x_u2081_159_, lean_object* v_x_u2082_160_, lean_object* v_useFirstEx_161_, lean_object* v_s_162_){
_start:
{
uint8_t v_useFirstEx_boxed_163_; lean_object* v_res_164_; 
v_useFirstEx_boxed_163_ = lean_unbox(v_useFirstEx_161_);
v_res_164_ = l_EStateM_orElse_x27(v_00_u03b5_154_, v_00_u03c3_155_, v_00_u03b1_156_, v_00_u03b4_157_, v_inst_158_, v_x_u2081_159_, v_x_u2082_160_, v_useFirstEx_boxed_163_, v_s_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___lam__0(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_x_167_, lean_object* v_h_168_, lean_object* v_s_169_){
_start:
{
lean_object* v_r_170_; 
v_r_170_ = lean_apply_1(v_x_167_, v_s_169_);
if (lean_obj_tag(v_r_170_) == 0)
{
lean_object* v_a_171_; lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_199_; 
v_a_171_ = lean_ctor_get(v_r_170_, 0);
v_a_172_ = lean_ctor_get(v_r_170_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_r_170_);
if (v_isSharedCheck_199_ == 0)
{
v___x_174_ = v_r_170_;
v_isShared_175_ = v_isSharedCheck_199_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_inc(v_a_171_);
lean_dec(v_r_170_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_199_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_inc(v_a_171_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_a_171_);
v___x_177_ = lean_apply_2(v_h_168_, v___x_176_, v_a_172_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_189_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_a_179_ = lean_ctor_get(v___x_177_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_189_ == 0)
{
v___x_181_ = v___x_177_;
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v_a_178_);
v___x_184_ = v___x_174_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_171_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_a_178_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_a_179_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_del_object(v___x_174_);
lean_dec(v_a_171_);
v_a_190_ = lean_ctor_get(v___x_177_, 0);
v_a_191_ = lean_ctor_get(v___x_177_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_177_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_inc(v_a_190_);
lean_dec(v___x_177_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_190_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v_a_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_a_200_ = lean_ctor_get(v_r_170_, 0);
lean_inc(v_a_200_);
v_a_201_ = lean_ctor_get(v_r_170_, 1);
lean_inc(v_a_201_);
lean_dec_ref(v_r_170_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_2(v_h_168_, v___x_202_, v_a_201_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_a_204_ = lean_ctor_get(v___x_203_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v___x_203_, 0);
lean_dec(v_unused_212_);
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 1);
lean_ctor_set(v___x_206_, 0, v_a_200_);
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_200_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_a_200_);
v_a_213_ = lean_ctor_get(v___x_203_, 0);
v_a_214_ = lean_ctor_get(v___x_203_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_203_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_inc(v_a_213_);
lean_dec(v___x_203_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_213_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally(lean_object* v_00_u03b5_223_, lean_object* v_00_u03c3_224_){
_start:
{
lean_object* v___f_225_; 
v___f_225_ = ((lean_object*)(l_EStateM_instMonadFinally___closed__0));
return v___f_225_;
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM___redArg(lean_object* v_x_226_, lean_object* v_s_227_){
_start:
{
lean_object* v___x_228_; lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v___x_228_ = lean_apply_1(v_x_226_, v_s_227_);
v_fst_229_ = lean_ctor_get(v___x_228_, 0);
v_snd_230_ = lean_ctor_get(v___x_228_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_228_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
lean_dec(v___x_228_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_snd_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object* v_00_u03b5_238_, lean_object* v_00_u03c3_239_, lean_object* v_00_u03b1_240_, lean_object* v_x_241_, lean_object* v_s_242_){
_start:
{
lean_object* v___x_243_; lean_object* v_fst_244_; lean_object* v_snd_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v___x_243_ = lean_apply_1(v_x_241_, v_s_242_);
v_fst_244_ = lean_ctor_get(v___x_243_, 0);
v_snd_245_ = lean_ctor_get(v___x_243_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_243_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_snd_245_);
lean_inc(v_fst_244_);
lean_dec(v___x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_fst_244_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_snd_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_EState(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_EState(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_EState(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_EState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_EState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_EState(builtin);
}
#ifdef __cplusplus
}
#endif
