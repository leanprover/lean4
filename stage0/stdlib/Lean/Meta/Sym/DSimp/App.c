// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.App
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.Result import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.ProofInstInfo import Init.Omega
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Sym.DSimp.App"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.DSimp.App.0.Lean.Meta.Sym.DSimp.dsimpAppArgs.go"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*10);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
lean_inc_ref(v_f_1_);
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref_known(v___x_16_, 1);
lean_inc_ref(v_a_2_);
v___x_17_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_dec_ref_known(v___x_17_, 1);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_26_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_16_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_16_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Expr_app___override(v_f_1_, v_a_2_);
v___x_13_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_12_, v___y_11_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg___boxed(lean_object* v_f_34_, lean_object* v_a_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_f_34_, v_a_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(lean_object* v_f_44_, lean_object* v_a_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_f_44_, v_a_45_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___boxed(lean_object* v_f_57_, lean_object* v_a_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(v_f_57_, v_a_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec(v___y_60_);
lean_dec(v___y_59_);
return v_res_69_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(lean_box(0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(lean_object* v_msg_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_12019__overap_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0);
v___x_12019__overap_83_ = lean_panic_fn_borrowed(v___x_82_, v_msg_71_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
lean_inc(v___y_76_);
lean_inc_ref(v___y_75_);
lean_inc(v___y_74_);
lean_inc(v___y_73_);
lean_inc(v___y_72_);
v___x_84_ = lean_apply_10(v___x_12019__overap_83_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___boxed(lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
lean_dec(v___y_86_);
return v_res_96_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2));
v___x_101_ = lean_unsigned_to_nat(24u);
v___x_102_ = lean_unsigned_to_nat(51u);
v___x_103_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1));
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0));
v___x_105_ = l_mkPanicMessageWithDecl(v___x_104_, v___x_103_, v___x_102_, v___x_101_, v___x_100_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(lean_object* v_argsInfo_x3f_108_, lean_object* v_i_109_, lean_object* v_e_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v_a_124_; lean_object* v_a_128_; lean_object* v_a_132_; lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___y_138_; lean_object* v___y_139_; lean_object* v___y_140_; lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v___y_143_; lean_object* v___y_144_; lean_object* v___y_145_; lean_object* v___y_146_; uint8_t v___y_147_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v_i_109_, v___x_121_);
if (v___x_122_ == 0)
{
if (lean_obj_tag(v_e_110_) == 5)
{
lean_object* v_fn_158_; lean_object* v_arg_159_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; uint8_t v___y_171_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_fn_158_ = lean_ctor_get(v_e_110_, 0);
v_arg_159_ = lean_ctor_get(v_e_110_, 1);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_sub(v_i_109_, v___x_204_);
lean_inc_ref(v_fn_158_);
v___x_206_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v_argsInfo_x3f_108_, v___x_205_, v_fn_158_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_253_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_253_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_253_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_253_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_ar_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; 
if (lean_obj_tag(v_argsInfo_x3f_108_) == 0)
{
lean_dec(v___x_205_);
goto v___jp_242_;
}
else
{
lean_object* v_val_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_val_247_ = lean_ctor_get(v_argsInfo_x3f_108_, 0);
v___x_248_ = lean_array_get_size(v_val_247_);
v___x_249_ = lean_nat_dec_lt(v___x_205_, v___x_248_);
if (v___x_249_ == 0)
{
lean_dec(v___x_205_);
goto v___jp_242_;
}
else
{
lean_object* v___x_250_; uint8_t v_isProof_251_; 
v___x_250_ = lean_array_fget_borrowed(v_val_247_, v___x_205_);
lean_dec(v___x_205_);
v_isProof_251_ = lean_ctor_get_uint8(v___x_250_, 0);
if (v_isProof_251_ == 0)
{
uint8_t v_isInstance_252_; 
v_isInstance_252_ = lean_ctor_get_uint8(v___x_250_, 1);
if (v_isInstance_252_ == 0)
{
goto v___jp_242_;
}
else
{
goto v___jp_245_;
}
}
else
{
goto v___jp_245_;
}
}
}
v___jp_211_:
{
if (lean_obj_tag(v_a_207_) == 0)
{
lean_dec_ref_known(v_a_207_, 0);
if (lean_obj_tag(v_ar_212_) == 0)
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref_known(v_e_110_, 2);
v_isSharedCheck_231_ = !lean_is_exclusive(v_ar_212_);
if (v_isSharedCheck_231_ == 0)
{
v___x_223_ = v_ar_212_;
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_ar_212_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 0, 1);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
lean_ctor_set_uint8(v___x_226_, 0, v___x_122_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_226_);
v___x_228_ = v___x_209_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_e_x27_232_; uint8_t v___x_233_; 
lean_del_object(v___x_209_);
v_e_x27_232_ = lean_ctor_get(v_ar_212_, 0);
lean_inc_ref(v_e_x27_232_);
lean_dec_ref_known(v_ar_212_, 1);
v___x_233_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_158_, v_fn_158_);
if (v___x_233_ == 0)
{
v___y_183_ = v___y_220_;
v___y_184_ = v___y_217_;
v___y_185_ = v___y_216_;
v___y_186_ = v___y_215_;
v___y_187_ = v___y_221_;
v___y_188_ = v___y_218_;
v___y_189_ = v___y_214_;
v___y_190_ = v___y_213_;
v___y_191_ = v_e_x27_232_;
v___y_192_ = v___y_219_;
v___y_193_ = v___x_233_;
goto v___jp_182_;
}
else
{
uint8_t v___x_234_; 
v___x_234_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_159_, v_e_x27_232_);
v___y_183_ = v___y_220_;
v___y_184_ = v___y_217_;
v___y_185_ = v___y_216_;
v___y_186_ = v___y_215_;
v___y_187_ = v___y_221_;
v___y_188_ = v___y_218_;
v___y_189_ = v___y_214_;
v___y_190_ = v___y_213_;
v___y_191_ = v_e_x27_232_;
v___y_192_ = v___y_219_;
v___y_193_ = v___x_234_;
goto v___jp_182_;
}
}
}
else
{
lean_del_object(v___x_209_);
if (lean_obj_tag(v_ar_212_) == 0)
{
lean_object* v_e_x27_235_; uint8_t v___x_236_; 
lean_dec_ref_known(v_ar_212_, 0);
v_e_x27_235_ = lean_ctor_get(v_a_207_, 0);
lean_inc_ref(v_e_x27_235_);
lean_dec_ref_known(v_a_207_, 1);
v___x_236_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_158_, v_e_x27_235_);
if (v___x_236_ == 0)
{
v___y_161_ = v___y_220_;
v___y_162_ = v___y_217_;
v___y_163_ = v___y_216_;
v___y_164_ = v___y_215_;
v___y_165_ = v___y_221_;
v___y_166_ = v___y_218_;
v___y_167_ = v___y_214_;
v___y_168_ = v___y_213_;
v___y_169_ = v___y_219_;
v___y_170_ = v_e_x27_235_;
v___y_171_ = v___x_236_;
goto v___jp_160_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_159_, v_arg_159_);
v___y_161_ = v___y_220_;
v___y_162_ = v___y_217_;
v___y_163_ = v___y_216_;
v___y_164_ = v___y_215_;
v___y_165_ = v___y_221_;
v___y_166_ = v___y_218_;
v___y_167_ = v___y_214_;
v___y_168_ = v___y_213_;
v___y_169_ = v___y_219_;
v___y_170_ = v_e_x27_235_;
v___y_171_ = v___x_237_;
goto v___jp_160_;
}
}
else
{
lean_object* v_e_x27_238_; lean_object* v_e_x27_239_; uint8_t v___x_240_; 
v_e_x27_238_ = lean_ctor_get(v_a_207_, 0);
lean_inc_ref(v_e_x27_238_);
lean_dec_ref_known(v_a_207_, 1);
v_e_x27_239_ = lean_ctor_get(v_ar_212_, 0);
lean_inc_ref(v_e_x27_239_);
lean_dec_ref_known(v_ar_212_, 1);
v___x_240_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_158_, v_e_x27_238_);
if (v___x_240_ == 0)
{
v___y_136_ = v___y_220_;
v___y_137_ = v___y_217_;
v___y_138_ = v___y_216_;
v___y_139_ = v___y_215_;
v___y_140_ = v_e_x27_239_;
v___y_141_ = v___y_221_;
v___y_142_ = v___y_218_;
v___y_143_ = v___y_214_;
v___y_144_ = v___y_213_;
v___y_145_ = v___y_219_;
v___y_146_ = v_e_x27_238_;
v___y_147_ = v___x_240_;
goto v___jp_135_;
}
else
{
uint8_t v___x_241_; 
v___x_241_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_159_, v_e_x27_239_);
v___y_136_ = v___y_220_;
v___y_137_ = v___y_217_;
v___y_138_ = v___y_216_;
v___y_139_ = v___y_215_;
v___y_140_ = v_e_x27_239_;
v___y_141_ = v___y_221_;
v___y_142_ = v___y_218_;
v___y_143_ = v___y_214_;
v___y_144_ = v___y_213_;
v___y_145_ = v___y_219_;
v___y_146_ = v_e_x27_238_;
v___y_147_ = v___x_241_;
goto v___jp_135_;
}
}
}
}
v___jp_242_:
{
lean_object* v___x_243_; 
lean_inc(v_a_119_);
lean_inc_ref(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc(v_a_112_);
lean_inc(v_a_111_);
lean_inc_ref(v_arg_159_);
v___x_243_ = lean_sym_dsimp(v_arg_159_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_243_, 1);
v_ar_212_ = v_a_244_;
v___y_213_ = v_a_111_;
v___y_214_ = v_a_112_;
v___y_215_ = v_a_113_;
v___y_216_ = v_a_114_;
v___y_217_ = v_a_115_;
v___y_218_ = v_a_116_;
v___y_219_ = v_a_117_;
v___y_220_ = v_a_118_;
v___y_221_ = v_a_119_;
goto v___jp_211_;
}
else
{
lean_del_object(v___x_209_);
lean_dec(v_a_207_);
lean_dec_ref_known(v_e_110_, 2);
return v___x_243_;
}
}
v___jp_245_:
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_246_, 0, v___x_122_);
v_ar_212_ = v___x_246_;
v___y_213_ = v_a_111_;
v___y_214_ = v_a_112_;
v___y_215_ = v_a_113_;
v___y_216_ = v_a_114_;
v___y_217_ = v_a_115_;
v___y_218_ = v_a_116_;
v___y_219_ = v_a_117_;
v___y_220_ = v_a_118_;
v___y_221_ = v_a_119_;
goto v___jp_211_;
}
}
}
else
{
lean_dec(v___x_205_);
lean_dec_ref_known(v_e_110_, 2);
return v___x_206_;
}
v___jp_160_:
{
if (v___y_171_ == 0)
{
lean_object* v___x_172_; 
lean_inc_ref(v_arg_159_);
lean_dec_ref_known(v_e_110_, 2);
v___x_172_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v___y_170_, v_arg_159_, v___y_163_, v___y_162_, v___y_166_, v___y_169_, v___y_161_, v___y_165_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v_a_124_ = v_a_173_;
goto v___jp_123_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
v_a_174_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_172_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_dec_ref(v___y_170_);
v_a_124_ = v_e_110_;
goto v___jp_123_;
}
}
v___jp_182_:
{
if (v___y_193_ == 0)
{
lean_object* v___x_194_; 
lean_inc_ref(v_fn_158_);
lean_dec_ref_known(v_e_110_, 2);
v___x_194_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_fn_158_, v___y_191_, v___y_185_, v___y_184_, v___y_188_, v___y_192_, v___y_183_, v___y_187_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v_a_128_ = v_a_195_;
goto v___jp_127_;
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_194_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_dec_ref(v___y_191_);
v_a_128_ = v_e_110_;
goto v___jp_127_;
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref(v_e_110_);
v___x_254_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3, &l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3_once, _init_l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3);
v___x_255_ = l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(v___x_254_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
return v___x_255_;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v_e_110_);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4));
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_125_, 0, v_a_124_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_122_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_129_, 0, v_a_128_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_122_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
v___jp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_133_, 0, v_a_132_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v___x_122_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
v___jp_135_:
{
if (v___y_147_ == 0)
{
lean_object* v___x_148_; 
lean_dec_ref(v_e_110_);
v___x_148_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v___y_146_, v___y_140_, v___y_138_, v___y_137_, v___y_142_, v___y_145_, v___y_136_, v___y_141_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v_a_132_ = v_a_149_;
goto v___jp_131_;
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_148_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_148_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_dec_ref(v___y_146_);
lean_dec_ref(v___y_140_);
v_a_132_ = v_e_110_;
goto v___jp_131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___boxed(lean_object* v_argsInfo_x3f_258_, lean_object* v_i_259_, lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v_argsInfo_x3f_258_, v_i_259_, v_e_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec(v_a_262_);
lean_dec(v_a_261_);
lean_dec(v_i_259_);
lean_dec(v_argsInfo_x3f_258_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs(lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_numArgs_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_numArgs_283_ = l_Lean_Expr_getAppNumArgs(v_e_272_);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_dec_eq(v_numArgs_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v_f_286_; lean_object* v___x_287_; 
v_f_286_ = l_Lean_Expr_getAppFn(v_e_272_);
v___x_287_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(v_f_286_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
if (lean_obj_tag(v_a_288_) == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_box(0);
v___x_290_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v___x_289_, v_numArgs_283_, v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_numArgs_283_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_val_291_ = lean_ctor_get(v_a_288_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v_a_288_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_val_291_);
lean_dec(v_a_288_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_val_291_);
v___x_296_ = v_reuseFailAlloc_298_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v___x_296_, v_numArgs_283_, v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_numArgs_283_);
lean_dec_ref(v___x_296_);
return v___x_297_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_numArgs_283_);
lean_dec_ref(v_e_272_);
v_a_300_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_287_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_287_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_numArgs_283_);
lean_dec_ref(v_e_272_);
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4));
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs___boxed(lean_object* v_e_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(v_e_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec(v_a_312_);
lean_dec(v_a_311_);
return v_res_321_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ProofInstInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ProofInstInfo(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_App(builtin);
}
#ifdef __cplusplus
}
#endif
