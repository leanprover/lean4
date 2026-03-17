// Lean compiler output
// Module: Lean.Meta.Match.MatcherApp.Basic
// Imports: public import Lean.Meta.Match.MatcherInfo
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
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_getConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_____r_2_){
_start:
{
lean_object* v_toApplicative_3_; lean_object* v_toPure_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_toApplicative_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toApplicative_3_);
lean_dec_ref(v_inst_1_);
v_toPure_4_ = lean_ctor_get(v_toApplicative_3_, 1);
lean_inc(v_toPure_4_);
lean_dec_ref(v_toApplicative_3_);
v___x_5_ = lean_box(0);
v___x_6_ = lean_apply_2(v_toPure_4_, lean_box(0), v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2));
v___x_11_ = lean_unsigned_to_nat(53u);
v___x_12_ = lean_unsigned_to_nat(62u);
v___x_13_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1));
v___x_14_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0));
v___x_15_ = l_mkPanicMessageWithDecl(v___x_14_, v___x_13_, v___x_12_, v___x_11_, v___x_10_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(lean_object* v_toApplicative_16_, lean_object* v_inst_17_, lean_object* v_____x_18_){
_start:
{
if (lean_obj_tag(v_____x_18_) == 6)
{
lean_object* v_val_19_; lean_object* v_toPure_20_; lean_object* v_numFields_21_; lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec_ref(v_inst_17_);
v_val_19_ = lean_ctor_get(v_____x_18_, 0);
v_toPure_20_ = lean_ctor_get(v_toApplicative_16_, 1);
lean_inc(v_toPure_20_);
lean_dec_ref(v_toApplicative_16_);
v_numFields_21_ = lean_ctor_get(v_val_19_, 4);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = 0;
lean_inc(v_numFields_21_);
v___x_24_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_24_, 0, v_numFields_21_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
lean_ctor_set_uint8(v___x_24_, sizeof(void*)*2, v___x_23_);
v___x_25_ = lean_apply_2(v_toPure_20_, lean_box(0), v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec_ref(v_toApplicative_16_);
v___x_26_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_27_ = l_instInhabitedOfMonad___redArg(v_inst_17_, v___x_26_);
v___x_28_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3);
v___x_29_ = l_panic___redArg(v___x_27_, v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed(lean_object* v_toApplicative_30_, lean_object* v_inst_31_, lean_object* v_____x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(v_toApplicative_30_, v_inst_31_, v_____x_32_);
lean_dec_ref(v_____x_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2(lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_toBind_37_, lean_object* v___f_38_, lean_object* v_ctor_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l_Lean_getConstInfo___redArg(v_inst_34_, v_inst_35_, v_inst_36_, v_ctor_39_);
v___x_41_ = lean_apply_4(v_toBind_37_, lean_box(0), lean_box(0), v___x_40_, v___f_38_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_box(0);
v___x_43_ = lean_unsigned_to_nat(16u);
v___x_44_ = lean_mk_array(v___x_43_, v___x_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3(lean_object* v_toApplicative_45_, lean_object* v_params_46_, lean_object* v_discrs_47_, lean_object* v___x_48_, lean_object* v___y_49_, lean_object* v_discrInfos_50_, lean_object* v_us_51_, lean_object* v_alts_52_, lean_object* v___x_53_, lean_object* v_declName_54_, lean_object* v_motive_55_, lean_object* v_altInfos_56_){
_start:
{
lean_object* v_toPure_57_; lean_object* v_start_58_; lean_object* v_stop_59_; lean_object* v_start_60_; lean_object* v_stop_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_toPure_57_ = lean_ctor_get(v_toApplicative_45_, 1);
lean_inc(v_toPure_57_);
lean_dec_ref(v_toApplicative_45_);
v_start_58_ = lean_ctor_get(v_params_46_, 1);
v_stop_59_ = lean_ctor_get(v_params_46_, 2);
v_start_60_ = lean_ctor_get(v_discrs_47_, 1);
v_stop_61_ = lean_ctor_get(v_discrs_47_, 2);
v___x_62_ = lean_nat_sub(v_stop_59_, v_start_58_);
v___x_63_ = lean_nat_sub(v_stop_61_, v_start_60_);
v___x_64_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_48_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_66_, 0, v___x_62_);
lean_ctor_set(v___x_66_, 1, v___x_63_);
lean_ctor_set(v___x_66_, 2, v_altInfos_56_);
lean_ctor_set(v___x_66_, 3, v___y_49_);
lean_ctor_set(v___x_66_, 4, v_discrInfos_50_);
lean_ctor_set(v___x_66_, 5, v___x_65_);
v___x_67_ = lean_array_mk(v_us_51_);
v___x_68_ = l_Subarray_copy___redArg(v_params_46_);
v___x_69_ = l_Subarray_copy___redArg(v_discrs_47_);
v___x_70_ = l_Subarray_copy___redArg(v_alts_52_);
v___x_71_ = l_Subarray_copy___redArg(v___x_53_);
v___x_72_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_72_, 0, v___x_66_);
lean_ctor_set(v___x_72_, 1, v_declName_54_);
lean_ctor_set(v___x_72_, 2, v___x_67_);
lean_ctor_set(v___x_72_, 3, v___x_68_);
lean_ctor_set(v___x_72_, 4, v_motive_55_);
lean_ctor_set(v___x_72_, 5, v___x_69_);
lean_ctor_set(v___x_72_, 6, v___x_70_);
lean_ctor_set(v___x_72_, 7, v___x_71_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
v___x_74_ = lean_apply_2(v_toPure_57_, lean_box(0), v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_75_; lean_object* v_dummy_76_; 
v___x_75_ = lean_box(0);
v_dummy_76_ = l_Lean_Expr_sort___override(v___x_75_);
return v_dummy_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(lean_object* v_e_79_, lean_object* v_toApplicative_80_, lean_object* v_us_81_, lean_object* v_declName_82_, lean_object* v_inst_83_, lean_object* v___f_84_, lean_object* v_toBind_85_, lean_object* v_____x_86_){
_start:
{
if (lean_obj_tag(v_____x_86_) == 5)
{
lean_object* v_val_87_; lean_object* v_toConstantVal_88_; lean_object* v_numParams_89_; lean_object* v_numIndices_90_; lean_object* v_ctors_91_; lean_object* v_nargs_92_; lean_object* v_dummy_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_args_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_val_87_ = lean_ctor_get(v_____x_86_, 0);
lean_inc_ref(v_val_87_);
lean_dec_ref(v_____x_86_);
v_toConstantVal_88_ = lean_ctor_get(v_val_87_, 0);
lean_inc_ref(v_toConstantVal_88_);
v_numParams_89_ = lean_ctor_get(v_val_87_, 1);
lean_inc(v_numParams_89_);
v_numIndices_90_ = lean_ctor_get(v_val_87_, 2);
lean_inc(v_numIndices_90_);
v_ctors_91_ = lean_ctor_get(v_val_87_, 4);
lean_inc(v_ctors_91_);
v_nargs_92_ = l_Lean_Expr_getAppNumArgs(v_e_79_);
v_dummy_93_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0);
lean_inc(v_nargs_92_);
v___x_94_ = lean_mk_array(v_nargs_92_, v_dummy_93_);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_sub(v_nargs_92_, v___x_95_);
lean_dec(v_nargs_92_);
v_args_97_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_79_, v___x_94_, v___x_96_);
v___x_98_ = lean_nat_add(v_numParams_89_, v___x_95_);
v___x_99_ = lean_nat_add(v___x_98_, v_numIndices_90_);
v___x_100_ = lean_nat_add(v___x_99_, v___x_95_);
lean_dec(v___x_99_);
v___x_101_ = l_Lean_InductiveVal_numCtors(v_val_87_);
lean_dec_ref(v_val_87_);
v___x_102_ = lean_nat_add(v___x_100_, v___x_101_);
lean_dec(v___x_101_);
v___x_103_ = lean_array_get_size(v_args_97_);
v___x_104_ = lean_nat_dec_le(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v_toPure_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v___x_102_);
lean_dec(v___x_100_);
lean_dec(v___x_98_);
lean_dec_ref(v_args_97_);
lean_dec(v_ctors_91_);
lean_dec(v_numIndices_90_);
lean_dec(v_numParams_89_);
lean_dec_ref(v_toConstantVal_88_);
lean_dec(v_toBind_85_);
lean_dec(v___f_84_);
lean_dec_ref(v_inst_83_);
lean_dec(v_declName_82_);
lean_dec(v_us_81_);
v_toPure_105_ = lean_ctor_get(v_toApplicative_80_, 1);
lean_inc(v_toPure_105_);
lean_dec_ref(v_toApplicative_80_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_apply_2(v_toPure_105_, lean_box(0), v___x_106_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v_params_109_; lean_object* v___x_110_; lean_object* v_motive_111_; lean_object* v_discrs_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_discrInfos_115_; lean_object* v_alts_116_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v_lower_127_; lean_object* v_upper_128_; uint8_t v___x_135_; 
v___x_108_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_89_);
lean_inc_ref(v_args_97_);
v_params_109_ = l_Array_toSubarray___redArg(v_args_97_, v___x_108_, v_numParams_89_);
v___x_110_ = l_Lean_instInhabitedExpr;
v_motive_111_ = lean_array_get(v___x_110_, v_args_97_, v_numParams_89_);
lean_dec(v_numParams_89_);
lean_inc(v___x_100_);
lean_inc_ref(v_args_97_);
v_discrs_112_ = l_Array_toSubarray___redArg(v_args_97_, v___x_98_, v___x_100_);
v___x_113_ = lean_nat_add(v_numIndices_90_, v___x_95_);
lean_dec(v_numIndices_90_);
v___x_114_ = lean_box(0);
v_discrInfos_115_ = lean_mk_array(v___x_113_, v___x_114_);
lean_inc(v___x_102_);
lean_inc_ref(v_args_97_);
v_alts_116_ = l_Array_toSubarray___redArg(v_args_97_, v___x_100_, v___x_102_);
v___x_135_ = lean_nat_dec_le(v___x_102_, v___x_108_);
if (v___x_135_ == 0)
{
v_lower_127_ = v___x_102_;
v_upper_128_ = v___x_103_;
goto v___jp_126_;
}
else
{
lean_dec(v___x_102_);
v_lower_127_ = v___x_108_;
v_upper_128_ = v___x_103_;
goto v___jp_126_;
}
v___jp_117_:
{
lean_object* v___f_120_; lean_object* v___x_121_; size_t v_sz_122_; size_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3), 12, 11);
lean_closure_set(v___f_120_, 0, v_toApplicative_80_);
lean_closure_set(v___f_120_, 1, v_params_109_);
lean_closure_set(v___f_120_, 2, v_discrs_112_);
lean_closure_set(v___f_120_, 3, v___x_108_);
lean_closure_set(v___f_120_, 4, v___y_119_);
lean_closure_set(v___f_120_, 5, v_discrInfos_115_);
lean_closure_set(v___f_120_, 6, v_us_81_);
lean_closure_set(v___f_120_, 7, v_alts_116_);
lean_closure_set(v___f_120_, 8, v___y_118_);
lean_closure_set(v___f_120_, 9, v_declName_82_);
lean_closure_set(v___f_120_, 10, v_motive_111_);
v___x_121_ = lean_array_mk(v_ctors_91_);
v_sz_122_ = lean_array_size(v___x_121_);
v___x_123_ = ((size_t)0ULL);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_83_, v___f_84_, v_sz_122_, v___x_123_, v___x_121_);
v___x_125_ = lean_apply_4(v_toBind_85_, lean_box(0), lean_box(0), v___x_124_, v___f_120_);
return v___x_125_;
}
v___jp_126_:
{
lean_object* v_levelParams_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_levelParams_129_ = lean_ctor_get(v_toConstantVal_88_, 1);
lean_inc(v_levelParams_129_);
lean_dec_ref(v_toConstantVal_88_);
v___x_130_ = l_Array_toSubarray___redArg(v_args_97_, v_lower_127_, v_upper_128_);
v___x_131_ = l_List_lengthTR___redArg(v_levelParams_129_);
lean_dec(v_levelParams_129_);
v___x_132_ = l_List_lengthTR___redArg(v_us_81_);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
lean_dec(v___x_131_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1));
v___y_118_ = v___x_130_;
v___y_119_ = v___x_134_;
goto v___jp_117_;
}
else
{
v___y_118_ = v___x_130_;
v___y_119_ = v___x_114_;
goto v___jp_117_;
}
}
}
}
else
{
lean_object* v_toPure_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec_ref(v_____x_86_);
lean_dec(v_toBind_85_);
lean_dec(v___f_84_);
lean_dec_ref(v_inst_83_);
lean_dec(v_declName_82_);
lean_dec(v_us_81_);
lean_dec_ref(v_e_79_);
v_toPure_136_ = lean_ctor_get(v_toApplicative_80_, 1);
lean_inc(v_toPure_136_);
lean_dec_ref(v_toApplicative_80_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_2(v_toPure_136_, lean_box(0), v___x_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(lean_object* v___f_139_, uint8_t v_alsoCasesOn_140_, lean_object* v_declName_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_toBind_145_, lean_object* v___f_146_, lean_object* v_____do__lift_147_){
_start:
{
if (v_alsoCasesOn_140_ == 0)
{
lean_dec_ref(v_____do__lift_147_);
lean_dec(v___f_146_);
lean_dec(v_toBind_145_);
lean_dec_ref(v_inst_144_);
lean_dec_ref(v_inst_143_);
lean_dec_ref(v_inst_142_);
lean_dec(v_declName_141_);
goto v___jp_148_;
}
else
{
uint8_t v___x_151_; 
lean_inc(v_declName_141_);
v___x_151_ = l_Lean_isCasesOnRecursor(v_____do__lift_147_, v_declName_141_);
if (v___x_151_ == 0)
{
lean_dec(v___f_146_);
lean_dec(v_toBind_145_);
lean_dec_ref(v_inst_144_);
lean_dec_ref(v_inst_143_);
lean_dec_ref(v_inst_142_);
lean_dec(v_declName_141_);
goto v___jp_148_;
}
else
{
lean_object* v_indName_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v___f_139_);
v_indName_152_ = l_Lean_Name_getPrefix(v_declName_141_);
lean_dec(v_declName_141_);
v___x_153_ = l_Lean_getConstInfo___redArg(v_inst_142_, v_inst_143_, v_inst_144_, v_indName_152_);
v___x_154_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v___x_153_, v___f_146_);
return v___x_154_;
}
}
v___jp_148_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v___f_139_, v___x_149_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed(lean_object* v___f_155_, lean_object* v_alsoCasesOn_156_, lean_object* v_declName_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_toBind_161_, lean_object* v___f_162_, lean_object* v_____do__lift_163_){
_start:
{
uint8_t v_alsoCasesOn_boxed_164_; lean_object* v_res_165_; 
v_alsoCasesOn_boxed_164_ = lean_unbox(v_alsoCasesOn_156_);
v_res_165_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(v___f_155_, v_alsoCasesOn_boxed_164_, v_declName_157_, v_inst_158_, v_inst_159_, v_inst_160_, v_toBind_161_, v___f_162_, v_____do__lift_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6(lean_object* v_e_166_, lean_object* v_toApplicative_167_, lean_object* v_us_168_, lean_object* v_declName_169_, lean_object* v_inst_170_, lean_object* v_toBind_171_, lean_object* v___f_172_, lean_object* v_____do__lift_173_){
_start:
{
if (lean_obj_tag(v_____do__lift_173_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_214_; 
lean_dec(v___f_172_);
lean_dec(v_toBind_171_);
lean_dec_ref(v_inst_170_);
v_val_174_ = lean_ctor_get(v_____do__lift_173_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_____do__lift_173_);
if (v_isSharedCheck_214_ == 0)
{
v___x_176_ = v_____do__lift_173_;
v_isShared_177_ = v_isSharedCheck_214_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_dec(v_____do__lift_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_214_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_dummy_178_; lean_object* v_nargs_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_args_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_dummy_178_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0);
v_nargs_179_ = l_Lean_Expr_getAppNumArgs(v_e_166_);
lean_inc(v_nargs_179_);
v___x_180_ = lean_mk_array(v_nargs_179_, v_dummy_178_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_sub(v_nargs_179_, v___x_181_);
lean_dec(v_nargs_179_);
v_args_183_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_166_, v___x_180_, v___x_182_);
v___x_184_ = lean_array_get_size(v_args_183_);
v___x_185_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_174_);
v___x_186_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
lean_dec(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v_toPure_187_; lean_object* v_numParams_188_; lean_object* v_numDiscrs_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v_toPure_187_ = lean_ctor_get(v_toApplicative_167_, 1);
lean_inc(v_toPure_187_);
lean_dec_ref(v_toApplicative_167_);
v_numParams_188_ = lean_ctor_get(v_val_174_, 0);
v_numDiscrs_189_ = lean_ctor_get(v_val_174_, 1);
v___x_190_ = lean_array_mk(v_us_168_);
v___x_191_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_188_);
v___x_192_ = l_Array_extract___redArg(v_args_183_, v___x_191_, v_numParams_188_);
v___x_193_ = l_Lean_instInhabitedExpr;
v___x_194_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_174_);
v___x_195_ = lean_array_get(v___x_193_, v_args_183_, v___x_194_);
lean_dec(v___x_194_);
v___x_196_ = lean_nat_add(v_numParams_188_, v___x_181_);
v___x_197_ = lean_nat_add(v___x_196_, v_numDiscrs_189_);
lean_inc(v___x_197_);
lean_inc_ref(v_args_183_);
v___x_198_ = l_Array_toSubarray___redArg(v_args_183_, v___x_196_, v___x_197_);
v___x_199_ = l_Subarray_copy___redArg(v___x_198_);
v___x_200_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_174_);
v___x_201_ = lean_nat_add(v___x_197_, v___x_200_);
lean_dec(v___x_200_);
lean_inc(v___x_201_);
lean_inc_ref(v_args_183_);
v___x_202_ = l_Array_toSubarray___redArg(v_args_183_, v___x_197_, v___x_201_);
v___x_203_ = l_Subarray_copy___redArg(v___x_202_);
v___x_204_ = l_Array_toSubarray___redArg(v_args_183_, v___x_201_, v___x_184_);
v___x_205_ = l_Subarray_copy___redArg(v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_206_, 0, v_val_174_);
lean_ctor_set(v___x_206_, 1, v_declName_169_);
lean_ctor_set(v___x_206_, 2, v___x_190_);
lean_ctor_set(v___x_206_, 3, v___x_192_);
lean_ctor_set(v___x_206_, 4, v___x_195_);
lean_ctor_set(v___x_206_, 5, v___x_199_);
lean_ctor_set(v___x_206_, 6, v___x_203_);
lean_ctor_set(v___x_206_, 7, v___x_205_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_206_);
v___x_208_ = v___x_176_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_210_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = lean_apply_2(v_toPure_187_, lean_box(0), v___x_208_);
return v___x_209_;
}
}
else
{
lean_object* v_toPure_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v_args_183_);
lean_del_object(v___x_176_);
lean_dec(v_val_174_);
lean_dec(v_declName_169_);
lean_dec(v_us_168_);
v_toPure_211_ = lean_ctor_get(v_toApplicative_167_, 1);
lean_inc(v_toPure_211_);
lean_dec_ref(v_toApplicative_167_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_212_);
return v___x_213_;
}
}
}
else
{
lean_object* v_getEnv_215_; lean_object* v___x_216_; 
lean_dec(v_____do__lift_173_);
lean_dec(v_declName_169_);
lean_dec(v_us_168_);
lean_dec_ref(v_toApplicative_167_);
lean_dec_ref(v_e_166_);
v_getEnv_215_ = lean_ctor_get(v_inst_170_, 0);
lean_inc(v_getEnv_215_);
lean_dec_ref(v_inst_170_);
v___x_216_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v_getEnv_215_, v___f_172_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg(lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_e_220_, uint8_t v_alsoCasesOn_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = l_Lean_Expr_isApp(v_e_220_);
if (v___x_222_ == 0)
{
lean_object* v_toApplicative_223_; lean_object* v_toPure_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v_e_220_);
lean_dec_ref(v_inst_219_);
lean_dec_ref(v_inst_218_);
v_toApplicative_223_ = lean_ctor_get(v_inst_217_, 0);
lean_inc_ref(v_toApplicative_223_);
lean_dec_ref(v_inst_217_);
v_toPure_224_ = lean_ctor_get(v_toApplicative_223_, 1);
lean_inc(v_toPure_224_);
lean_dec_ref(v_toApplicative_223_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_apply_2(v_toPure_224_, lean_box(0), v___x_225_);
return v___x_226_;
}
else
{
lean_object* v___f_227_; lean_object* v___x_228_; 
lean_inc_ref(v_inst_217_);
v___f_227_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_227_, 0, v_inst_217_);
v___x_228_ = l_Lean_Expr_getAppFn(v_e_220_);
if (lean_obj_tag(v___x_228_) == 4)
{
lean_object* v_declName_229_; lean_object* v_us_230_; lean_object* v_toApplicative_231_; lean_object* v_toBind_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_declName_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_declName_229_);
v_us_230_ = lean_ctor_get(v___x_228_, 1);
lean_inc(v_us_230_);
lean_dec_ref(v___x_228_);
v_toApplicative_231_ = lean_ctor_get(v_inst_217_, 0);
v_toBind_232_ = lean_ctor_get(v_inst_217_, 1);
lean_inc(v_toBind_232_);
lean_inc_ref(v_inst_217_);
lean_inc_ref(v_toApplicative_231_);
v___f_233_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_233_, 0, v_toApplicative_231_);
lean_closure_set(v___f_233_, 1, v_inst_217_);
lean_inc(v_toBind_232_);
lean_inc_ref(v_inst_219_);
lean_inc_ref(v_inst_218_);
lean_inc_ref(v_inst_217_);
v___f_234_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2), 6, 5);
lean_closure_set(v___f_234_, 0, v_inst_217_);
lean_closure_set(v___f_234_, 1, v_inst_218_);
lean_closure_set(v___f_234_, 2, v_inst_219_);
lean_closure_set(v___f_234_, 3, v_toBind_232_);
lean_closure_set(v___f_234_, 4, v___f_233_);
lean_inc(v_toBind_232_);
lean_inc_ref(v_inst_217_);
lean_inc(v_declName_229_);
lean_inc(v_us_230_);
lean_inc_ref(v_toApplicative_231_);
lean_inc_ref(v_e_220_);
v___f_235_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4), 8, 7);
lean_closure_set(v___f_235_, 0, v_e_220_);
lean_closure_set(v___f_235_, 1, v_toApplicative_231_);
lean_closure_set(v___f_235_, 2, v_us_230_);
lean_closure_set(v___f_235_, 3, v_declName_229_);
lean_closure_set(v___f_235_, 4, v_inst_217_);
lean_closure_set(v___f_235_, 5, v___f_234_);
lean_closure_set(v___f_235_, 6, v_toBind_232_);
v___x_236_ = lean_box(v_alsoCasesOn_221_);
lean_inc(v_toBind_232_);
lean_inc_ref(v_inst_218_);
lean_inc_ref(v_inst_217_);
lean_inc(v_declName_229_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_237_, 0, v___f_227_);
lean_closure_set(v___f_237_, 1, v___x_236_);
lean_closure_set(v___f_237_, 2, v_declName_229_);
lean_closure_set(v___f_237_, 3, v_inst_217_);
lean_closure_set(v___f_237_, 4, v_inst_218_);
lean_closure_set(v___f_237_, 5, v_inst_219_);
lean_closure_set(v___f_237_, 6, v_toBind_232_);
lean_closure_set(v___f_237_, 7, v___f_235_);
lean_inc(v_toBind_232_);
lean_inc_ref(v_inst_218_);
lean_inc(v_declName_229_);
lean_inc_ref(v_toApplicative_231_);
v___f_238_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6), 8, 7);
lean_closure_set(v___f_238_, 0, v_e_220_);
lean_closure_set(v___f_238_, 1, v_toApplicative_231_);
lean_closure_set(v___f_238_, 2, v_us_230_);
lean_closure_set(v___f_238_, 3, v_declName_229_);
lean_closure_set(v___f_238_, 4, v_inst_218_);
lean_closure_set(v___f_238_, 5, v_toBind_232_);
lean_closure_set(v___f_238_, 6, v___f_237_);
v___x_239_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_217_, v_inst_218_, v_declName_229_);
v___x_240_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_239_, v___f_238_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec_ref(v___x_228_);
lean_dec_ref(v___f_227_);
lean_dec_ref(v_e_220_);
lean_dec_ref(v_inst_219_);
lean_dec_ref(v_inst_218_);
v___x_241_ = lean_box(0);
v___x_242_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(v_inst_217_, v___x_241_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___boxed(lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_e_246_, lean_object* v_alsoCasesOn_247_){
_start:
{
uint8_t v_alsoCasesOn_boxed_248_; lean_object* v_res_249_; 
v_alsoCasesOn_boxed_248_ = lean_unbox(v_alsoCasesOn_247_);
v_res_249_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(v_inst_243_, v_inst_244_, v_inst_245_, v_e_246_, v_alsoCasesOn_boxed_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object* v_m_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_e_254_, uint8_t v_alsoCasesOn_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(v_inst_251_, v_inst_252_, v_inst_253_, v_e_254_, v_alsoCasesOn_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___boxed(lean_object* v_m_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_e_261_, lean_object* v_alsoCasesOn_262_){
_start:
{
uint8_t v_alsoCasesOn_boxed_263_; lean_object* v_res_264_; 
v_alsoCasesOn_boxed_263_ = lean_unbox(v_alsoCasesOn_262_);
v_res_264_ = l_Lean_Meta_matchMatcherApp_x3f(v_m_257_, v_inst_258_, v_inst_259_, v_inst_260_, v_e_261_, v_alsoCasesOn_boxed_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object* v_matcherApp_265_){
_start:
{
lean_object* v_toMatcherInfo_266_; lean_object* v___x_267_; 
v_toMatcherInfo_266_ = lean_ctor_get(v_matcherApp_265_, 0);
lean_inc_ref(v_toMatcherInfo_266_);
lean_dec_ref(v_matcherApp_265_);
v___x_267_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_toMatcherInfo_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object* v_matcherApp_268_){
_start:
{
lean_object* v_matcherName_269_; lean_object* v_matcherLevels_270_; lean_object* v_params_271_; lean_object* v_motive_272_; lean_object* v_discrs_273_; lean_object* v_alts_274_; lean_object* v_remaining_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_result_278_; lean_object* v_result_279_; lean_object* v_result_280_; lean_object* v_result_281_; lean_object* v___x_282_; 
v_matcherName_269_ = lean_ctor_get(v_matcherApp_268_, 1);
lean_inc(v_matcherName_269_);
v_matcherLevels_270_ = lean_ctor_get(v_matcherApp_268_, 2);
lean_inc_ref(v_matcherLevels_270_);
v_params_271_ = lean_ctor_get(v_matcherApp_268_, 3);
lean_inc_ref(v_params_271_);
v_motive_272_ = lean_ctor_get(v_matcherApp_268_, 4);
lean_inc_ref(v_motive_272_);
v_discrs_273_ = lean_ctor_get(v_matcherApp_268_, 5);
lean_inc_ref(v_discrs_273_);
v_alts_274_ = lean_ctor_get(v_matcherApp_268_, 6);
lean_inc_ref(v_alts_274_);
v_remaining_275_ = lean_ctor_get(v_matcherApp_268_, 7);
lean_inc_ref(v_remaining_275_);
lean_dec_ref(v_matcherApp_268_);
v___x_276_ = lean_array_to_list(v_matcherLevels_270_);
v___x_277_ = l_Lean_mkConst(v_matcherName_269_, v___x_276_);
v_result_278_ = l_Lean_mkAppN(v___x_277_, v_params_271_);
lean_dec_ref(v_params_271_);
v_result_279_ = l_Lean_Expr_app___override(v_result_278_, v_motive_272_);
v_result_280_ = l_Lean_mkAppN(v_result_279_, v_discrs_273_);
lean_dec_ref(v_discrs_273_);
v_result_281_ = l_Lean_mkAppN(v_result_280_, v_alts_274_);
lean_dec_ref(v_alts_274_);
v___x_282_ = l_Lean_mkAppN(v_result_281_, v_remaining_275_);
lean_dec_ref(v_remaining_275_);
return v___x_282_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
