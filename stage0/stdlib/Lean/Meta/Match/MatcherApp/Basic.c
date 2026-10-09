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
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_____r_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_8_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2));
v___x_9_ = lean_unsigned_to_nat(53u);
v___x_10_ = lean_unsigned_to_nat(62u);
v___x_11_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1));
v___x_12_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0));
v___x_13_ = l_mkPanicMessageWithDecl(v___x_12_, v___x_11_, v___x_10_, v___x_9_, v___x_8_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(lean_object* v_toPure_14_, lean_object* v___x_15_, lean_object* v_____x_16_){
_start:
{
if (lean_obj_tag(v_____x_16_) == 6)
{
lean_object* v_val_17_; lean_object* v_numFields_18_; lean_object* v___x_19_; uint8_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_val_17_ = lean_ctor_get(v_____x_16_, 0);
v_numFields_18_ = lean_ctor_get(v_val_17_, 4);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = 0;
lean_inc(v_numFields_18_);
v___x_21_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_21_, 0, v_numFields_18_);
lean_ctor_set(v___x_21_, 1, v___x_19_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*2, v___x_20_);
v___x_22_ = lean_apply_2(v_toPure_14_, lean_box(0), v___x_21_);
return v___x_22_;
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_toPure_14_);
v___x_23_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3);
v___x_24_ = l_panic___redArg(v___x_15_, v___x_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed(lean_object* v_toPure_25_, lean_object* v___x_26_, lean_object* v_____x_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(v_toPure_25_, v___x_26_, v_____x_27_);
lean_dec_ref(v_____x_27_);
lean_dec(v___x_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_toBind_32_, lean_object* v___f_33_, lean_object* v_ctor_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = l_Lean_getConstInfo___redArg(v_inst_29_, v_inst_30_, v_inst_31_, v_ctor_34_);
v___x_36_ = lean_apply_4(v_toBind_32_, lean_box(0), lean_box(0), v___x_35_, v___f_33_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_unsigned_to_nat(16u);
v___x_39_ = lean_mk_array(v___x_38_, v___x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3(lean_object* v_params_40_, lean_object* v_discrs_41_, lean_object* v___x_42_, lean_object* v___y_43_, lean_object* v_discrInfos_44_, lean_object* v_us_45_, lean_object* v_alts_46_, lean_object* v___x_47_, lean_object* v_declName_48_, lean_object* v_motive_49_, lean_object* v_toPure_50_, lean_object* v_altInfos_51_){
_start:
{
lean_object* v_start_52_; lean_object* v_stop_53_; lean_object* v_start_54_; lean_object* v_stop_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_start_52_ = lean_ctor_get(v_params_40_, 1);
v_stop_53_ = lean_ctor_get(v_params_40_, 2);
v_start_54_ = lean_ctor_get(v_discrs_41_, 1);
v_stop_55_ = lean_ctor_get(v_discrs_41_, 2);
v___x_56_ = lean_nat_sub(v_stop_53_, v_start_52_);
v___x_57_ = lean_nat_sub(v_stop_55_, v_start_54_);
v___x_58_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_42_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_60_, 0, v___x_56_);
lean_ctor_set(v___x_60_, 1, v___x_57_);
lean_ctor_set(v___x_60_, 2, v_altInfos_51_);
lean_ctor_set(v___x_60_, 3, v___y_43_);
lean_ctor_set(v___x_60_, 4, v_discrInfos_44_);
lean_ctor_set(v___x_60_, 5, v___x_59_);
v___x_61_ = lean_array_mk(v_us_45_);
v___x_62_ = l_Subarray_copy___redArg(v_params_40_);
v___x_63_ = l_Subarray_copy___redArg(v_discrs_41_);
v___x_64_ = l_Subarray_copy___redArg(v_alts_46_);
v___x_65_ = l_Subarray_copy___redArg(v___x_47_);
v___x_66_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_66_, 0, v___x_60_);
lean_ctor_set(v___x_66_, 1, v_declName_48_);
lean_ctor_set(v___x_66_, 2, v___x_61_);
lean_ctor_set(v___x_66_, 3, v___x_62_);
lean_ctor_set(v___x_66_, 4, v_motive_49_);
lean_ctor_set(v___x_66_, 5, v___x_63_);
lean_ctor_set(v___x_66_, 6, v___x_64_);
lean_ctor_set(v___x_66_, 7, v___x_65_);
v___x_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
v___x_68_ = lean_apply_2(v_toPure_50_, lean_box(0), v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v_dummy_70_; 
v___x_69_ = lean_box(0);
v_dummy_70_ = l_Lean_Expr_sort___override(v___x_69_);
return v_dummy_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(lean_object* v_e_73_, lean_object* v_toPure_74_, lean_object* v___x_75_, lean_object* v_us_76_, lean_object* v_declName_77_, lean_object* v_inst_78_, lean_object* v___f_79_, lean_object* v_toBind_80_, lean_object* v_____x_81_){
_start:
{
if (lean_obj_tag(v_____x_81_) == 5)
{
lean_object* v_val_82_; lean_object* v_toConstantVal_83_; lean_object* v_numParams_84_; lean_object* v_numIndices_85_; lean_object* v_ctors_86_; lean_object* v_nargs_87_; lean_object* v_dummy_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v_args_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_val_82_ = lean_ctor_get(v_____x_81_, 0);
lean_inc_ref(v_val_82_);
lean_dec_ref_known(v_____x_81_, 1);
v_toConstantVal_83_ = lean_ctor_get(v_val_82_, 0);
lean_inc_ref(v_toConstantVal_83_);
v_numParams_84_ = lean_ctor_get(v_val_82_, 1);
lean_inc(v_numParams_84_);
v_numIndices_85_ = lean_ctor_get(v_val_82_, 2);
lean_inc(v_numIndices_85_);
v_ctors_86_ = lean_ctor_get(v_val_82_, 4);
lean_inc(v_ctors_86_);
v_nargs_87_ = l_Lean_Expr_getAppNumArgs(v_e_73_);
v_dummy_88_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0);
lean_inc(v_nargs_87_);
v___x_89_ = lean_mk_array(v_nargs_87_, v_dummy_88_);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_sub(v_nargs_87_, v___x_90_);
lean_dec(v_nargs_87_);
v_args_92_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_73_, v___x_89_, v___x_91_);
v___x_93_ = lean_nat_add(v_numParams_84_, v___x_90_);
v___x_94_ = lean_nat_add(v___x_93_, v_numIndices_85_);
v___x_95_ = lean_nat_add(v___x_94_, v___x_90_);
lean_dec(v___x_94_);
v___x_96_ = l_Lean_InductiveVal_numCtors(v_val_82_);
lean_dec_ref(v_val_82_);
v___x_97_ = lean_nat_add(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
v___x_98_ = lean_array_get_size(v_args_92_);
v___x_99_ = lean_nat_dec_le(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v___x_97_);
lean_dec(v___x_95_);
lean_dec(v___x_93_);
lean_dec_ref(v_args_92_);
lean_dec(v_ctors_86_);
lean_dec(v_numIndices_85_);
lean_dec(v_numParams_84_);
lean_dec_ref(v_toConstantVal_83_);
lean_dec(v_toBind_80_);
lean_dec(v___f_79_);
lean_dec_ref(v_inst_78_);
lean_dec(v_declName_77_);
lean_dec(v_us_76_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v_params_103_; lean_object* v_motive_104_; lean_object* v_discrs_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_discrInfos_108_; lean_object* v_alts_109_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v_lower_120_; lean_object* v_upper_121_; uint8_t v___x_128_; 
v___x_102_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_84_);
lean_inc_ref_n(v_args_92_, 3);
v_params_103_ = l_Array_toSubarray___redArg(v_args_92_, v___x_102_, v_numParams_84_);
v_motive_104_ = lean_array_get(v___x_75_, v_args_92_, v_numParams_84_);
lean_dec(v_numParams_84_);
lean_inc(v___x_95_);
v_discrs_105_ = l_Array_toSubarray___redArg(v_args_92_, v___x_93_, v___x_95_);
v___x_106_ = lean_nat_add(v_numIndices_85_, v___x_90_);
lean_dec(v_numIndices_85_);
v___x_107_ = lean_box(0);
v_discrInfos_108_ = lean_mk_array(v___x_106_, v___x_107_);
lean_inc(v___x_97_);
v_alts_109_ = l_Array_toSubarray___redArg(v_args_92_, v___x_95_, v___x_97_);
v___x_128_ = lean_nat_dec_le(v___x_97_, v___x_102_);
if (v___x_128_ == 0)
{
v_lower_120_ = v___x_97_;
v_upper_121_ = v___x_98_;
goto v___jp_119_;
}
else
{
lean_dec(v___x_97_);
v_lower_120_ = v___x_102_;
v_upper_121_ = v___x_98_;
goto v___jp_119_;
}
v___jp_110_:
{
lean_object* v___f_113_; lean_object* v___x_114_; size_t v_sz_115_; size_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___f_113_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3), 12, 11);
lean_closure_set(v___f_113_, 0, v_params_103_);
lean_closure_set(v___f_113_, 1, v_discrs_105_);
lean_closure_set(v___f_113_, 2, v___x_102_);
lean_closure_set(v___f_113_, 3, v___y_112_);
lean_closure_set(v___f_113_, 4, v_discrInfos_108_);
lean_closure_set(v___f_113_, 5, v_us_76_);
lean_closure_set(v___f_113_, 6, v_alts_109_);
lean_closure_set(v___f_113_, 7, v___y_111_);
lean_closure_set(v___f_113_, 8, v_declName_77_);
lean_closure_set(v___f_113_, 9, v_motive_104_);
lean_closure_set(v___f_113_, 10, v_toPure_74_);
v___x_114_ = lean_array_mk(v_ctors_86_);
v_sz_115_ = lean_array_size(v___x_114_);
v___x_116_ = ((size_t)0ULL);
v___x_117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_78_, v___f_79_, v_sz_115_, v___x_116_, v___x_114_);
v___x_118_ = lean_apply_4(v_toBind_80_, lean_box(0), lean_box(0), v___x_117_, v___f_113_);
return v___x_118_;
}
v___jp_119_:
{
lean_object* v_levelParams_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_levelParams_122_ = lean_ctor_get(v_toConstantVal_83_, 1);
lean_inc(v_levelParams_122_);
lean_dec_ref(v_toConstantVal_83_);
v___x_123_ = l_Array_toSubarray___redArg(v_args_92_, v_lower_120_, v_upper_121_);
v___x_124_ = l_List_lengthTR___redArg(v_levelParams_122_);
lean_dec(v_levelParams_122_);
v___x_125_ = l_List_lengthTR___redArg(v_us_76_);
v___x_126_ = lean_nat_dec_eq(v___x_124_, v___x_125_);
lean_dec(v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1));
v___y_111_ = v___x_123_;
v___y_112_ = v___x_127_;
goto v___jp_110_;
}
else
{
v___y_111_ = v___x_123_;
v___y_112_ = v___x_107_;
goto v___jp_110_;
}
}
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec_ref(v_____x_81_);
lean_dec(v_toBind_80_);
lean_dec(v___f_79_);
lean_dec_ref(v_inst_78_);
lean_dec(v_declName_77_);
lean_dec(v_us_76_);
lean_dec_ref(v_e_73_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___boxed(lean_object* v_e_131_, lean_object* v_toPure_132_, lean_object* v___x_133_, lean_object* v_us_134_, lean_object* v_declName_135_, lean_object* v_inst_136_, lean_object* v___f_137_, lean_object* v_toBind_138_, lean_object* v_____x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(v_e_131_, v_toPure_132_, v___x_133_, v_us_134_, v_declName_135_, v_inst_136_, v___f_137_, v_toBind_138_, v_____x_139_);
lean_dec_ref(v___x_133_);
return v_res_140_;
}
}
lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(lean_object* v___f_141_, uint8_t v_alsoCasesOn_142_, lean_object* v_declName_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_toBind_147_, lean_object* v___f_148_, lean_object* v_____do__lift_149_){
_start:
{
if (v_alsoCasesOn_142_ == 0)
{
lean_dec_ref(v_____do__lift_149_);
lean_dec(v___f_148_);
lean_dec(v_toBind_147_);
lean_dec_ref(v_inst_146_);
lean_dec_ref(v_inst_145_);
lean_dec_ref(v_inst_144_);
lean_dec(v_declName_143_);
goto v___jp_150_;
}
else
{
uint8_t v___x_153_; 
lean_inc(v_declName_143_);
v___x_153_ = l_Lean_isCasesOnRecursor(v_____do__lift_149_, v_declName_143_);
if (v___x_153_ == 0)
{
lean_dec(v___f_148_);
lean_dec(v_toBind_147_);
lean_dec_ref(v_inst_146_);
lean_dec_ref(v_inst_145_);
lean_dec_ref(v_inst_144_);
lean_dec(v_declName_143_);
goto v___jp_150_;
}
else
{
lean_object* v_indName_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v___f_141_);
v_indName_154_ = l_Lean_Name_getPrefix(v_declName_143_);
lean_dec(v_declName_143_);
v___x_155_ = l_Lean_getConstInfo___redArg(v_inst_144_, v_inst_145_, v_inst_146_, v_indName_154_);
v___x_156_ = lean_apply_4(v_toBind_147_, lean_box(0), lean_box(0), v___x_155_, v___f_148_);
return v___x_156_;
}
}
v___jp_150_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_1(v___f_141_, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_141_ = stack[0].m_obj;
uint8_t v_alsoCasesOn_142_ = stack[1].m_num;
lean_object* v_declName_143_ = stack[2].m_obj;
lean_object* v_inst_144_ = stack[3].m_obj;
lean_object* v_inst_145_ = stack[4].m_obj;
lean_object* v_inst_146_ = stack[5].m_obj;
lean_object* v_toBind_147_ = stack[6].m_obj;
lean_object* v___f_148_ = stack[7].m_obj;
lean_object* v_____do__lift_149_ = stack[8].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(v___f_141_, v_alsoCasesOn_142_, v_declName_143_, v_inst_144_, v_inst_145_, v_inst_146_, v_toBind_147_, v___f_148_, v_____do__lift_149_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed(lean_object* v___f_158_, lean_object* v_alsoCasesOn_159_, lean_object* v_declName_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_toBind_164_, lean_object* v___f_165_, lean_object* v_____do__lift_166_){
_start:
{
uint8_t v_alsoCasesOn_boxed_167_; lean_object* v_res_168_; 
v_alsoCasesOn_boxed_167_ = lean_unbox(v_alsoCasesOn_159_);
v_res_168_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(v___f_158_, v_alsoCasesOn_boxed_167_, v_declName_160_, v_inst_161_, v_inst_162_, v_inst_163_, v_toBind_164_, v___f_165_, v_____do__lift_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6(lean_object* v_e_169_, lean_object* v_us_170_, lean_object* v___x_171_, lean_object* v_declName_172_, lean_object* v_toPure_173_, lean_object* v_inst_174_, lean_object* v_toBind_175_, lean_object* v___f_176_, lean_object* v_____do__lift_177_){
_start:
{
if (lean_obj_tag(v_____do__lift_177_) == 1)
{
lean_object* v_val_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_215_; 
lean_dec(v___f_176_);
lean_dec(v_toBind_175_);
lean_dec_ref(v_inst_174_);
v_val_178_ = lean_ctor_get(v_____do__lift_177_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_____do__lift_177_);
if (v_isSharedCheck_215_ == 0)
{
v___x_180_ = v_____do__lift_177_;
v_isShared_181_ = v_isSharedCheck_215_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_val_178_);
lean_dec(v_____do__lift_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_215_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_dummy_182_; lean_object* v_nargs_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_args_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_dummy_182_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0);
v_nargs_183_ = l_Lean_Expr_getAppNumArgs(v_e_169_);
lean_inc(v_nargs_183_);
v___x_184_ = lean_mk_array(v_nargs_183_, v_dummy_182_);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_sub(v_nargs_183_, v___x_185_);
lean_dec(v_nargs_183_);
v_args_187_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_169_, v___x_184_, v___x_186_);
v___x_188_ = lean_array_get_size(v_args_187_);
v___x_189_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_178_);
v___x_190_ = lean_nat_dec_lt(v___x_188_, v___x_189_);
lean_dec(v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v_numParams_191_; lean_object* v_numDiscrs_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v_numParams_191_ = lean_ctor_get(v_val_178_, 0);
v_numDiscrs_192_ = lean_ctor_get(v_val_178_, 1);
v___x_193_ = lean_array_mk(v_us_170_);
v___x_194_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_191_);
v___x_195_ = l_Array_extract___redArg(v_args_187_, v___x_194_, v_numParams_191_);
v___x_196_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_178_);
v___x_197_ = lean_array_get(v___x_171_, v_args_187_, v___x_196_);
lean_dec(v___x_196_);
v___x_198_ = lean_nat_add(v_numParams_191_, v___x_185_);
v___x_199_ = lean_nat_add(v___x_198_, v_numDiscrs_192_);
lean_inc(v___x_199_);
lean_inc_ref_n(v_args_187_, 2);
v___x_200_ = l_Array_toSubarray___redArg(v_args_187_, v___x_198_, v___x_199_);
v___x_201_ = l_Subarray_copy___redArg(v___x_200_);
v___x_202_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_178_);
v___x_203_ = lean_nat_add(v___x_199_, v___x_202_);
lean_dec(v___x_202_);
lean_inc(v___x_203_);
v___x_204_ = l_Array_toSubarray___redArg(v_args_187_, v___x_199_, v___x_203_);
v___x_205_ = l_Subarray_copy___redArg(v___x_204_);
v___x_206_ = l_Array_toSubarray___redArg(v_args_187_, v___x_203_, v___x_188_);
v___x_207_ = l_Subarray_copy___redArg(v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_208_, 0, v_val_178_);
lean_ctor_set(v___x_208_, 1, v_declName_172_);
lean_ctor_set(v___x_208_, 2, v___x_193_);
lean_ctor_set(v___x_208_, 3, v___x_195_);
lean_ctor_set(v___x_208_, 4, v___x_197_);
lean_ctor_set(v___x_208_, 5, v___x_201_);
lean_ctor_set(v___x_208_, 6, v___x_205_);
lean_ctor_set(v___x_208_, 7, v___x_207_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_208_);
v___x_210_ = v___x_180_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_212_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; 
v___x_211_ = lean_apply_2(v_toPure_173_, lean_box(0), v___x_210_);
return v___x_211_;
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec_ref(v_args_187_);
lean_del_object(v___x_180_);
lean_dec(v_val_178_);
lean_dec(v_declName_172_);
lean_dec(v_us_170_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_2(v_toPure_173_, lean_box(0), v___x_213_);
return v___x_214_;
}
}
}
else
{
lean_object* v_getEnv_216_; lean_object* v___x_217_; 
lean_dec(v_____do__lift_177_);
lean_dec(v_toPure_173_);
lean_dec(v_declName_172_);
lean_dec(v_us_170_);
lean_dec_ref(v_e_169_);
v_getEnv_216_ = lean_ctor_get(v_inst_174_, 0);
lean_inc(v_getEnv_216_);
lean_dec_ref(v_inst_174_);
v___x_217_ = lean_apply_4(v_toBind_175_, lean_box(0), lean_box(0), v_getEnv_216_, v___f_176_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6___boxed(lean_object* v_e_218_, lean_object* v_us_219_, lean_object* v___x_220_, lean_object* v_declName_221_, lean_object* v_toPure_222_, lean_object* v_inst_223_, lean_object* v_toBind_224_, lean_object* v___f_225_, lean_object* v_____do__lift_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6(v_e_218_, v_us_219_, v___x_220_, v_declName_221_, v_toPure_222_, v_inst_223_, v_toBind_224_, v___f_225_, v_____do__lift_226_);
lean_dec_ref(v___x_220_);
return v_res_227_;
}
}
lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_e_231_, uint8_t v_alsoCasesOn_232_){
_start:
{
lean_object* v_toApplicative_233_; lean_object* v_toBind_234_; lean_object* v_toPure_235_; uint8_t v___x_236_; 
v_toApplicative_233_ = lean_ctor_get(v_inst_228_, 0);
v_toBind_234_ = lean_ctor_get(v_inst_228_, 1);
lean_inc(v_toBind_234_);
v_toPure_235_ = lean_ctor_get(v_toApplicative_233_, 1);
v___x_236_ = l_Lean_Expr_isApp(v_e_231_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_inc(v_toPure_235_);
lean_dec(v_toBind_234_);
lean_dec_ref(v_e_231_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_inst_229_);
lean_dec_ref(v_inst_228_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_apply_2(v_toPure_235_, lean_box(0), v___x_237_);
return v___x_238_;
}
else
{
lean_object* v___f_239_; lean_object* v___x_240_; 
lean_inc(v_toPure_235_);
v___f_239_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_239_, 0, v_toPure_235_);
v___x_240_ = l_Lean_Expr_getAppFn(v_e_231_);
if (lean_obj_tag(v___x_240_) == 4)
{
lean_object* v_declName_241_; lean_object* v_us_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_declName_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_n(v_declName_241_, 4);
v_us_242_ = lean_ctor_get(v___x_240_, 1);
lean_inc_n(v_us_242_, 2);
lean_dec_ref_known(v___x_240_, 2);
v___x_243_ = l_Lean_instInhabitedExpr;
v___x_244_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_inc_ref_n(v_inst_228_, 4);
v___x_245_ = l_instInhabitedOfMonad___redArg(v_inst_228_, v___x_244_);
lean_inc_n(v_toPure_235_, 3);
v___f_246_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_246_, 0, v_toPure_235_);
lean_closure_set(v___f_246_, 1, v___x_245_);
lean_inc_n(v_toBind_234_, 4);
lean_inc_ref(v_inst_230_);
lean_inc_ref_n(v_inst_229_, 3);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2), 6, 5);
lean_closure_set(v___f_247_, 0, v_inst_228_);
lean_closure_set(v___f_247_, 1, v_inst_229_);
lean_closure_set(v___f_247_, 2, v_inst_230_);
lean_closure_set(v___f_247_, 3, v_toBind_234_);
lean_closure_set(v___f_247_, 4, v___f_246_);
lean_inc_ref(v_e_231_);
v___f_248_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_248_, 0, v_e_231_);
lean_closure_set(v___f_248_, 1, v_toPure_235_);
lean_closure_set(v___f_248_, 2, v___x_243_);
lean_closure_set(v___f_248_, 3, v_us_242_);
lean_closure_set(v___f_248_, 4, v_declName_241_);
lean_closure_set(v___f_248_, 5, v_inst_228_);
lean_closure_set(v___f_248_, 6, v___f_247_);
lean_closure_set(v___f_248_, 7, v_toBind_234_);
v___x_249_ = lean_box(v_alsoCasesOn_232_);
v___f_250_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_250_, 0, v___f_239_);
lean_closure_set(v___f_250_, 1, v___x_249_);
lean_closure_set(v___f_250_, 2, v_declName_241_);
lean_closure_set(v___f_250_, 3, v_inst_228_);
lean_closure_set(v___f_250_, 4, v_inst_229_);
lean_closure_set(v___f_250_, 5, v_inst_230_);
lean_closure_set(v___f_250_, 6, v_toBind_234_);
lean_closure_set(v___f_250_, 7, v___f_248_);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_251_, 0, v_e_231_);
lean_closure_set(v___f_251_, 1, v_us_242_);
lean_closure_set(v___f_251_, 2, v___x_243_);
lean_closure_set(v___f_251_, 3, v_declName_241_);
lean_closure_set(v___f_251_, 4, v_toPure_235_);
lean_closure_set(v___f_251_, 5, v_inst_229_);
lean_closure_set(v___f_251_, 6, v_toBind_234_);
lean_closure_set(v___f_251_, 7, v___f_250_);
v___x_252_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_228_, v_inst_229_, v_declName_241_);
v___x_253_ = lean_apply_4(v_toBind_234_, lean_box(0), lean_box(0), v___x_252_, v___f_251_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_inc(v_toPure_235_);
lean_dec_ref(v___x_240_);
lean_dec_ref(v___f_239_);
lean_dec(v_toBind_234_);
lean_dec_ref(v_e_231_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_inst_229_);
lean_dec_ref(v_inst_228_);
v___x_254_ = lean_box(0);
v___x_255_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(v_toPure_235_, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchMatcherApp_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_228_ = stack[0].m_obj;
lean_object* v_inst_229_ = stack[1].m_obj;
lean_object* v_inst_230_ = stack[2].m_obj;
lean_object* v_e_231_ = stack[3].m_obj;
uint8_t v_alsoCasesOn_232_ = stack[4].m_num;
lean_object* v_res_256_;
v_res_256_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(v_inst_228_, v_inst_229_, v_inst_230_, v_e_231_, v_alsoCasesOn_232_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___boxed(lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_e_260_, lean_object* v_alsoCasesOn_261_){
_start:
{
uint8_t v_alsoCasesOn_boxed_262_; lean_object* v_res_263_; 
v_alsoCasesOn_boxed_262_ = lean_unbox(v_alsoCasesOn_261_);
v_res_263_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(v_inst_257_, v_inst_258_, v_inst_259_, v_e_260_, v_alsoCasesOn_boxed_262_);
return v_res_263_;
}
}
lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object* v_m_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_e_268_, uint8_t v_alsoCasesOn_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(v_inst_265_, v_inst_266_, v_inst_267_, v_e_268_, v_alsoCasesOn_269_);
return v___x_270_;
}
}
LEAN_EXPORT void l_Lean_Meta_matchMatcherApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_265_ = stack[1].m_obj;
lean_object* v_inst_266_ = stack[2].m_obj;
lean_object* v_inst_267_ = stack[3].m_obj;
lean_object* v_e_268_ = stack[4].m_obj;
uint8_t v_alsoCasesOn_269_ = stack[5].m_num;
lean_object* v_res_271_;
v_res_271_ = l_Lean_Meta_matchMatcherApp_x3f(lean_box(0), v_inst_265_, v_inst_266_, v_inst_267_, v_e_268_, v_alsoCasesOn_269_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___boxed(lean_object* v_m_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_e_276_, lean_object* v_alsoCasesOn_277_){
_start:
{
uint8_t v_alsoCasesOn_boxed_278_; lean_object* v_res_279_; 
v_alsoCasesOn_boxed_278_ = lean_unbox(v_alsoCasesOn_277_);
v_res_279_ = l_Lean_Meta_matchMatcherApp_x3f(v_m_272_, v_inst_273_, v_inst_274_, v_inst_275_, v_e_276_, v_alsoCasesOn_boxed_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object* v_matcherApp_280_){
_start:
{
lean_object* v_toMatcherInfo_281_; lean_object* v___x_282_; 
v_toMatcherInfo_281_ = lean_ctor_get(v_matcherApp_280_, 0);
lean_inc_ref(v_toMatcherInfo_281_);
lean_dec_ref(v_matcherApp_280_);
v___x_282_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_toMatcherInfo_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object* v_matcherApp_283_){
_start:
{
lean_object* v_matcherName_284_; lean_object* v_matcherLevels_285_; lean_object* v_params_286_; lean_object* v_motive_287_; lean_object* v_discrs_288_; lean_object* v_alts_289_; lean_object* v_remaining_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_result_293_; lean_object* v_result_294_; lean_object* v_result_295_; lean_object* v_result_296_; lean_object* v___x_297_; 
v_matcherName_284_ = lean_ctor_get(v_matcherApp_283_, 1);
lean_inc(v_matcherName_284_);
v_matcherLevels_285_ = lean_ctor_get(v_matcherApp_283_, 2);
lean_inc_ref(v_matcherLevels_285_);
v_params_286_ = lean_ctor_get(v_matcherApp_283_, 3);
lean_inc_ref(v_params_286_);
v_motive_287_ = lean_ctor_get(v_matcherApp_283_, 4);
lean_inc_ref(v_motive_287_);
v_discrs_288_ = lean_ctor_get(v_matcherApp_283_, 5);
lean_inc_ref(v_discrs_288_);
v_alts_289_ = lean_ctor_get(v_matcherApp_283_, 6);
lean_inc_ref(v_alts_289_);
v_remaining_290_ = lean_ctor_get(v_matcherApp_283_, 7);
lean_inc_ref(v_remaining_290_);
lean_dec_ref(v_matcherApp_283_);
v___x_291_ = lean_array_to_list(v_matcherLevels_285_);
v___x_292_ = l_Lean_mkConst(v_matcherName_284_, v___x_291_);
v_result_293_ = l_Lean_mkAppN(v___x_292_, v_params_286_);
lean_dec_ref(v_params_286_);
v_result_294_ = l_Lean_Expr_app___override(v_result_293_, v_motive_287_);
v_result_295_ = l_Lean_mkAppN(v_result_294_, v_discrs_288_);
lean_dec_ref(v_discrs_288_);
v_result_296_ = l_Lean_mkAppN(v_result_295_, v_alts_289_);
lean_dec_ref(v_alts_289_);
v___x_297_ = l_Lean_mkAppN(v_result_296_, v_remaining_290_);
lean_dec_ref(v_remaining_290_);
return v___x_297_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
