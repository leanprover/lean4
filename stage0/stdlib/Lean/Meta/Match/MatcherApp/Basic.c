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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__1;
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
lean_dec(v___x_27_);
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
lean_object* v_cellCount_42_; lean_object* v___x_43_; 
v_cellCount_42_ = lean_unsigned_to_nat(16u);
v___x_43_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v_cellCount_44_; lean_object* v___x_45_; 
v_cellCount_44_ = lean_unsigned_to_nat(16u);
v___x_45_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3(lean_object* v_toApplicative_46_, lean_object* v_params_47_, lean_object* v_discrs_48_, lean_object* v___x_49_, lean_object* v___y_50_, lean_object* v_discrInfos_51_, lean_object* v_us_52_, lean_object* v_alts_53_, lean_object* v___x_54_, lean_object* v_declName_55_, lean_object* v_motive_56_, lean_object* v_altInfos_57_){
_start:
{
lean_object* v_toPure_58_; lean_object* v_start_59_; lean_object* v_stop_60_; lean_object* v_start_61_; lean_object* v_stop_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_toPure_58_ = lean_ctor_get(v_toApplicative_46_, 1);
lean_inc(v_toPure_58_);
lean_dec_ref(v_toApplicative_46_);
v_start_59_ = lean_ctor_get(v_params_47_, 1);
v_stop_60_ = lean_ctor_get(v_params_47_, 2);
v_start_61_ = lean_ctor_get(v_discrs_48_, 1);
v_stop_62_ = lean_ctor_get(v_discrs_48_, 2);
v___x_63_ = lean_nat_sub(v_stop_60_, v_start_59_);
v___x_64_ = lean_nat_sub(v_stop_62_, v_start_61_);
v___x_65_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0);
v___x_66_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__1);
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_49_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_68_, 0, v___x_63_);
lean_ctor_set(v___x_68_, 1, v___x_64_);
lean_ctor_set(v___x_68_, 2, v_altInfos_57_);
lean_ctor_set(v___x_68_, 3, v___y_50_);
lean_ctor_set(v___x_68_, 4, v_discrInfos_51_);
lean_ctor_set(v___x_68_, 5, v___x_67_);
v___x_69_ = lean_array_mk(v_us_52_);
v___x_70_ = l_Subarray_copy___redArg(v_params_47_);
v___x_71_ = l_Subarray_copy___redArg(v_discrs_48_);
v___x_72_ = l_Subarray_copy___redArg(v_alts_53_);
v___x_73_ = l_Subarray_copy___redArg(v___x_54_);
v___x_74_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_74_, 0, v___x_68_);
lean_ctor_set(v___x_74_, 1, v_declName_55_);
lean_ctor_set(v___x_74_, 2, v___x_69_);
lean_ctor_set(v___x_74_, 3, v___x_70_);
lean_ctor_set(v___x_74_, 4, v_motive_56_);
lean_ctor_set(v___x_74_, 5, v___x_71_);
lean_ctor_set(v___x_74_, 6, v___x_72_);
lean_ctor_set(v___x_74_, 7, v___x_73_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___x_76_ = lean_apply_2(v_toPure_58_, lean_box(0), v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_77_; lean_object* v_dummy_78_; 
v___x_77_ = lean_box(0);
v_dummy_78_ = l_Lean_Expr_sort___override(v___x_77_);
return v_dummy_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(lean_object* v_e_81_, lean_object* v_toApplicative_82_, lean_object* v_us_83_, lean_object* v_declName_84_, lean_object* v_inst_85_, lean_object* v___f_86_, lean_object* v_toBind_87_, lean_object* v_____x_88_){
_start:
{
if (lean_obj_tag(v_____x_88_) == 5)
{
lean_object* v_val_89_; lean_object* v_toConstantVal_90_; lean_object* v_numParams_91_; lean_object* v_numIndices_92_; lean_object* v_ctors_93_; lean_object* v_nargs_94_; lean_object* v_dummy_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_args_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_val_89_ = lean_ctor_get(v_____x_88_, 0);
lean_inc_ref(v_val_89_);
lean_dec_ref_known(v_____x_88_, 1);
v_toConstantVal_90_ = lean_ctor_get(v_val_89_, 0);
lean_inc_ref(v_toConstantVal_90_);
v_numParams_91_ = lean_ctor_get(v_val_89_, 1);
lean_inc(v_numParams_91_);
v_numIndices_92_ = lean_ctor_get(v_val_89_, 2);
lean_inc(v_numIndices_92_);
v_ctors_93_ = lean_ctor_get(v_val_89_, 4);
lean_inc(v_ctors_93_);
v_nargs_94_ = l_Lean_Expr_getAppNumArgs(v_e_81_);
v_dummy_95_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0);
lean_inc(v_nargs_94_);
v___x_96_ = lean_mk_array(v_nargs_94_, v_dummy_95_);
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_sub(v_nargs_94_, v___x_97_);
lean_dec(v_nargs_94_);
v_args_99_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_81_, v___x_96_, v___x_98_);
v___x_100_ = lean_nat_add(v_numParams_91_, v___x_97_);
v___x_101_ = lean_nat_add(v___x_100_, v_numIndices_92_);
v___x_102_ = lean_nat_add(v___x_101_, v___x_97_);
lean_dec(v___x_101_);
v___x_103_ = l_Lean_InductiveVal_numCtors(v_val_89_);
lean_dec_ref(v_val_89_);
v___x_104_ = lean_nat_add(v___x_102_, v___x_103_);
lean_dec(v___x_103_);
v___x_105_ = lean_array_get_size(v_args_99_);
v___x_106_ = lean_nat_dec_le(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v_toPure_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v___x_104_);
lean_dec(v___x_102_);
lean_dec(v___x_100_);
lean_dec_ref(v_args_99_);
lean_dec(v_ctors_93_);
lean_dec(v_numIndices_92_);
lean_dec(v_numParams_91_);
lean_dec_ref(v_toConstantVal_90_);
lean_dec(v_toBind_87_);
lean_dec(v___f_86_);
lean_dec_ref(v_inst_85_);
lean_dec(v_declName_84_);
lean_dec(v_us_83_);
v_toPure_107_ = lean_ctor_get(v_toApplicative_82_, 1);
lean_inc(v_toPure_107_);
lean_dec_ref(v_toApplicative_82_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_2(v_toPure_107_, lean_box(0), v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v_params_111_; lean_object* v___x_112_; lean_object* v_motive_113_; lean_object* v_discrs_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_discrInfos_117_; lean_object* v_alts_118_; lean_object* v___y_120_; lean_object* v___y_121_; lean_object* v_lower_129_; lean_object* v_upper_130_; uint8_t v___x_137_; 
v___x_110_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_91_);
lean_inc_ref_n(v_args_99_, 3);
v_params_111_ = l_Array_toSubarray___redArg(v_args_99_, v___x_110_, v_numParams_91_);
v___x_112_ = l_Lean_instInhabitedExpr;
v_motive_113_ = lean_array_get(v___x_112_, v_args_99_, v_numParams_91_);
lean_dec(v_numParams_91_);
lean_inc(v___x_102_);
v_discrs_114_ = l_Array_toSubarray___redArg(v_args_99_, v___x_100_, v___x_102_);
v___x_115_ = lean_nat_add(v_numIndices_92_, v___x_97_);
lean_dec(v_numIndices_92_);
v___x_116_ = lean_box(0);
v_discrInfos_117_ = lean_mk_array(v___x_115_, v___x_116_);
lean_inc(v___x_104_);
v_alts_118_ = l_Array_toSubarray___redArg(v_args_99_, v___x_102_, v___x_104_);
v___x_137_ = lean_nat_dec_le(v___x_104_, v___x_110_);
if (v___x_137_ == 0)
{
v_lower_129_ = v___x_104_;
v_upper_130_ = v___x_105_;
goto v___jp_128_;
}
else
{
lean_dec(v___x_104_);
v_lower_129_ = v___x_110_;
v_upper_130_ = v___x_105_;
goto v___jp_128_;
}
v___jp_119_:
{
lean_object* v___f_122_; lean_object* v___x_123_; size_t v_sz_124_; size_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3), 12, 11);
lean_closure_set(v___f_122_, 0, v_toApplicative_82_);
lean_closure_set(v___f_122_, 1, v_params_111_);
lean_closure_set(v___f_122_, 2, v_discrs_114_);
lean_closure_set(v___f_122_, 3, v___x_110_);
lean_closure_set(v___f_122_, 4, v___y_121_);
lean_closure_set(v___f_122_, 5, v_discrInfos_117_);
lean_closure_set(v___f_122_, 6, v_us_83_);
lean_closure_set(v___f_122_, 7, v_alts_118_);
lean_closure_set(v___f_122_, 8, v___y_120_);
lean_closure_set(v___f_122_, 9, v_declName_84_);
lean_closure_set(v___f_122_, 10, v_motive_113_);
v___x_123_ = lean_array_mk(v_ctors_93_);
v_sz_124_ = lean_array_size(v___x_123_);
v___x_125_ = ((size_t)0ULL);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_85_, v___f_86_, v_sz_124_, v___x_125_, v___x_123_);
v___x_127_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_126_, v___f_122_);
return v___x_127_;
}
v___jp_128_:
{
lean_object* v_levelParams_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_levelParams_131_ = lean_ctor_get(v_toConstantVal_90_, 1);
lean_inc(v_levelParams_131_);
lean_dec_ref(v_toConstantVal_90_);
v___x_132_ = l_Array_toSubarray___redArg(v_args_99_, v_lower_129_, v_upper_130_);
v___x_133_ = l_List_lengthTR___redArg(v_levelParams_131_);
lean_dec(v_levelParams_131_);
v___x_134_ = l_List_lengthTR___redArg(v_us_83_);
v___x_135_ = lean_nat_dec_eq(v___x_133_, v___x_134_);
lean_dec(v___x_134_);
lean_dec(v___x_133_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1));
v___y_120_ = v___x_132_;
v___y_121_ = v___x_136_;
goto v___jp_119_;
}
else
{
v___y_120_ = v___x_132_;
v___y_121_ = v___x_116_;
goto v___jp_119_;
}
}
}
}
else
{
lean_object* v_toPure_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec_ref(v_____x_88_);
lean_dec(v_toBind_87_);
lean_dec(v___f_86_);
lean_dec_ref(v_inst_85_);
lean_dec(v_declName_84_);
lean_dec(v_us_83_);
lean_dec_ref(v_e_81_);
v_toPure_138_ = lean_ctor_get(v_toApplicative_82_, 1);
lean_inc(v_toPure_138_);
lean_dec_ref(v_toApplicative_82_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_2(v_toPure_138_, lean_box(0), v___x_139_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(lean_object* v___f_141_, uint8_t v_alsoCasesOn_142_, lean_object* v_declName_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_toBind_147_, lean_object* v___f_148_, lean_object* v_____do__lift_149_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed(lean_object* v___f_157_, lean_object* v_alsoCasesOn_158_, lean_object* v_declName_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_toBind_163_, lean_object* v___f_164_, lean_object* v_____do__lift_165_){
_start:
{
uint8_t v_alsoCasesOn_boxed_166_; lean_object* v_res_167_; 
v_alsoCasesOn_boxed_166_ = lean_unbox(v_alsoCasesOn_158_);
v_res_167_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(v___f_157_, v_alsoCasesOn_boxed_166_, v_declName_159_, v_inst_160_, v_inst_161_, v_inst_162_, v_toBind_163_, v___f_164_, v_____do__lift_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6(lean_object* v_e_168_, lean_object* v_toApplicative_169_, lean_object* v_us_170_, lean_object* v_declName_171_, lean_object* v_inst_172_, lean_object* v_toBind_173_, lean_object* v___f_174_, lean_object* v_____do__lift_175_){
_start:
{
if (lean_obj_tag(v_____do__lift_175_) == 1)
{
lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_216_; 
lean_dec(v___f_174_);
lean_dec(v_toBind_173_);
lean_dec_ref(v_inst_172_);
v_val_176_ = lean_ctor_get(v_____do__lift_175_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v_____do__lift_175_);
if (v_isSharedCheck_216_ == 0)
{
v___x_178_ = v_____do__lift_175_;
v_isShared_179_ = v_isSharedCheck_216_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_dec(v_____do__lift_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_216_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_dummy_180_; lean_object* v_nargs_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_args_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_dummy_180_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0);
v_nargs_181_ = l_Lean_Expr_getAppNumArgs(v_e_168_);
lean_inc(v_nargs_181_);
v___x_182_ = lean_mk_array(v_nargs_181_, v_dummy_180_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_sub(v_nargs_181_, v___x_183_);
lean_dec(v_nargs_181_);
v_args_185_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_168_, v___x_182_, v___x_184_);
v___x_186_ = lean_array_get_size(v_args_185_);
v___x_187_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_176_);
v___x_188_ = lean_nat_dec_lt(v___x_186_, v___x_187_);
lean_dec(v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v_toPure_189_; lean_object* v_numParams_190_; lean_object* v_numDiscrs_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v_toPure_189_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc(v_toPure_189_);
lean_dec_ref(v_toApplicative_169_);
v_numParams_190_ = lean_ctor_get(v_val_176_, 0);
v_numDiscrs_191_ = lean_ctor_get(v_val_176_, 1);
v___x_192_ = lean_array_mk(v_us_170_);
v___x_193_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_190_);
v___x_194_ = l_Array_extract___redArg(v_args_185_, v___x_193_, v_numParams_190_);
v___x_195_ = l_Lean_instInhabitedExpr;
v___x_196_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_176_);
v___x_197_ = lean_array_get(v___x_195_, v_args_185_, v___x_196_);
lean_dec(v___x_196_);
v___x_198_ = lean_nat_add(v_numParams_190_, v___x_183_);
v___x_199_ = lean_nat_add(v___x_198_, v_numDiscrs_191_);
lean_inc(v___x_199_);
lean_inc_ref_n(v_args_185_, 2);
v___x_200_ = l_Array_toSubarray___redArg(v_args_185_, v___x_198_, v___x_199_);
v___x_201_ = l_Subarray_copy___redArg(v___x_200_);
v___x_202_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_176_);
v___x_203_ = lean_nat_add(v___x_199_, v___x_202_);
lean_dec(v___x_202_);
lean_inc(v___x_203_);
v___x_204_ = l_Array_toSubarray___redArg(v_args_185_, v___x_199_, v___x_203_);
v___x_205_ = l_Subarray_copy___redArg(v___x_204_);
v___x_206_ = l_Array_toSubarray___redArg(v_args_185_, v___x_203_, v___x_186_);
v___x_207_ = l_Subarray_copy___redArg(v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_208_, 0, v_val_176_);
lean_ctor_set(v___x_208_, 1, v_declName_171_);
lean_ctor_set(v___x_208_, 2, v___x_192_);
lean_ctor_set(v___x_208_, 3, v___x_194_);
lean_ctor_set(v___x_208_, 4, v___x_197_);
lean_ctor_set(v___x_208_, 5, v___x_201_);
lean_ctor_set(v___x_208_, 6, v___x_205_);
lean_ctor_set(v___x_208_, 7, v___x_207_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_208_);
v___x_210_ = v___x_178_;
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
v___x_211_ = lean_apply_2(v_toPure_189_, lean_box(0), v___x_210_);
return v___x_211_;
}
}
else
{
lean_object* v_toPure_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref(v_args_185_);
lean_del_object(v___x_178_);
lean_dec(v_val_176_);
lean_dec(v_declName_171_);
lean_dec(v_us_170_);
v_toPure_213_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc(v_toPure_213_);
lean_dec_ref(v_toApplicative_169_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_2(v_toPure_213_, lean_box(0), v___x_214_);
return v___x_215_;
}
}
}
else
{
lean_object* v_getEnv_217_; lean_object* v___x_218_; 
lean_dec(v_____do__lift_175_);
lean_dec(v_declName_171_);
lean_dec(v_us_170_);
lean_dec_ref(v_toApplicative_169_);
lean_dec_ref(v_e_168_);
v_getEnv_217_ = lean_ctor_get(v_inst_172_, 0);
lean_inc(v_getEnv_217_);
lean_dec_ref(v_inst_172_);
v___x_218_ = lean_apply_4(v_toBind_173_, lean_box(0), lean_box(0), v_getEnv_217_, v___f_174_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_e_222_, uint8_t v_alsoCasesOn_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Lean_Expr_isApp(v_e_222_);
if (v___x_224_ == 0)
{
lean_object* v_toApplicative_225_; lean_object* v_toPure_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref(v_e_222_);
lean_dec_ref(v_inst_221_);
lean_dec_ref(v_inst_220_);
v_toApplicative_225_ = lean_ctor_get(v_inst_219_, 0);
lean_inc_ref(v_toApplicative_225_);
lean_dec_ref(v_inst_219_);
v_toPure_226_ = lean_ctor_get(v_toApplicative_225_, 1);
lean_inc(v_toPure_226_);
lean_dec_ref(v_toApplicative_225_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_apply_2(v_toPure_226_, lean_box(0), v___x_227_);
return v___x_228_;
}
else
{
lean_object* v___f_229_; lean_object* v___x_230_; 
lean_inc_ref(v_inst_219_);
v___f_229_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_229_, 0, v_inst_219_);
v___x_230_ = l_Lean_Expr_getAppFn(v_e_222_);
if (lean_obj_tag(v___x_230_) == 4)
{
lean_object* v_declName_231_; lean_object* v_us_232_; lean_object* v_toApplicative_233_; lean_object* v_toBind_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_declName_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_n(v_declName_231_, 4);
v_us_232_ = lean_ctor_get(v___x_230_, 1);
lean_inc_n(v_us_232_, 2);
lean_dec_ref_known(v___x_230_, 2);
v_toApplicative_233_ = lean_ctor_get(v_inst_219_, 0);
v_toBind_234_ = lean_ctor_get(v_inst_219_, 1);
lean_inc_n(v_toBind_234_, 5);
lean_inc_ref_n(v_inst_219_, 4);
lean_inc_ref_n(v_toApplicative_233_, 3);
v___f_235_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_235_, 0, v_toApplicative_233_);
lean_closure_set(v___f_235_, 1, v_inst_219_);
lean_inc_ref(v_inst_221_);
lean_inc_ref_n(v_inst_220_, 3);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2), 6, 5);
lean_closure_set(v___f_236_, 0, v_inst_219_);
lean_closure_set(v___f_236_, 1, v_inst_220_);
lean_closure_set(v___f_236_, 2, v_inst_221_);
lean_closure_set(v___f_236_, 3, v_toBind_234_);
lean_closure_set(v___f_236_, 4, v___f_235_);
lean_inc_ref(v_e_222_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4), 8, 7);
lean_closure_set(v___f_237_, 0, v_e_222_);
lean_closure_set(v___f_237_, 1, v_toApplicative_233_);
lean_closure_set(v___f_237_, 2, v_us_232_);
lean_closure_set(v___f_237_, 3, v_declName_231_);
lean_closure_set(v___f_237_, 4, v_inst_219_);
lean_closure_set(v___f_237_, 5, v___f_236_);
lean_closure_set(v___f_237_, 6, v_toBind_234_);
v___x_238_ = lean_box(v_alsoCasesOn_223_);
v___f_239_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_239_, 0, v___f_229_);
lean_closure_set(v___f_239_, 1, v___x_238_);
lean_closure_set(v___f_239_, 2, v_declName_231_);
lean_closure_set(v___f_239_, 3, v_inst_219_);
lean_closure_set(v___f_239_, 4, v_inst_220_);
lean_closure_set(v___f_239_, 5, v_inst_221_);
lean_closure_set(v___f_239_, 6, v_toBind_234_);
lean_closure_set(v___f_239_, 7, v___f_237_);
v___f_240_ = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6), 8, 7);
lean_closure_set(v___f_240_, 0, v_e_222_);
lean_closure_set(v___f_240_, 1, v_toApplicative_233_);
lean_closure_set(v___f_240_, 2, v_us_232_);
lean_closure_set(v___f_240_, 3, v_declName_231_);
lean_closure_set(v___f_240_, 4, v_inst_220_);
lean_closure_set(v___f_240_, 5, v_toBind_234_);
lean_closure_set(v___f_240_, 6, v___f_239_);
v___x_241_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_219_, v_inst_220_, v_declName_231_);
v___x_242_ = lean_apply_4(v_toBind_234_, lean_box(0), lean_box(0), v___x_241_, v___f_240_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v___x_230_);
lean_dec_ref(v___f_229_);
lean_dec_ref(v_e_222_);
lean_dec_ref(v_inst_221_);
lean_dec_ref(v_inst_220_);
v___x_243_ = lean_box(0);
v___x_244_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(v_inst_219_, v___x_243_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___redArg___boxed(lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_e_248_, lean_object* v_alsoCasesOn_249_){
_start:
{
uint8_t v_alsoCasesOn_boxed_250_; lean_object* v_res_251_; 
v_alsoCasesOn_boxed_250_ = lean_unbox(v_alsoCasesOn_249_);
v_res_251_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(v_inst_245_, v_inst_246_, v_inst_247_, v_e_248_, v_alsoCasesOn_boxed_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object* v_m_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_e_256_, uint8_t v_alsoCasesOn_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(v_inst_253_, v_inst_254_, v_inst_255_, v_e_256_, v_alsoCasesOn_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___boxed(lean_object* v_m_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_e_263_, lean_object* v_alsoCasesOn_264_){
_start:
{
uint8_t v_alsoCasesOn_boxed_265_; lean_object* v_res_266_; 
v_alsoCasesOn_boxed_265_ = lean_unbox(v_alsoCasesOn_264_);
v_res_266_ = l_Lean_Meta_matchMatcherApp_x3f(v_m_259_, v_inst_260_, v_inst_261_, v_inst_262_, v_e_263_, v_alsoCasesOn_boxed_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object* v_matcherApp_267_){
_start:
{
lean_object* v_toMatcherInfo_268_; lean_object* v___x_269_; 
v_toMatcherInfo_268_ = lean_ctor_get(v_matcherApp_267_, 0);
lean_inc_ref(v_toMatcherInfo_268_);
lean_dec_ref(v_matcherApp_267_);
v___x_269_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_toMatcherInfo_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object* v_matcherApp_270_){
_start:
{
lean_object* v_matcherName_271_; lean_object* v_matcherLevels_272_; lean_object* v_params_273_; lean_object* v_motive_274_; lean_object* v_discrs_275_; lean_object* v_alts_276_; lean_object* v_remaining_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_result_280_; lean_object* v_result_281_; lean_object* v_result_282_; lean_object* v_result_283_; lean_object* v___x_284_; 
v_matcherName_271_ = lean_ctor_get(v_matcherApp_270_, 1);
lean_inc(v_matcherName_271_);
v_matcherLevels_272_ = lean_ctor_get(v_matcherApp_270_, 2);
lean_inc_ref(v_matcherLevels_272_);
v_params_273_ = lean_ctor_get(v_matcherApp_270_, 3);
lean_inc_ref(v_params_273_);
v_motive_274_ = lean_ctor_get(v_matcherApp_270_, 4);
lean_inc_ref(v_motive_274_);
v_discrs_275_ = lean_ctor_get(v_matcherApp_270_, 5);
lean_inc_ref(v_discrs_275_);
v_alts_276_ = lean_ctor_get(v_matcherApp_270_, 6);
lean_inc_ref(v_alts_276_);
v_remaining_277_ = lean_ctor_get(v_matcherApp_270_, 7);
lean_inc_ref(v_remaining_277_);
lean_dec_ref(v_matcherApp_270_);
v___x_278_ = lean_array_to_list(v_matcherLevels_272_);
v___x_279_ = l_Lean_mkConst(v_matcherName_271_, v___x_278_);
v_result_280_ = l_Lean_mkAppN(v___x_279_, v_params_273_);
lean_dec_ref(v_params_273_);
v_result_281_ = l_Lean_Expr_app___override(v_result_280_, v_motive_274_);
v_result_282_ = l_Lean_mkAppN(v_result_281_, v_discrs_275_);
lean_dec_ref(v_discrs_275_);
v_result_283_ = l_Lean_mkAppN(v_result_282_, v_alts_276_);
lean_dec_ref(v_alts_276_);
v___x_284_ = l_Lean_mkAppN(v_result_283_, v_remaining_277_);
lean_dec_ref(v_remaining_277_);
return v___x_284_;
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
