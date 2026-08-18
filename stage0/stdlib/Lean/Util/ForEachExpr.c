// Lean compiler output
// Module: Lean.Util.ForEachExpr
// Imports: public import Lean.Expr public import Lean.Util.MonadCache
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ForEachExpr_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExpr_visit___redArg___closed__0 = (const lean_object*)&l_Lean_ForEachExpr_visit___redArg___closed__0_value;
static const lean_closure_object l_Lean_ForEachExpr_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExpr_visit___redArg___closed__1 = (const lean_object*)&l_Lean_ForEachExpr_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_forEach_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEach_x27___redArg___closed__0;
static lean_once_cell_t l_Lean_Expr_forEach_x27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEach_x27___redArg___closed__1;
static lean_once_cell_t l_Lean_Expr_forEach_x27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEach_x27___redArg___closed__2;
static lean_once_cell_t l_Lean_Expr_forEach_x27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEach_x27___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9(lean_object* v_toApplicative_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_e_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_toPure_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_toPure_6_ = lean_ctor_get(v_toApplicative_1_, 1);
lean_inc(v_toPure_6_);
lean_dec_ref(v_toApplicative_1_);
v___x_7_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2_, v___x_3_, v_a_5_, v_e_4_);
v___x_8_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9___boxed(lean_object* v_toApplicative_9_, lean_object* v___x_10_, lean_object* v___x_11_, lean_object* v_e_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_ForEachExpr_visit___redArg___lam__9(v_toApplicative_9_, v___x_10_, v___x_11_, v_e_12_, v_a_13_);
lean_dec_ref(v_a_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__8(lean_object* v_g_15_, lean_object* v_e_16_, lean_object* v_toBind_17_, lean_object* v___f_18_, lean_object* v___f_19_, lean_object* v_toApplicative_20_, lean_object* v_a_21_){
_start:
{
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec_ref(v_toApplicative_20_);
v___x_22_ = lean_apply_1(v_g_15_, v_e_16_);
lean_inc(v_toBind_17_);
v___x_23_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v___x_22_, v___f_18_);
v___x_24_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v___x_23_, v___f_19_);
return v___x_24_;
}
else
{
lean_object* v_val_25_; lean_object* v_toPure_26_; lean_object* v___x_27_; 
lean_dec(v___f_19_);
lean_dec(v___f_18_);
lean_dec(v_toBind_17_);
lean_dec_ref(v_e_16_);
lean_dec(v_g_15_);
v_val_25_ = lean_ctor_get(v_a_21_, 0);
lean_inc(v_val_25_);
lean_dec_ref_known(v_a_21_, 1);
v_toPure_26_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_inc(v_toPure_26_);
lean_dec_ref(v_toApplicative_20_);
v___x_27_ = lean_apply_2(v_toPure_26_, lean_box(0), v_val_25_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__5(lean_object* v_toApplicative_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_toPure_31_; lean_object* v___x_32_; 
v_toPure_31_ = lean_ctor_get(v_toApplicative_28_, 1);
lean_inc(v_toPure_31_);
lean_dec_ref(v_toApplicative_28_);
v___x_32_ = lean_apply_2(v_toPure_31_, lean_box(0), v_a_29_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__6(lean_object* v___x_33_, lean_object* v___x_34_, lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_s_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___y_40_; lean_object* v_i_41_; lean_object* v___y_48_; lean_object* v___y_60_; lean_object* v_i_61_; lean_object* v___x_79_; 
v___x_38_ = lean_box(0);
lean_inc_ref(v_e_35_);
lean_inc_ref(v___x_34_);
lean_inc_ref(v___x_33_);
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_33_, v___x_34_, v_s_37_, v_e_35_);
switch(lean_obj_tag(v___x_79_))
{
case 0:
{
lean_object* v_index_80_; lean_object* v_size_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v___x_34_);
lean_dec_ref(v___x_33_);
v_index_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_index_80_);
lean_dec_ref_known(v___x_79_, 3);
v_size_81_ = lean_ctor_get(v_s_37_, 0);
lean_inc(v_size_81_);
v___x_82_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_37_, v_size_81_, v_index_80_, v_e_35_, v_a_36_);
lean_dec(v_index_80_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_38_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
return v___x_83_;
}
case 1:
{
lean_object* v_index_84_; lean_object* v_size_85_; lean_object* v_keyArray_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_index_84_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_index_84_);
lean_dec_ref_known(v___x_79_, 1);
v_size_85_ = lean_ctor_get(v_s_37_, 0);
v_keyArray_86_ = lean_ctor_get(v_s_37_, 1);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_size_85_, v___x_87_);
v___x_89_ = lean_array_get_size(v_keyArray_86_);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec(v___x_88_);
lean_dec(v_index_84_);
goto v___jp_67_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_91_ = lean_unsigned_to_nat(4u);
v___x_92_ = lean_nat_mul(v___x_88_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = lean_nat_mul(v___x_89_, v___x_93_);
v___x_95_ = lean_nat_dec_le(v___x_92_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_92_);
if (v___x_95_ == 0)
{
lean_dec(v___x_88_);
lean_dec(v_index_84_);
goto v___jp_67_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec_ref(v___x_34_);
lean_dec_ref(v___x_33_);
v___x_96_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_37_, v___x_88_, v_index_84_, v_e_35_, v_a_36_);
lean_dec(v_index_84_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_38_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
return v___x_97_;
}
}
}
default: 
{
lean_object* v_size_98_; lean_object* v_keyArray_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_size_98_ = lean_ctor_get(v_s_37_, 0);
v_keyArray_99_ = lean_ctor_get(v_s_37_, 1);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_size_98_, v___x_100_);
v___x_102_ = lean_array_get_size(v_keyArray_99_);
v___x_103_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
lean_dec(v___x_101_);
lean_inc_ref(v___x_34_);
lean_inc_ref(v___x_33_);
v___x_104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_33_, v___x_34_, v_s_37_);
v___y_48_ = v___x_104_;
goto v___jp_47_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_105_ = lean_unsigned_to_nat(4u);
v___x_106_ = lean_nat_mul(v___x_101_, v___x_105_);
lean_dec(v___x_101_);
v___x_107_ = lean_unsigned_to_nat(3u);
v___x_108_ = lean_nat_mul(v___x_102_, v___x_107_);
v___x_109_ = lean_nat_dec_le(v___x_106_, v___x_108_);
lean_dec(v___x_108_);
lean_dec(v___x_106_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_inc_ref(v___x_34_);
lean_inc_ref(v___x_33_);
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_33_, v___x_34_, v_s_37_);
v___y_48_ = v___x_110_;
goto v___jp_47_;
}
else
{
v___y_48_ = v_s_37_;
goto v___jp_47_;
}
}
}
}
v___jp_39_:
{
lean_object* v_size_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_size_42_ = lean_ctor_get(v___y_40_, 0);
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_add(v_size_42_, v___x_43_);
v___x_45_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_40_, v___x_44_, v_i_41_, v_e_35_, v_a_36_);
lean_dec(v_i_41_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_38_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
return v___x_46_;
}
v___jp_47_:
{
lean_object* v___x_49_; 
lean_inc_ref(v_e_35_);
v___x_49_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_33_, v___x_34_, v___y_48_, v_e_35_);
switch(lean_obj_tag(v___x_49_))
{
case 0:
{
lean_object* v_index_50_; lean_object* v_size_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_index_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_index_50_);
lean_dec_ref_known(v___x_49_, 3);
v_size_51_ = lean_ctor_get(v___y_48_, 0);
lean_inc(v_size_51_);
v___x_52_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_48_, v_size_51_, v_index_50_, v_e_35_, v_a_36_);
lean_dec(v_index_50_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_38_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
return v___x_53_;
}
case 1:
{
lean_object* v_index_54_; 
v_index_54_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_index_54_);
lean_dec_ref_known(v___x_49_, 1);
v___y_40_ = v___y_48_;
v_i_41_ = v_index_54_;
goto v___jp_39_;
}
default: 
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_48_, v___x_55_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_index_57_; 
v_index_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_index_57_);
lean_dec_ref_known(v___x_56_, 1);
v___y_40_ = v___y_48_;
v_i_41_ = v_index_57_;
goto v___jp_39_;
}
else
{
lean_object* v___x_58_; 
lean_dec_ref(v_e_35_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_38_);
lean_ctor_set(v___x_58_, 1, v___y_48_);
return v___x_58_;
}
}
}
}
v___jp_59_:
{
lean_object* v_size_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_size_62_ = lean_ctor_get(v___y_60_, 0);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_add(v_size_62_, v___x_63_);
v___x_65_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_60_, v___x_64_, v_i_61_, v_e_35_, v_a_36_);
lean_dec(v_i_61_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_38_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc_ref(v___x_34_);
lean_inc_ref(v___x_33_);
v___x_68_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_33_, v___x_34_, v_s_37_);
lean_inc_ref(v_e_35_);
v___x_69_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_33_, v___x_34_, v___x_68_, v_e_35_);
switch(lean_obj_tag(v___x_69_))
{
case 0:
{
lean_object* v_index_70_; lean_object* v_size_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_index_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_index_70_);
lean_dec_ref_known(v___x_69_, 3);
v_size_71_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_size_71_);
v___x_72_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_68_, v_size_71_, v_index_70_, v_e_35_, v_a_36_);
lean_dec(v_index_70_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_38_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
case 1:
{
lean_object* v_index_74_; 
v_index_74_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_index_74_);
lean_dec_ref_known(v___x_69_, 1);
v___y_60_ = v___x_68_;
v_i_61_ = v_index_74_;
goto v___jp_59_;
}
default: 
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_68_, v___x_75_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_index_77_; 
v_index_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_index_77_);
lean_dec_ref_known(v___x_76_, 1);
v___y_60_ = v___x_68_;
v_i_61_ = v_index_77_;
goto v___jp_59_;
}
else
{
lean_object* v___x_78_; 
lean_dec_ref(v_e_35_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_38_);
lean_ctor_set(v___x_78_, 1, v___x_68_);
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7(lean_object* v_toApplicative_111_, lean_object* v___x_112_, lean_object* v___x_113_, lean_object* v_e_114_, lean_object* v_a_115_, lean_object* v_inst_116_, lean_object* v_toBind_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___f_119_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__5), 3, 2);
lean_closure_set(v___f_119_, 0, v_toApplicative_111_);
lean_closure_set(v___f_119_, 1, v_a_118_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__6), 5, 4);
lean_closure_set(v___f_120_, 0, v___x_112_);
lean_closure_set(v___f_120_, 1, v___x_113_);
lean_closure_set(v___f_120_, 2, v_e_114_);
lean_closure_set(v___f_120_, 3, v_a_118_);
lean_inc(v_a_115_);
v___x_121_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_121_, 0, lean_box(0));
lean_closure_set(v___x_121_, 1, lean_box(0));
lean_closure_set(v___x_121_, 2, lean_box(0));
lean_closure_set(v___x_121_, 3, v_a_115_);
lean_closure_set(v___x_121_, 4, v___f_120_);
v___x_122_ = lean_apply_2(v_inst_116_, lean_box(0), v___x_121_);
v___x_123_ = lean_apply_4(v_toBind_117_, lean_box(0), lean_box(0), v___x_122_, v___f_119_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7___boxed(lean_object* v_toApplicative_124_, lean_object* v___x_125_, lean_object* v___x_126_, lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_inst_129_, lean_object* v_toBind_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_ForEachExpr_visit___redArg___lam__7(v_toApplicative_124_, v___x_125_, v___x_126_, v_e_127_, v_a_128_, v_inst_129_, v_toBind_130_, v_a_131_);
lean_dec(v_a_128_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0___boxed(lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_g_135_, lean_object* v_b_136_, lean_object* v___y_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_ForEachExpr_visit___redArg___lam__0(v_inst_133_, v_inst_134_, v_g_135_, v_b_136_, v___y_137_, v_a_138_);
lean_dec(v___y_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1(lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_g_142_, lean_object* v_body_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_ForEachExpr_visit___redArg(v_inst_140_, v_inst_141_, v_g_142_, v_body_143_, v_a_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1___boxed(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_g_149_, lean_object* v_body_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_ForEachExpr_visit___redArg___lam__1(v_inst_147_, v_inst_148_, v_g_149_, v_body_150_, v_a_151_, v_a_152_);
lean_dec(v_a_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2(lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_g_156_, lean_object* v_value_157_, lean_object* v_a_158_, lean_object* v_toBind_159_, lean_object* v___f_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = l_Lean_ForEachExpr_visit___redArg(v_inst_154_, v_inst_155_, v_g_156_, v_value_157_, v_a_158_);
v___x_163_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_162_, v___f_160_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2___boxed(lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_g_166_, lean_object* v_value_167_, lean_object* v_a_168_, lean_object* v_toBind_169_, lean_object* v___f_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_ForEachExpr_visit___redArg___lam__2(v_inst_164_, v_inst_165_, v_g_166_, v_value_167_, v_a_168_, v_toBind_169_, v___f_170_, v_a_171_);
lean_dec(v_a_168_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_g_175_, lean_object* v_arg_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_ForEachExpr_visit___redArg(v_inst_173_, v_inst_174_, v_g_175_, v_arg_176_, v_a_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3___boxed(lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_g_182_, lean_object* v_arg_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_ForEachExpr_visit___redArg___lam__3(v_inst_180_, v_inst_181_, v_g_182_, v_arg_183_, v_a_184_, v_a_185_);
lean_dec(v_a_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4(lean_object* v_toApplicative_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_g_190_, lean_object* v_toBind_191_, lean_object* v_e_192_, lean_object* v_a_193_, uint8_t v_a_194_){
_start:
{
lean_object* v_d_196_; lean_object* v_b_197_; lean_object* v___y_198_; 
if (v_a_194_ == 0)
{
lean_object* v_toPure_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref(v_e_192_);
lean_dec(v_toBind_191_);
lean_dec(v_g_190_);
lean_dec_ref(v_inst_189_);
lean_dec(v_inst_188_);
v_toPure_202_ = lean_ctor_get(v_toApplicative_187_, 1);
lean_inc(v_toPure_202_);
lean_dec_ref(v_toApplicative_187_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_2(v_toPure_202_, lean_box(0), v___x_203_);
return v___x_204_;
}
else
{
switch(lean_obj_tag(v_e_192_))
{
case 7:
{
lean_object* v_binderType_205_; lean_object* v_body_206_; 
lean_dec_ref(v_toApplicative_187_);
v_binderType_205_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_binderType_205_);
v_body_206_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_body_206_);
lean_dec_ref_known(v_e_192_, 3);
v_d_196_ = v_binderType_205_;
v_b_197_ = v_body_206_;
v___y_198_ = v_a_193_;
goto v___jp_195_;
}
case 6:
{
lean_object* v_binderType_207_; lean_object* v_body_208_; 
lean_dec_ref(v_toApplicative_187_);
v_binderType_207_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_binderType_207_);
v_body_208_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_body_208_);
lean_dec_ref_known(v_e_192_, 3);
v_d_196_ = v_binderType_207_;
v_b_197_ = v_body_208_;
v___y_198_ = v_a_193_;
goto v___jp_195_;
}
case 8:
{
lean_object* v_type_209_; lean_object* v_value_210_; lean_object* v_body_211_; lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref(v_toApplicative_187_);
v_type_209_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_type_209_);
v_value_210_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_value_210_);
v_body_211_ = lean_ctor_get(v_e_192_, 3);
lean_inc_ref(v_body_211_);
lean_dec_ref_known(v_e_192_, 4);
lean_inc_n(v_a_193_, 2);
lean_inc_n(v_g_190_, 2);
lean_inc_ref_n(v_inst_189_, 2);
lean_inc_n(v_inst_188_, 2);
v___f_212_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_212_, 0, v_inst_188_);
lean_closure_set(v___f_212_, 1, v_inst_189_);
lean_closure_set(v___f_212_, 2, v_g_190_);
lean_closure_set(v___f_212_, 3, v_body_211_);
lean_closure_set(v___f_212_, 4, v_a_193_);
lean_inc(v_toBind_191_);
v___f_213_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_213_, 0, v_inst_188_);
lean_closure_set(v___f_213_, 1, v_inst_189_);
lean_closure_set(v___f_213_, 2, v_g_190_);
lean_closure_set(v___f_213_, 3, v_value_210_);
lean_closure_set(v___f_213_, 4, v_a_193_);
lean_closure_set(v___f_213_, 5, v_toBind_191_);
lean_closure_set(v___f_213_, 6, v___f_212_);
v___x_214_ = l_Lean_ForEachExpr_visit___redArg(v_inst_188_, v_inst_189_, v_g_190_, v_type_209_, v_a_193_);
v___x_215_ = lean_apply_4(v_toBind_191_, lean_box(0), lean_box(0), v___x_214_, v___f_213_);
return v___x_215_;
}
case 5:
{
lean_object* v_fn_216_; lean_object* v_arg_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref(v_toApplicative_187_);
v_fn_216_ = lean_ctor_get(v_e_192_, 0);
lean_inc_ref(v_fn_216_);
v_arg_217_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_arg_217_);
lean_dec_ref_known(v_e_192_, 2);
lean_inc(v_a_193_);
lean_inc(v_g_190_);
lean_inc_ref(v_inst_189_);
lean_inc(v_inst_188_);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_218_, 0, v_inst_188_);
lean_closure_set(v___f_218_, 1, v_inst_189_);
lean_closure_set(v___f_218_, 2, v_g_190_);
lean_closure_set(v___f_218_, 3, v_arg_217_);
lean_closure_set(v___f_218_, 4, v_a_193_);
v___x_219_ = l_Lean_ForEachExpr_visit___redArg(v_inst_188_, v_inst_189_, v_g_190_, v_fn_216_, v_a_193_);
v___x_220_ = lean_apply_4(v_toBind_191_, lean_box(0), lean_box(0), v___x_219_, v___f_218_);
return v___x_220_;
}
case 10:
{
lean_object* v_expr_221_; lean_object* v___x_222_; 
lean_dec(v_toBind_191_);
lean_dec_ref(v_toApplicative_187_);
v_expr_221_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_expr_221_);
lean_dec_ref_known(v_e_192_, 2);
v___x_222_ = l_Lean_ForEachExpr_visit___redArg(v_inst_188_, v_inst_189_, v_g_190_, v_expr_221_, v_a_193_);
return v___x_222_;
}
case 11:
{
lean_object* v_struct_223_; lean_object* v___x_224_; 
lean_dec(v_toBind_191_);
lean_dec_ref(v_toApplicative_187_);
v_struct_223_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_struct_223_);
lean_dec_ref_known(v_e_192_, 3);
v___x_224_ = l_Lean_ForEachExpr_visit___redArg(v_inst_188_, v_inst_189_, v_g_190_, v_struct_223_, v_a_193_);
return v___x_224_;
}
default: 
{
lean_object* v_toPure_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref(v_e_192_);
lean_dec(v_toBind_191_);
lean_dec(v_g_190_);
lean_dec_ref(v_inst_189_);
lean_dec(v_inst_188_);
v_toPure_225_ = lean_ctor_get(v_toApplicative_187_, 1);
lean_inc(v_toPure_225_);
lean_dec_ref(v_toApplicative_187_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_apply_2(v_toPure_225_, lean_box(0), v___x_226_);
return v___x_227_;
}
}
}
v___jp_195_:
{
lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_inc(v___y_198_);
lean_inc(v_g_190_);
lean_inc_ref(v_inst_189_);
lean_inc(v_inst_188_);
v___f_199_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_199_, 0, v_inst_188_);
lean_closure_set(v___f_199_, 1, v_inst_189_);
lean_closure_set(v___f_199_, 2, v_g_190_);
lean_closure_set(v___f_199_, 3, v_b_197_);
lean_closure_set(v___f_199_, 4, v___y_198_);
v___x_200_ = l_Lean_ForEachExpr_visit___redArg(v_inst_188_, v_inst_189_, v_g_190_, v_d_196_, v___y_198_);
v___x_201_ = lean_apply_4(v_toBind_191_, lean_box(0), lean_box(0), v___x_200_, v___f_199_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4___boxed(lean_object* v_toApplicative_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_g_231_, lean_object* v_toBind_232_, lean_object* v_e_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_a_boxed_236_; lean_object* v_res_237_; 
v_a_boxed_236_ = lean_unbox(v_a_235_);
v_res_237_ = l_Lean_ForEachExpr_visit___redArg___lam__4(v_toApplicative_228_, v_inst_229_, v_inst_230_, v_g_231_, v_toBind_232_, v_e_233_, v_a_234_, v_a_boxed_236_);
lean_dec(v_a_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg(lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_g_242_, lean_object* v_e_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_toApplicative_245_; lean_object* v_toBind_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_toApplicative_245_ = lean_ctor_get(v_inst_241_, 0);
lean_inc_ref_n(v_toApplicative_245_, 4);
v_toBind_246_ = lean_ctor_get(v_inst_241_, 1);
lean_inc_n(v_toBind_246_, 5);
lean_inc_n(v_a_244_, 3);
lean_inc_ref_n(v_e_243_, 3);
lean_inc(v_g_242_);
lean_inc_n(v_inst_240_, 2);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_247_, 0, v_toApplicative_245_);
lean_closure_set(v___f_247_, 1, v_inst_240_);
lean_closure_set(v___f_247_, 2, v_inst_241_);
lean_closure_set(v___f_247_, 3, v_g_242_);
lean_closure_set(v___f_247_, 4, v_toBind_246_);
lean_closure_set(v___f_247_, 5, v_e_243_);
lean_closure_set(v___f_247_, 6, v_a_244_);
v___x_248_ = ((lean_object*)(l_Lean_ForEachExpr_visit___redArg___closed__0));
v___x_249_ = ((lean_object*)(l_Lean_ForEachExpr_visit___redArg___closed__1));
v___f_250_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__7___boxed), 8, 7);
lean_closure_set(v___f_250_, 0, v_toApplicative_245_);
lean_closure_set(v___f_250_, 1, v___x_248_);
lean_closure_set(v___f_250_, 2, v___x_249_);
lean_closure_set(v___f_250_, 3, v_e_243_);
lean_closure_set(v___f_250_, 4, v_a_244_);
lean_closure_set(v___f_250_, 5, v_inst_240_);
lean_closure_set(v___f_250_, 6, v_toBind_246_);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__8), 7, 6);
lean_closure_set(v___f_251_, 0, v_g_242_);
lean_closure_set(v___f_251_, 1, v_e_243_);
lean_closure_set(v___f_251_, 2, v_toBind_246_);
lean_closure_set(v___f_251_, 3, v___f_247_);
lean_closure_set(v___f_251_, 4, v___f_250_);
lean_closure_set(v___f_251_, 5, v_toApplicative_245_);
v___f_252_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__9___boxed), 5, 4);
lean_closure_set(v___f_252_, 0, v_toApplicative_245_);
lean_closure_set(v___f_252_, 1, v___x_248_);
lean_closure_set(v___f_252_, 2, v___x_249_);
lean_closure_set(v___f_252_, 3, v_e_243_);
v___x_253_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_253_, 0, lean_box(0));
lean_closure_set(v___x_253_, 1, lean_box(0));
lean_closure_set(v___x_253_, 2, v_a_244_);
v___x_254_ = lean_apply_2(v_inst_240_, lean_box(0), v___x_253_);
v___x_255_ = lean_apply_4(v_toBind_246_, lean_box(0), lean_box(0), v___x_254_, v___f_252_);
v___x_256_ = lean_apply_4(v_toBind_246_, lean_box(0), lean_box(0), v___x_255_, v___f_251_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0(lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_g_259_, lean_object* v_b_260_, lean_object* v___y_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_ForEachExpr_visit___redArg(v_inst_257_, v_inst_258_, v_g_259_, v_b_260_, v___y_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___boxed(lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_g_266_, lean_object* v_e_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_ForEachExpr_visit___redArg(v_inst_264_, v_inst_265_, v_g_266_, v_e_267_, v_a_268_);
lean_dec(v_a_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit(lean_object* v_00_u03c9_270_, lean_object* v_m_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_g_275_, lean_object* v_e_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_ForEachExpr_visit___redArg(v_inst_273_, v_inst_274_, v_g_275_, v_e_276_, v_a_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___boxed(lean_object* v_00_u03c9_279_, lean_object* v_m_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_g_284_, lean_object* v_e_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_ForEachExpr_visit(v_00_u03c9_279_, v_m_280_, v_inst_281_, v_inst_282_, v_inst_283_, v_g_284_, v_e_285_, v_a_286_);
lean_dec(v_a_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__0(lean_object* v_toPure_288_, lean_object* v_____x_289_){
_start:
{
lean_object* v_fst_290_; lean_object* v___x_291_; 
v_fst_290_ = lean_ctor_get(v_____x_289_, 0);
lean_inc(v_fst_290_);
lean_dec_ref(v_____x_289_);
v___x_291_ = lean_apply_2(v_toPure_288_, lean_box(0), v_fst_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__1(lean_object* v_a_292_, lean_object* v_toPure_293_, lean_object* v_s_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_a_292_);
lean_ctor_set(v___x_295_, 1, v_s_294_);
v___x_296_ = lean_apply_2(v_toPure_293_, lean_box(0), v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__2(lean_object* v_toPure_297_, lean_object* v_ref_298_, lean_object* v_inst_299_, lean_object* v_toBind_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_302_, 0, v_a_301_);
lean_closure_set(v___f_302_, 1, v_toPure_297_);
v___x_303_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_303_, 0, lean_box(0));
lean_closure_set(v___x_303_, 1, lean_box(0));
lean_closure_set(v___x_303_, 2, v_ref_298_);
v___x_304_ = lean_apply_2(v_inst_299_, lean_box(0), v___x_303_);
v___x_305_ = lean_apply_4(v_toBind_300_, lean_box(0), lean_box(0), v___x_304_, v___f_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__3(lean_object* v_toPure_306_, lean_object* v_inst_307_, lean_object* v_toBind_308_, lean_object* v_inst_309_, lean_object* v_f_310_, lean_object* v_e_311_, lean_object* v_ref_312_){
_start:
{
lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_inc(v_toBind_308_);
lean_inc(v_inst_307_);
lean_inc(v_ref_312_);
v___f_313_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_313_, 0, v_toPure_306_);
lean_closure_set(v___f_313_, 1, v_ref_312_);
lean_closure_set(v___f_313_, 2, v_inst_307_);
lean_closure_set(v___f_313_, 3, v_toBind_308_);
v___x_314_ = l_Lean_ForEachExpr_visit___redArg(v_inst_307_, v_inst_309_, v_f_310_, v_e_311_, v_ref_312_);
lean_dec(v_ref_312_);
v___x_315_ = lean_apply_4(v_toBind_308_, lean_box(0), lean_box(0), v___x_314_, v___f_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_316_; lean_object* v___x_317_; 
v_cellCount_316_ = lean_unsigned_to_nat(16u);
v___x_317_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_318_; lean_object* v___x_319_; 
v_cellCount_318_ = lean_unsigned_to_nat(16u);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__1, &l_Lean_Expr_forEach_x27___redArg___closed__1_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__1);
v___x_321_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__0, &l_Lean_Expr_forEach_x27___redArg___closed__0_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__0);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_320_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__3(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
v___x_325_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, lean_box(0));
lean_closure_set(v___x_325_, 2, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg(lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_e_328_, lean_object* v_f_329_){
_start:
{
lean_object* v_toApplicative_330_; lean_object* v_toBind_331_; lean_object* v_toPure_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_toApplicative_330_ = lean_ctor_get(v_inst_327_, 0);
v_toBind_331_ = lean_ctor_get(v_inst_327_, 1);
lean_inc_n(v_toBind_331_, 3);
v_toPure_332_ = lean_ctor_get(v_toApplicative_330_, 1);
lean_inc_n(v_toPure_332_, 2);
v___x_333_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__3, &l_Lean_Expr_forEach_x27___redArg___closed__3_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__3);
lean_inc(v_inst_326_);
v___x_334_ = lean_apply_2(v_inst_326_, lean_box(0), v___x_333_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_335_, 0, v_toPure_332_);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_336_, 0, v_toPure_332_);
lean_closure_set(v___f_336_, 1, v_inst_326_);
lean_closure_set(v___f_336_, 2, v_toBind_331_);
lean_closure_set(v___f_336_, 3, v_inst_327_);
lean_closure_set(v___f_336_, 4, v_f_329_);
lean_closure_set(v___f_336_, 5, v_e_328_);
v___x_337_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_334_, v___f_336_);
v___x_338_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_337_, v___f_335_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27(lean_object* v_00_u03c9_339_, lean_object* v_m_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_e_344_, lean_object* v_f_345_){
_start:
{
lean_object* v_toApplicative_346_; lean_object* v_toBind_347_; lean_object* v_toPure_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_toApplicative_346_ = lean_ctor_get(v_inst_343_, 0);
v_toBind_347_ = lean_ctor_get(v_inst_343_, 1);
lean_inc_n(v_toBind_347_, 3);
v_toPure_348_ = lean_ctor_get(v_toApplicative_346_, 1);
lean_inc_n(v_toPure_348_, 2);
v___x_349_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__3, &l_Lean_Expr_forEach_x27___redArg___closed__3_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__3);
lean_inc(v_inst_342_);
v___x_350_ = lean_apply_2(v_inst_342_, lean_box(0), v___x_349_);
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_351_, 0, v_toPure_348_);
v___f_352_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_352_, 0, v_toPure_348_);
lean_closure_set(v___f_352_, 1, v_inst_342_);
lean_closure_set(v___f_352_, 2, v_toBind_347_);
lean_closure_set(v___f_352_, 3, v_inst_343_);
lean_closure_set(v___f_352_, 4, v_f_345_);
lean_closure_set(v___f_352_, 5, v_e_344_);
v___x_353_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_350_, v___f_352_);
v___x_354_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_353_, v___f_351_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__1(lean_object* v_toPure_355_, lean_object* v_____r_356_){
_start:
{
uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = 1;
v___x_358_ = lean_box(v___x_357_);
v___x_359_ = lean_apply_2(v_toPure_355_, lean_box(0), v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__0(lean_object* v_f_360_, lean_object* v_toBind_361_, lean_object* v___f_362_, lean_object* v_e_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_apply_1(v_f_360_, v_e_363_);
v___x_365_ = lean_apply_4(v_toBind_361_, lean_box(0), lean_box(0), v___x_364_, v___f_362_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__4(lean_object* v_toPure_366_, lean_object* v_inst_367_, lean_object* v_toBind_368_, lean_object* v_inst_369_, lean_object* v___f_370_, lean_object* v_e_371_, lean_object* v_ref_372_){
_start:
{
lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc(v_toBind_368_);
lean_inc(v_inst_367_);
lean_inc(v_ref_372_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_373_, 0, v_toPure_366_);
lean_closure_set(v___f_373_, 1, v_ref_372_);
lean_closure_set(v___f_373_, 2, v_inst_367_);
lean_closure_set(v___f_373_, 3, v_toBind_368_);
v___x_374_ = l_Lean_ForEachExpr_visit___redArg(v_inst_367_, v_inst_369_, v___f_370_, v_e_371_, v_ref_372_);
lean_dec(v_ref_372_);
v___x_375_ = lean_apply_4(v_toBind_368_, lean_box(0), lean_box(0), v___x_374_, v___f_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_e_378_, lean_object* v_f_379_){
_start:
{
lean_object* v_toApplicative_380_; lean_object* v_toBind_381_; lean_object* v_toPure_382_; lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_toApplicative_380_ = lean_ctor_get(v_inst_377_, 0);
v_toBind_381_ = lean_ctor_get(v_inst_377_, 1);
lean_inc_n(v_toBind_381_, 4);
v_toPure_382_ = lean_ctor_get(v_toApplicative_380_, 1);
lean_inc_n(v_toPure_382_, 3);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_383_, 0, v_toPure_382_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__1), 2, 1);
lean_closure_set(v___f_384_, 0, v_toPure_382_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__0), 4, 3);
lean_closure_set(v___f_385_, 0, v_f_379_);
lean_closure_set(v___f_385_, 1, v_toBind_381_);
lean_closure_set(v___f_385_, 2, v___f_384_);
lean_inc(v_inst_376_);
v___f_386_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__4), 7, 6);
lean_closure_set(v___f_386_, 0, v_toPure_382_);
lean_closure_set(v___f_386_, 1, v_inst_376_);
lean_closure_set(v___f_386_, 2, v_toBind_381_);
lean_closure_set(v___f_386_, 3, v_inst_377_);
lean_closure_set(v___f_386_, 4, v___f_385_);
lean_closure_set(v___f_386_, 5, v_e_378_);
v___x_387_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__3, &l_Lean_Expr_forEach_x27___redArg___closed__3_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__3);
v___x_388_ = lean_apply_2(v_inst_376_, lean_box(0), v___x_387_);
v___x_389_ = lean_apply_4(v_toBind_381_, lean_box(0), lean_box(0), v___x_388_, v___f_386_);
v___x_390_ = lean_apply_4(v_toBind_381_, lean_box(0), lean_box(0), v___x_389_, v___f_383_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach(lean_object* v_00_u03c9_391_, lean_object* v_m_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_e_396_, lean_object* v_f_397_){
_start:
{
lean_object* v_toApplicative_398_; lean_object* v_toBind_399_; lean_object* v_toPure_400_; lean_object* v___f_401_; lean_object* v___f_402_; lean_object* v___f_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_toApplicative_398_ = lean_ctor_get(v_inst_395_, 0);
v_toBind_399_ = lean_ctor_get(v_inst_395_, 1);
lean_inc_n(v_toBind_399_, 4);
v_toPure_400_ = lean_ctor_get(v_toApplicative_398_, 1);
lean_inc_n(v_toPure_400_, 3);
v___f_401_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_401_, 0, v_toPure_400_);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__1), 2, 1);
lean_closure_set(v___f_402_, 0, v_toPure_400_);
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__0), 4, 3);
lean_closure_set(v___f_403_, 0, v_f_397_);
lean_closure_set(v___f_403_, 1, v_toBind_399_);
lean_closure_set(v___f_403_, 2, v___f_402_);
lean_inc(v_inst_394_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__4), 7, 6);
lean_closure_set(v___f_404_, 0, v_toPure_400_);
lean_closure_set(v___f_404_, 1, v_inst_394_);
lean_closure_set(v___f_404_, 2, v_toBind_399_);
lean_closure_set(v___f_404_, 3, v_inst_395_);
lean_closure_set(v___f_404_, 4, v___f_403_);
lean_closure_set(v___f_404_, 5, v_e_396_);
v___x_405_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__3, &l_Lean_Expr_forEach_x27___redArg___closed__3_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__3);
v___x_406_ = lean_apply_2(v_inst_394_, lean_box(0), v___x_405_);
v___x_407_ = lean_apply_4(v_toBind_399_, lean_box(0), lean_box(0), v___x_406_, v___f_404_);
v___x_408_ = lean_apply_4(v_toBind_399_, lean_box(0), lean_box(0), v___x_407_, v___f_401_);
return v___x_408_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_ForEachExpr(builtin);
}
#ifdef __cplusplus
}
#endif
