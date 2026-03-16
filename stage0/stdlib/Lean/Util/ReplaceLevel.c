// Lean compiler output
// Module: Lean.Util.ReplaceLevel
// Imports: public import Lean.Expr
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0 = (const lean_object*)&l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr = (const lean_object*)&l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
static const lean_string_object l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = (const lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value;
static const lean_ctor_object l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3 = (const lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_value;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object* v_f_x3f_1_, lean_object* v_u_2_){
_start:
{
lean_object* v___x_3_; 
lean_inc_ref(v_f_x3f_1_);
lean_inc(v_u_2_);
v___x_3_ = lean_apply_1(v_f_x3f_1_, v_u_2_);
if (lean_obj_tag(v___x_3_) == 0)
{
switch(lean_obj_tag(v_u_2_))
{
case 2:
{
lean_object* v_a_4_; lean_object* v_a_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_a_4_ = lean_ctor_get(v_u_2_, 0);
lean_inc(v_a_4_);
v_a_5_ = lean_ctor_get(v_u_2_, 1);
lean_inc(v_a_5_);
lean_dec_ref(v_u_2_);
lean_inc_ref(v_f_x3f_1_);
v___x_6_ = l_Lean_Level_replace(v_f_x3f_1_, v_a_4_);
v___x_7_ = l_Lean_Level_replace(v_f_x3f_1_, v_a_5_);
v___x_8_ = l_Lean_mkLevelMax_x27(v___x_6_, v___x_7_);
return v___x_8_;
}
case 3:
{
lean_object* v_a_9_; lean_object* v_a_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_a_9_ = lean_ctor_get(v_u_2_, 0);
lean_inc(v_a_9_);
v_a_10_ = lean_ctor_get(v_u_2_, 1);
lean_inc(v_a_10_);
lean_dec_ref(v_u_2_);
lean_inc_ref(v_f_x3f_1_);
v___x_11_ = l_Lean_Level_replace(v_f_x3f_1_, v_a_9_);
v___x_12_ = l_Lean_Level_replace(v_f_x3f_1_, v_a_10_);
v___x_13_ = l_Lean_mkLevelIMax_x27(v___x_11_, v___x_12_);
return v___x_13_;
}
case 1:
{
lean_object* v_a_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_a_14_ = lean_ctor_get(v_u_2_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v_u_2_);
v___x_15_ = l_Lean_Level_replace(v_f_x3f_1_, v_a_14_);
v___x_16_ = l_Lean_Level_succ___override(v___x_15_);
return v___x_16_;
}
default: 
{
lean_dec_ref(v_f_x3f_1_);
return v_u_2_;
}
}
}
else
{
lean_object* v_val_17_; 
lean_dec(v_u_2_);
lean_dec_ref(v_f_x3f_1_);
v_val_17_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_val_17_);
lean_dec_ref(v___x_3_);
return v_val_17_;
}
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0(void){
_start:
{
size_t v___x_18_; size_t v___x_19_; size_t v___x_20_; 
v___x_18_ = ((size_t)1ULL);
v___x_19_ = ((size_t)8192ULL);
v___x_20_ = lean_usize_sub(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize(void){
_start:
{
size_t v___x_21_; 
v___x_21_ = lean_usize_once(&l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0, &l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t v_i_22_, lean_object* v_key_23_, lean_object* v_result_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_keys_26_; lean_object* v_results_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_37_; 
v_keys_26_ = lean_ctor_get(v_a_25_, 0);
v_results_27_ = lean_ctor_get(v_a_25_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v_a_25_);
if (v_isSharedCheck_37_ == 0)
{
v___x_29_ = v_a_25_;
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_results_27_);
lean_inc(v_keys_26_);
lean_dec(v_a_25_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_31_ = lean_array_uset(v_keys_26_, v_i_22_, v_key_23_);
lean_inc_ref(v_result_24_);
v___x_32_ = lean_array_uset(v_results_27_, v_i_22_, v_result_24_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___x_32_);
lean_ctor_set(v___x_29_, 0, v___x_31_);
v___x_34_ = v___x_29_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_32_);
v___x_34_ = v_reuseFailAlloc_36_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_result_24_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* v_i_38_, lean_object* v_key_39_, lean_object* v_result_40_, lean_object* v_a_41_){
_start:
{
size_t v_i_boxed_42_; lean_object* v_res_43_; 
v_i_boxed_42_ = lean_unbox_usize(v_i_38_);
lean_dec(v_i_38_);
v_res_43_ = l_Lean_Expr_ReplaceLevelImpl_cache(v_i_boxed_42_, v_key_39_, v_result_40_, v_a_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object* v_f_x3f_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
if (lean_obj_tag(v_a_45_) == 0)
{
lean_object* v___x_47_; 
lean_dec_ref(v_f_x3f_44_);
v___x_47_ = l_List_reverse___redArg(v_a_46_);
return v___x_47_;
}
else
{
lean_object* v_head_48_; lean_object* v_tail_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_58_; 
v_head_48_ = lean_ctor_get(v_a_45_, 0);
v_tail_49_ = lean_ctor_get(v_a_45_, 1);
v_isSharedCheck_58_ = !lean_is_exclusive(v_a_45_);
if (v_isSharedCheck_58_ == 0)
{
v___x_51_ = v_a_45_;
v_isShared_52_ = v_isSharedCheck_58_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_tail_49_);
lean_inc(v_head_48_);
lean_dec(v_a_45_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_58_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
lean_inc_ref(v_f_x3f_44_);
v___x_53_ = l_Lean_Level_replace(v_f_x3f_44_, v_head_48_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v_a_46_);
lean_ctor_set(v___x_51_, 0, v___x_53_);
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v_a_46_);
v___x_55_ = v_reuseFailAlloc_57_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
v_a_45_ = v_tail_49_;
v_a_46_ = v___x_55_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* v_f_x3f_59_, size_t v_size_60_, lean_object* v_e_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_keys_63_; lean_object* v_results_64_; size_t v___x_65_; size_t v___x_66_; lean_object* v___x_67_; size_t v___x_68_; uint8_t v___x_69_; 
v_keys_63_ = lean_ctor_get(v_a_62_, 0);
v_results_64_ = lean_ctor_get(v_a_62_, 1);
v___x_65_ = lean_ptr_addr(v_e_61_);
v___x_66_ = lean_usize_mod(v___x_65_, v_size_60_);
v___x_67_ = lean_array_uget_borrowed(v_keys_63_, v___x_66_);
v___x_68_ = lean_ptr_addr(v___x_67_);
v___x_69_ = lean_usize_dec_eq(v___x_68_, v___x_65_);
if (v___x_69_ == 0)
{
switch(lean_obj_tag(v_e_61_))
{
case 7:
{
lean_object* v_binderName_70_; lean_object* v_binderType_71_; lean_object* v_body_72_; uint8_t v_binderInfo_73_; lean_object* v___x_74_; lean_object* v_fst_75_; lean_object* v_snd_76_; lean_object* v___x_77_; lean_object* v_fst_78_; lean_object* v_snd_79_; uint8_t v___y_81_; size_t v___x_88_; size_t v___x_89_; uint8_t v___x_90_; 
v_binderName_70_ = lean_ctor_get(v_e_61_, 0);
v_binderType_71_ = lean_ctor_get(v_e_61_, 1);
v_body_72_ = lean_ctor_get(v_e_61_, 2);
v_binderInfo_73_ = lean_ctor_get_uint8(v_e_61_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_71_);
lean_inc_ref(v_f_x3f_59_);
v___x_74_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_binderType_71_, v_a_62_);
v_fst_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_fst_75_);
v_snd_76_ = lean_ctor_get(v___x_74_, 1);
lean_inc(v_snd_76_);
lean_dec_ref(v___x_74_);
lean_inc_ref(v_body_72_);
v___x_77_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_body_72_, v_snd_76_);
v_fst_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_fst_78_);
v_snd_79_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_snd_79_);
lean_dec_ref(v___x_77_);
v___x_88_ = lean_ptr_addr(v_binderType_71_);
v___x_89_ = lean_ptr_addr(v_fst_75_);
v___x_90_ = lean_usize_dec_eq(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
v___y_81_ = v___x_90_;
goto v___jp_80_;
}
else
{
size_t v___x_91_; size_t v___x_92_; uint8_t v___x_93_; 
v___x_91_ = lean_ptr_addr(v_body_72_);
v___x_92_ = lean_ptr_addr(v_fst_78_);
v___x_93_ = lean_usize_dec_eq(v___x_91_, v___x_92_);
v___y_81_ = v___x_93_;
goto v___jp_80_;
}
v___jp_80_:
{
if (v___y_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_inc(v_binderName_70_);
v___x_82_ = l_Lean_Expr_forallE___override(v_binderName_70_, v_fst_75_, v_fst_78_, v_binderInfo_73_);
v___x_83_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_82_, v_snd_79_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_73_, v_binderInfo_73_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_inc(v_binderName_70_);
v___x_85_ = l_Lean_Expr_forallE___override(v_binderName_70_, v_fst_75_, v_fst_78_, v_binderInfo_73_);
v___x_86_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_85_, v_snd_79_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; 
lean_dec(v_fst_78_);
lean_dec(v_fst_75_);
lean_inc_ref(v_e_61_);
v___x_87_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_snd_79_);
return v___x_87_;
}
}
}
}
case 6:
{
lean_object* v_binderName_94_; lean_object* v_binderType_95_; lean_object* v_body_96_; uint8_t v_binderInfo_97_; lean_object* v___x_98_; lean_object* v_fst_99_; lean_object* v_snd_100_; lean_object* v___x_101_; lean_object* v_fst_102_; lean_object* v_snd_103_; uint8_t v___y_105_; size_t v___x_112_; size_t v___x_113_; uint8_t v___x_114_; 
v_binderName_94_ = lean_ctor_get(v_e_61_, 0);
v_binderType_95_ = lean_ctor_get(v_e_61_, 1);
v_body_96_ = lean_ctor_get(v_e_61_, 2);
v_binderInfo_97_ = lean_ctor_get_uint8(v_e_61_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_95_);
lean_inc_ref(v_f_x3f_59_);
v___x_98_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_binderType_95_, v_a_62_);
v_fst_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_fst_99_);
v_snd_100_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_snd_100_);
lean_dec_ref(v___x_98_);
lean_inc_ref(v_body_96_);
v___x_101_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_body_96_, v_snd_100_);
v_fst_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_fst_102_);
v_snd_103_ = lean_ctor_get(v___x_101_, 1);
lean_inc(v_snd_103_);
lean_dec_ref(v___x_101_);
v___x_112_ = lean_ptr_addr(v_binderType_95_);
v___x_113_ = lean_ptr_addr(v_fst_99_);
v___x_114_ = lean_usize_dec_eq(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
v___y_105_ = v___x_114_;
goto v___jp_104_;
}
else
{
size_t v___x_115_; size_t v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_ptr_addr(v_body_96_);
v___x_116_ = lean_ptr_addr(v_fst_102_);
v___x_117_ = lean_usize_dec_eq(v___x_115_, v___x_116_);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
v___jp_104_:
{
if (v___y_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_inc(v_binderName_94_);
v___x_106_ = l_Lean_Expr_lam___override(v_binderName_94_, v_fst_99_, v_fst_102_, v_binderInfo_97_);
v___x_107_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_106_, v_snd_103_);
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_97_, v_binderInfo_97_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_inc(v_binderName_94_);
v___x_109_ = l_Lean_Expr_lam___override(v_binderName_94_, v_fst_99_, v_fst_102_, v_binderInfo_97_);
v___x_110_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_109_, v_snd_103_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; 
lean_dec(v_fst_102_);
lean_dec(v_fst_99_);
lean_inc_ref(v_e_61_);
v___x_111_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_snd_103_);
return v___x_111_;
}
}
}
}
case 10:
{
lean_object* v_data_118_; lean_object* v_expr_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; size_t v___x_123_; size_t v___x_124_; uint8_t v___x_125_; 
v_data_118_ = lean_ctor_get(v_e_61_, 0);
v_expr_119_ = lean_ctor_get(v_e_61_, 1);
lean_inc_ref(v_expr_119_);
v___x_120_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_expr_119_, v_a_62_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_fst_121_);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_snd_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_ptr_addr(v_expr_119_);
v___x_124_ = lean_ptr_addr(v_fst_121_);
v___x_125_ = lean_usize_dec_eq(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_inc(v_data_118_);
v___x_126_ = l_Lean_Expr_mdata___override(v_data_118_, v_fst_121_);
v___x_127_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_126_, v_snd_122_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; 
lean_dec(v_fst_121_);
lean_inc_ref(v_e_61_);
v___x_128_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_snd_122_);
return v___x_128_;
}
}
case 8:
{
lean_object* v_declName_129_; lean_object* v_type_130_; lean_object* v_value_131_; lean_object* v_body_132_; uint8_t v_nondep_133_; lean_object* v___x_134_; lean_object* v_fst_135_; lean_object* v_snd_136_; lean_object* v___x_137_; lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_140_; lean_object* v_fst_141_; lean_object* v_snd_142_; uint8_t v___y_144_; size_t v___x_153_; size_t v___x_154_; uint8_t v___x_155_; 
v_declName_129_ = lean_ctor_get(v_e_61_, 0);
v_type_130_ = lean_ctor_get(v_e_61_, 1);
v_value_131_ = lean_ctor_get(v_e_61_, 2);
v_body_132_ = lean_ctor_get(v_e_61_, 3);
v_nondep_133_ = lean_ctor_get_uint8(v_e_61_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_130_);
lean_inc_ref(v_f_x3f_59_);
v___x_134_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_type_130_, v_a_62_);
v_fst_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_fst_135_);
v_snd_136_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_snd_136_);
lean_dec_ref(v___x_134_);
lean_inc_ref(v_value_131_);
lean_inc_ref(v_f_x3f_59_);
v___x_137_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_value_131_, v_snd_136_);
v_fst_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_fst_138_);
v_snd_139_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_snd_139_);
lean_dec_ref(v___x_137_);
lean_inc_ref(v_body_132_);
v___x_140_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_body_132_, v_snd_139_);
v_fst_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_fst_141_);
v_snd_142_ = lean_ctor_get(v___x_140_, 1);
lean_inc(v_snd_142_);
lean_dec_ref(v___x_140_);
v___x_153_ = lean_ptr_addr(v_type_130_);
v___x_154_ = lean_ptr_addr(v_fst_135_);
v___x_155_ = lean_usize_dec_eq(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
v___y_144_ = v___x_155_;
goto v___jp_143_;
}
else
{
size_t v___x_156_; size_t v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_ptr_addr(v_value_131_);
v___x_157_ = lean_ptr_addr(v_fst_138_);
v___x_158_ = lean_usize_dec_eq(v___x_156_, v___x_157_);
v___y_144_ = v___x_158_;
goto v___jp_143_;
}
v___jp_143_:
{
if (v___y_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_inc(v_declName_129_);
v___x_145_ = l_Lean_Expr_letE___override(v_declName_129_, v_fst_135_, v_fst_138_, v_fst_141_, v_nondep_133_);
v___x_146_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_145_, v_snd_142_);
return v___x_146_;
}
else
{
size_t v___x_147_; size_t v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_ptr_addr(v_body_132_);
v___x_148_ = lean_ptr_addr(v_fst_141_);
v___x_149_ = lean_usize_dec_eq(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_inc(v_declName_129_);
v___x_150_ = l_Lean_Expr_letE___override(v_declName_129_, v_fst_135_, v_fst_138_, v_fst_141_, v_nondep_133_);
v___x_151_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_150_, v_snd_142_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
lean_dec(v_fst_141_);
lean_dec(v_fst_138_);
lean_dec(v_fst_135_);
lean_inc_ref(v_e_61_);
v___x_152_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_snd_142_);
return v___x_152_;
}
}
}
}
case 5:
{
lean_object* v_fn_159_; lean_object* v_arg_160_; lean_object* v___x_161_; lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_164_; lean_object* v_fst_165_; lean_object* v_snd_166_; uint8_t v___y_168_; size_t v___x_172_; size_t v___x_173_; uint8_t v___x_174_; 
v_fn_159_ = lean_ctor_get(v_e_61_, 0);
v_arg_160_ = lean_ctor_get(v_e_61_, 1);
lean_inc_ref(v_fn_159_);
lean_inc_ref(v_f_x3f_59_);
v___x_161_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_fn_159_, v_a_62_);
v_fst_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_fst_162_);
v_snd_163_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_snd_163_);
lean_dec_ref(v___x_161_);
lean_inc_ref(v_arg_160_);
v___x_164_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_arg_160_, v_snd_163_);
v_fst_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_fst_165_);
v_snd_166_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_snd_166_);
lean_dec_ref(v___x_164_);
v___x_172_ = lean_ptr_addr(v_fn_159_);
v___x_173_ = lean_ptr_addr(v_fst_162_);
v___x_174_ = lean_usize_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
v___y_168_ = v___x_174_;
goto v___jp_167_;
}
else
{
size_t v___x_175_; size_t v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_ptr_addr(v_arg_160_);
v___x_176_ = lean_ptr_addr(v_fst_165_);
v___x_177_ = lean_usize_dec_eq(v___x_175_, v___x_176_);
v___y_168_ = v___x_177_;
goto v___jp_167_;
}
v___jp_167_:
{
if (v___y_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l_Lean_Expr_app___override(v_fst_162_, v_fst_165_);
v___x_170_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_169_, v_snd_166_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; 
lean_dec(v_fst_165_);
lean_dec(v_fst_162_);
lean_inc_ref(v_e_61_);
v___x_171_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_snd_166_);
return v___x_171_;
}
}
}
case 11:
{
lean_object* v_typeName_178_; lean_object* v_idx_179_; lean_object* v_struct_180_; lean_object* v___x_181_; lean_object* v_fst_182_; lean_object* v_snd_183_; size_t v___x_184_; size_t v___x_185_; uint8_t v___x_186_; 
v_typeName_178_ = lean_ctor_get(v_e_61_, 0);
v_idx_179_ = lean_ctor_get(v_e_61_, 1);
v_struct_180_ = lean_ctor_get(v_e_61_, 2);
lean_inc_ref(v_struct_180_);
v___x_181_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_59_, v_size_60_, v_struct_180_, v_a_62_);
v_fst_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_fst_182_);
v_snd_183_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_snd_183_);
lean_dec_ref(v___x_181_);
v___x_184_ = lean_ptr_addr(v_struct_180_);
v___x_185_ = lean_ptr_addr(v_fst_182_);
v___x_186_ = lean_usize_dec_eq(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc(v_idx_179_);
lean_inc(v_typeName_178_);
v___x_187_ = l_Lean_Expr_proj___override(v_typeName_178_, v_idx_179_, v_fst_182_);
v___x_188_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_187_, v_snd_183_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; 
lean_dec(v_fst_182_);
lean_inc_ref(v_e_61_);
v___x_189_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_snd_183_);
return v___x_189_;
}
}
case 3:
{
lean_object* v_u_190_; lean_object* v___x_191_; size_t v___x_192_; size_t v___x_193_; uint8_t v___x_194_; 
v_u_190_ = lean_ctor_get(v_e_61_, 0);
lean_inc(v_u_190_);
v___x_191_ = l_Lean_Level_replace(v_f_x3f_59_, v_u_190_);
v___x_192_ = lean_ptr_addr(v_u_190_);
v___x_193_ = lean_ptr_addr(v___x_191_);
v___x_194_ = lean_usize_dec_eq(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = l_Lean_Expr_sort___override(v___x_191_);
v___x_196_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_195_, v_a_62_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; 
lean_dec(v___x_191_);
lean_inc_ref(v_e_61_);
v___x_197_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_a_62_);
return v___x_197_;
}
}
case 4:
{
lean_object* v_declName_198_; lean_object* v_us_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_declName_198_ = lean_ctor_get(v_e_61_, 0);
v_us_199_ = lean_ctor_get(v_e_61_, 1);
v___x_200_ = lean_box(0);
lean_inc(v_us_199_);
v___x_201_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_59_, v_us_199_, v___x_200_);
v___x_202_ = l_ptrEqList___redArg(v_us_199_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc(v_declName_198_);
v___x_203_ = l_Lean_Expr_const___override(v_declName_198_, v___x_201_);
v___x_204_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v___x_203_, v_a_62_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
lean_dec(v___x_201_);
lean_inc_ref(v_e_61_);
v___x_205_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_66_, v_e_61_, v_e_61_, v_a_62_);
return v___x_205_;
}
}
default: 
{
lean_object* v___x_206_; 
lean_dec_ref(v_f_x3f_59_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_e_61_);
lean_ctor_set(v___x_206_, 1, v_a_62_);
return v___x_206_;
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref(v_e_61_);
lean_dec_ref(v_f_x3f_59_);
v___x_207_ = lean_array_uget(v_results_64_, v___x_66_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_a_62_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* v_f_x3f_209_, lean_object* v_size_210_, lean_object* v_e_211_, lean_object* v_a_212_){
_start:
{
size_t v_size_boxed_213_; lean_object* v_res_214_; 
v_size_boxed_213_ = lean_unbox_usize(v_size_210_);
lean_dec(v_size_210_);
v_res_214_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_209_, v_size_boxed_213_, v_e_211_, v_a_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* v_f_x3f_215_, size_t v_size_216_, lean_object* v_e_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_215_, v_size_216_, v_e_217_, v_a_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object* v_f_x3f_220_, lean_object* v_size_221_, lean_object* v_e_222_, lean_object* v_a_223_){
_start:
{
size_t v_size_boxed_224_; lean_object* v_res_225_; 
v_size_boxed_224_ = lean_unbox_usize(v_size_221_);
lean_dec(v_size_221_);
v_res_225_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(v_f_x3f_220_, v_size_boxed_224_, v_e_222_, v_a_223_);
return v_res_225_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0(void){
_start:
{
size_t v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_usize_once(&l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0, &l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0);
v___x_230_ = lean_usize_to_nat(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr));
v___x_232_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0);
v___x_233_ = lean_mk_array(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_box(0);
v___x_238_ = ((lean_object*)(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3));
v___x_239_ = l_Lean_Expr_const___override(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4);
v___x_241_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0);
v___x_242_ = lean_mk_array(v___x_241_, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5);
v___x_244_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* v_f_x3f_247_, lean_object* v_e_248_){
_start:
{
size_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_fst_252_; 
v___x_249_ = lean_usize_once(&l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0, &l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0);
v___x_250_ = l_Lean_Expr_ReplaceLevelImpl_initCache;
v___x_251_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_247_, v___x_249_, v_e_248_, v___x_250_);
v_fst_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_fst_252_);
lean_dec_ref(v___x_251_);
return v_fst_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object* v_f_x3f_253_, lean_object* v_x_254_){
_start:
{
switch(lean_obj_tag(v_x_254_))
{
case 7:
{
lean_object* v_binderName_255_; lean_object* v_binderType_256_; lean_object* v_body_257_; uint8_t v_binderInfo_258_; lean_object* v_d_259_; lean_object* v_b_260_; uint8_t v___y_262_; size_t v___x_266_; size_t v___x_267_; uint8_t v___x_268_; 
v_binderName_255_ = lean_ctor_get(v_x_254_, 0);
v_binderType_256_ = lean_ctor_get(v_x_254_, 1);
v_body_257_ = lean_ctor_get(v_x_254_, 2);
v_binderInfo_258_ = lean_ctor_get_uint8(v_x_254_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_256_);
lean_inc_ref(v_f_x3f_253_);
v_d_259_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_binderType_256_);
lean_inc_ref(v_body_257_);
v_b_260_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_body_257_);
v___x_266_ = lean_ptr_addr(v_binderType_256_);
v___x_267_ = lean_ptr_addr(v_d_259_);
v___x_268_ = lean_usize_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
v___y_262_ = v___x_268_;
goto v___jp_261_;
}
else
{
size_t v___x_269_; size_t v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_ptr_addr(v_body_257_);
v___x_270_ = lean_ptr_addr(v_b_260_);
v___x_271_ = lean_usize_dec_eq(v___x_269_, v___x_270_);
v___y_262_ = v___x_271_;
goto v___jp_261_;
}
v___jp_261_:
{
if (v___y_262_ == 0)
{
lean_object* v___x_263_; 
lean_inc(v_binderName_255_);
lean_dec_ref(v_x_254_);
v___x_263_ = l_Lean_Expr_forallE___override(v_binderName_255_, v_d_259_, v_b_260_, v_binderInfo_258_);
return v___x_263_;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_258_, v_binderInfo_258_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_inc(v_binderName_255_);
lean_dec_ref(v_x_254_);
v___x_265_ = l_Lean_Expr_forallE___override(v_binderName_255_, v_d_259_, v_b_260_, v_binderInfo_258_);
return v___x_265_;
}
else
{
lean_dec_ref(v_b_260_);
lean_dec_ref(v_d_259_);
return v_x_254_;
}
}
}
}
case 6:
{
lean_object* v_binderName_272_; lean_object* v_binderType_273_; lean_object* v_body_274_; uint8_t v_binderInfo_275_; lean_object* v_d_276_; lean_object* v_b_277_; uint8_t v___y_279_; size_t v___x_283_; size_t v___x_284_; uint8_t v___x_285_; 
v_binderName_272_ = lean_ctor_get(v_x_254_, 0);
v_binderType_273_ = lean_ctor_get(v_x_254_, 1);
v_body_274_ = lean_ctor_get(v_x_254_, 2);
v_binderInfo_275_ = lean_ctor_get_uint8(v_x_254_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_273_);
lean_inc_ref(v_f_x3f_253_);
v_d_276_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_binderType_273_);
lean_inc_ref(v_body_274_);
v_b_277_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_body_274_);
v___x_283_ = lean_ptr_addr(v_binderType_273_);
v___x_284_ = lean_ptr_addr(v_d_276_);
v___x_285_ = lean_usize_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
v___y_279_ = v___x_285_;
goto v___jp_278_;
}
else
{
size_t v___x_286_; size_t v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_ptr_addr(v_body_274_);
v___x_287_ = lean_ptr_addr(v_b_277_);
v___x_288_ = lean_usize_dec_eq(v___x_286_, v___x_287_);
v___y_279_ = v___x_288_;
goto v___jp_278_;
}
v___jp_278_:
{
if (v___y_279_ == 0)
{
lean_object* v___x_280_; 
lean_inc(v_binderName_272_);
lean_dec_ref(v_x_254_);
v___x_280_ = l_Lean_Expr_lam___override(v_binderName_272_, v_d_276_, v_b_277_, v_binderInfo_275_);
return v___x_280_;
}
else
{
uint8_t v___x_281_; 
v___x_281_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_275_, v_binderInfo_275_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_inc(v_binderName_272_);
lean_dec_ref(v_x_254_);
v___x_282_ = l_Lean_Expr_lam___override(v_binderName_272_, v_d_276_, v_b_277_, v_binderInfo_275_);
return v___x_282_;
}
else
{
lean_dec_ref(v_b_277_);
lean_dec_ref(v_d_276_);
return v_x_254_;
}
}
}
}
case 10:
{
lean_object* v_data_289_; lean_object* v_expr_290_; lean_object* v_b_291_; size_t v___x_292_; size_t v___x_293_; uint8_t v___x_294_; 
v_data_289_ = lean_ctor_get(v_x_254_, 0);
v_expr_290_ = lean_ctor_get(v_x_254_, 1);
lean_inc_ref(v_expr_290_);
v_b_291_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_expr_290_);
v___x_292_ = lean_ptr_addr(v_expr_290_);
v___x_293_ = lean_ptr_addr(v_b_291_);
v___x_294_ = lean_usize_dec_eq(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_inc(v_data_289_);
lean_dec_ref(v_x_254_);
v___x_295_ = l_Lean_Expr_mdata___override(v_data_289_, v_b_291_);
return v___x_295_;
}
else
{
lean_dec_ref(v_b_291_);
return v_x_254_;
}
}
case 8:
{
lean_object* v_declName_296_; lean_object* v_type_297_; lean_object* v_value_298_; lean_object* v_body_299_; uint8_t v_nondep_300_; lean_object* v_t_301_; lean_object* v_v_302_; lean_object* v_b_303_; uint8_t v___y_305_; size_t v___x_311_; size_t v___x_312_; uint8_t v___x_313_; 
v_declName_296_ = lean_ctor_get(v_x_254_, 0);
v_type_297_ = lean_ctor_get(v_x_254_, 1);
v_value_298_ = lean_ctor_get(v_x_254_, 2);
v_body_299_ = lean_ctor_get(v_x_254_, 3);
v_nondep_300_ = lean_ctor_get_uint8(v_x_254_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_297_);
lean_inc_ref(v_f_x3f_253_);
v_t_301_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_type_297_);
lean_inc_ref(v_value_298_);
lean_inc_ref(v_f_x3f_253_);
v_v_302_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_value_298_);
lean_inc_ref(v_body_299_);
v_b_303_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_body_299_);
v___x_311_ = lean_ptr_addr(v_type_297_);
v___x_312_ = lean_ptr_addr(v_t_301_);
v___x_313_ = lean_usize_dec_eq(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
v___y_305_ = v___x_313_;
goto v___jp_304_;
}
else
{
size_t v___x_314_; size_t v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_ptr_addr(v_value_298_);
v___x_315_ = lean_ptr_addr(v_v_302_);
v___x_316_ = lean_usize_dec_eq(v___x_314_, v___x_315_);
v___y_305_ = v___x_316_;
goto v___jp_304_;
}
v___jp_304_:
{
if (v___y_305_ == 0)
{
lean_object* v___x_306_; 
lean_inc(v_declName_296_);
lean_dec_ref(v_x_254_);
v___x_306_ = l_Lean_Expr_letE___override(v_declName_296_, v_t_301_, v_v_302_, v_b_303_, v_nondep_300_);
return v___x_306_;
}
else
{
size_t v___x_307_; size_t v___x_308_; uint8_t v___x_309_; 
v___x_307_ = lean_ptr_addr(v_body_299_);
v___x_308_ = lean_ptr_addr(v_b_303_);
v___x_309_ = lean_usize_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
lean_inc(v_declName_296_);
lean_dec_ref(v_x_254_);
v___x_310_ = l_Lean_Expr_letE___override(v_declName_296_, v_t_301_, v_v_302_, v_b_303_, v_nondep_300_);
return v___x_310_;
}
else
{
lean_dec_ref(v_b_303_);
lean_dec_ref(v_v_302_);
lean_dec_ref(v_t_301_);
return v_x_254_;
}
}
}
}
case 5:
{
lean_object* v_fn_317_; lean_object* v_arg_318_; lean_object* v_f_319_; lean_object* v_a_320_; uint8_t v___y_322_; size_t v___x_324_; size_t v___x_325_; uint8_t v___x_326_; 
v_fn_317_ = lean_ctor_get(v_x_254_, 0);
v_arg_318_ = lean_ctor_get(v_x_254_, 1);
lean_inc_ref(v_fn_317_);
lean_inc_ref(v_f_x3f_253_);
v_f_319_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_fn_317_);
lean_inc_ref(v_arg_318_);
v_a_320_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_arg_318_);
v___x_324_ = lean_ptr_addr(v_fn_317_);
v___x_325_ = lean_ptr_addr(v_f_319_);
v___x_326_ = lean_usize_dec_eq(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
v___y_322_ = v___x_326_;
goto v___jp_321_;
}
else
{
size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_ptr_addr(v_arg_318_);
v___x_328_ = lean_ptr_addr(v_a_320_);
v___x_329_ = lean_usize_dec_eq(v___x_327_, v___x_328_);
v___y_322_ = v___x_329_;
goto v___jp_321_;
}
v___jp_321_:
{
if (v___y_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v_x_254_);
v___x_323_ = l_Lean_Expr_app___override(v_f_319_, v_a_320_);
return v___x_323_;
}
else
{
lean_dec_ref(v_a_320_);
lean_dec_ref(v_f_319_);
return v_x_254_;
}
}
}
case 11:
{
lean_object* v_typeName_330_; lean_object* v_idx_331_; lean_object* v_struct_332_; lean_object* v_b_333_; size_t v___x_334_; size_t v___x_335_; uint8_t v___x_336_; 
v_typeName_330_ = lean_ctor_get(v_x_254_, 0);
v_idx_331_ = lean_ctor_get(v_x_254_, 1);
v_struct_332_ = lean_ctor_get(v_x_254_, 2);
lean_inc_ref(v_struct_332_);
v_b_333_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_253_, v_struct_332_);
v___x_334_ = lean_ptr_addr(v_struct_332_);
v___x_335_ = lean_ptr_addr(v_b_333_);
v___x_336_ = lean_usize_dec_eq(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_inc(v_idx_331_);
lean_inc(v_typeName_330_);
lean_dec_ref(v_x_254_);
v___x_337_ = l_Lean_Expr_proj___override(v_typeName_330_, v_idx_331_, v_b_333_);
return v___x_337_;
}
else
{
lean_dec_ref(v_b_333_);
return v_x_254_;
}
}
case 3:
{
lean_object* v_u_338_; lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; uint8_t v___x_342_; 
v_u_338_ = lean_ctor_get(v_x_254_, 0);
lean_inc(v_u_338_);
v___x_339_ = l_Lean_Level_replace(v_f_x3f_253_, v_u_338_);
v___x_340_ = lean_ptr_addr(v_u_338_);
v___x_341_ = lean_ptr_addr(v___x_339_);
v___x_342_ = lean_usize_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v_x_254_);
v___x_343_ = l_Lean_Expr_sort___override(v___x_339_);
return v___x_343_;
}
else
{
lean_dec(v___x_339_);
return v_x_254_;
}
}
case 4:
{
lean_object* v_declName_344_; lean_object* v_us_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_declName_344_ = lean_ctor_get(v_x_254_, 0);
v_us_345_ = lean_ctor_get(v_x_254_, 1);
v___x_346_ = lean_box(0);
lean_inc(v_us_345_);
v___x_347_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_253_, v_us_345_, v___x_346_);
v___x_348_ = l_ptrEqList___redArg(v_us_345_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_inc(v_declName_344_);
lean_dec_ref(v_x_254_);
v___x_349_ = l_Lean_Expr_const___override(v_declName_344_, v___x_347_);
return v___x_349_;
}
else
{
lean_dec(v___x_347_);
return v_x_254_;
}
}
default: 
{
lean_dec_ref(v_f_x3f_253_);
return v_x_254_;
}
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ReplaceLevel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_ReplaceLevel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ReplaceLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_ReplaceLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_ReplaceLevel(builtin);
}
#ifdef __cplusplus
}
#endif
