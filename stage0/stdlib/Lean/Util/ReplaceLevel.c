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
static const lean_string_object l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1 = (const lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_value;
static const lean_ctor_object l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = (const lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
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
lean_dec_ref_known(v_u_2_, 2);
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
lean_dec_ref_known(v_u_2_, 2);
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
lean_dec_ref_known(v_u_2_, 1);
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
lean_dec_ref_known(v___x_3_, 1);
return v_val_17_;
}
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize(void){
_start:
{
size_t v___x_18_; 
v___x_18_ = ((size_t)8191ULL);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t v_i_19_, lean_object* v_key_20_, lean_object* v_result_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_keys_23_; lean_object* v_results_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_34_; 
v_keys_23_ = lean_ctor_get(v_a_22_, 0);
v_results_24_ = lean_ctor_get(v_a_22_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_a_22_);
if (v_isSharedCheck_34_ == 0)
{
v___x_26_ = v_a_22_;
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_results_24_);
lean_inc(v_keys_23_);
lean_dec(v_a_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_28_ = lean_array_uset(v_keys_23_, v_i_19_, v_key_20_);
lean_inc_ref(v_result_21_);
v___x_29_ = lean_array_uset(v_results_24_, v_i_19_, v_result_21_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_29_);
lean_ctor_set(v___x_26_, 0, v___x_28_);
v___x_31_ = v___x_26_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_29_);
v___x_31_ = v_reuseFailAlloc_33_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; 
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v_result_21_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* v_i_35_, lean_object* v_key_36_, lean_object* v_result_37_, lean_object* v_a_38_){
_start:
{
size_t v_i_boxed_39_; lean_object* v_res_40_; 
v_i_boxed_39_ = lean_unbox_usize(v_i_35_);
lean_dec(v_i_35_);
v_res_40_ = l_Lean_Expr_ReplaceLevelImpl_cache(v_i_boxed_39_, v_key_36_, v_result_37_, v_a_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object* v_f_x3f_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
if (lean_obj_tag(v_a_42_) == 0)
{
lean_object* v___x_44_; 
lean_dec_ref(v_f_x3f_41_);
v___x_44_ = l_List_reverse___redArg(v_a_43_);
return v___x_44_;
}
else
{
lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_55_; 
v_head_45_ = lean_ctor_get(v_a_42_, 0);
v_tail_46_ = lean_ctor_get(v_a_42_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_a_42_);
if (v_isSharedCheck_55_ == 0)
{
v___x_48_ = v_a_42_;
v_isShared_49_ = v_isSharedCheck_55_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_tail_46_);
lean_inc(v_head_45_);
lean_dec(v_a_42_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_55_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc_ref(v_f_x3f_41_);
v___x_50_ = l_Lean_Level_replace(v_f_x3f_41_, v_head_45_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v_a_43_);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_a_43_);
v___x_52_ = v_reuseFailAlloc_54_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
v_a_42_ = v_tail_46_;
v_a_43_ = v___x_52_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* v_f_x3f_56_, size_t v_size_57_, lean_object* v_e_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_keys_60_; lean_object* v_results_61_; size_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; size_t v___x_65_; uint8_t v___x_66_; 
v_keys_60_ = lean_ctor_get(v_a_59_, 0);
v_results_61_ = lean_ctor_get(v_a_59_, 1);
v___x_62_ = lean_ptr_addr(v_e_58_);
v___x_63_ = lean_usize_mod(v___x_62_, v_size_57_);
v___x_64_ = lean_array_uget_borrowed(v_keys_60_, v___x_63_);
v___x_65_ = lean_ptr_addr(v___x_64_);
v___x_66_ = lean_usize_dec_eq(v___x_65_, v___x_62_);
if (v___x_66_ == 0)
{
switch(lean_obj_tag(v_e_58_))
{
case 7:
{
lean_object* v_binderName_67_; lean_object* v_binderType_68_; lean_object* v_body_69_; uint8_t v_binderInfo_70_; lean_object* v___x_71_; lean_object* v_fst_72_; lean_object* v_snd_73_; lean_object* v___x_74_; lean_object* v_fst_75_; lean_object* v_snd_76_; uint8_t v___y_78_; size_t v___x_85_; size_t v___x_86_; uint8_t v___x_87_; 
v_binderName_67_ = lean_ctor_get(v_e_58_, 0);
v_binderType_68_ = lean_ctor_get(v_e_58_, 1);
v_body_69_ = lean_ctor_get(v_e_58_, 2);
v_binderInfo_70_ = lean_ctor_get_uint8(v_e_58_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_68_);
lean_inc_ref(v_f_x3f_56_);
v___x_71_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_binderType_68_, v_a_59_);
v_fst_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_fst_72_);
v_snd_73_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_snd_73_);
lean_dec_ref(v___x_71_);
lean_inc_ref(v_body_69_);
v___x_74_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_body_69_, v_snd_73_);
v_fst_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_fst_75_);
v_snd_76_ = lean_ctor_get(v___x_74_, 1);
lean_inc(v_snd_76_);
lean_dec_ref(v___x_74_);
v___x_85_ = lean_ptr_addr(v_binderType_68_);
v___x_86_ = lean_ptr_addr(v_fst_72_);
v___x_87_ = lean_usize_dec_eq(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
v___y_78_ = v___x_87_;
goto v___jp_77_;
}
else
{
size_t v___x_88_; size_t v___x_89_; uint8_t v___x_90_; 
v___x_88_ = lean_ptr_addr(v_body_69_);
v___x_89_ = lean_ptr_addr(v_fst_75_);
v___x_90_ = lean_usize_dec_eq(v___x_88_, v___x_89_);
v___y_78_ = v___x_90_;
goto v___jp_77_;
}
v___jp_77_:
{
if (v___y_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_inc(v_binderName_67_);
v___x_79_ = l_Lean_Expr_forallE___override(v_binderName_67_, v_fst_72_, v_fst_75_, v_binderInfo_70_);
v___x_80_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_79_, v_snd_76_);
return v___x_80_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_70_, v_binderInfo_70_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_inc(v_binderName_67_);
v___x_82_ = l_Lean_Expr_forallE___override(v_binderName_67_, v_fst_72_, v_fst_75_, v_binderInfo_70_);
v___x_83_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_82_, v_snd_76_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; 
lean_dec(v_fst_75_);
lean_dec(v_fst_72_);
lean_inc_ref(v_e_58_);
v___x_84_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_snd_76_);
return v___x_84_;
}
}
}
}
case 6:
{
lean_object* v_binderName_91_; lean_object* v_binderType_92_; lean_object* v_body_93_; uint8_t v_binderInfo_94_; lean_object* v___x_95_; lean_object* v_fst_96_; lean_object* v_snd_97_; lean_object* v___x_98_; lean_object* v_fst_99_; lean_object* v_snd_100_; uint8_t v___y_102_; size_t v___x_109_; size_t v___x_110_; uint8_t v___x_111_; 
v_binderName_91_ = lean_ctor_get(v_e_58_, 0);
v_binderType_92_ = lean_ctor_get(v_e_58_, 1);
v_body_93_ = lean_ctor_get(v_e_58_, 2);
v_binderInfo_94_ = lean_ctor_get_uint8(v_e_58_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_92_);
lean_inc_ref(v_f_x3f_56_);
v___x_95_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_binderType_92_, v_a_59_);
v_fst_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_fst_96_);
v_snd_97_ = lean_ctor_get(v___x_95_, 1);
lean_inc(v_snd_97_);
lean_dec_ref(v___x_95_);
lean_inc_ref(v_body_93_);
v___x_98_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_body_93_, v_snd_97_);
v_fst_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_fst_99_);
v_snd_100_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_snd_100_);
lean_dec_ref(v___x_98_);
v___x_109_ = lean_ptr_addr(v_binderType_92_);
v___x_110_ = lean_ptr_addr(v_fst_96_);
v___x_111_ = lean_usize_dec_eq(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
v___y_102_ = v___x_111_;
goto v___jp_101_;
}
else
{
size_t v___x_112_; size_t v___x_113_; uint8_t v___x_114_; 
v___x_112_ = lean_ptr_addr(v_body_93_);
v___x_113_ = lean_ptr_addr(v_fst_99_);
v___x_114_ = lean_usize_dec_eq(v___x_112_, v___x_113_);
v___y_102_ = v___x_114_;
goto v___jp_101_;
}
v___jp_101_:
{
if (v___y_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_inc(v_binderName_91_);
v___x_103_ = l_Lean_Expr_lam___override(v_binderName_91_, v_fst_96_, v_fst_99_, v_binderInfo_94_);
v___x_104_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_103_, v_snd_100_);
return v___x_104_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_94_, v_binderInfo_94_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_inc(v_binderName_91_);
v___x_106_ = l_Lean_Expr_lam___override(v_binderName_91_, v_fst_96_, v_fst_99_, v_binderInfo_94_);
v___x_107_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_106_, v_snd_100_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; 
lean_dec(v_fst_99_);
lean_dec(v_fst_96_);
lean_inc_ref(v_e_58_);
v___x_108_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_snd_100_);
return v___x_108_;
}
}
}
}
case 10:
{
lean_object* v_data_115_; lean_object* v_expr_116_; lean_object* v___x_117_; lean_object* v_fst_118_; lean_object* v_snd_119_; size_t v___x_120_; size_t v___x_121_; uint8_t v___x_122_; 
v_data_115_ = lean_ctor_get(v_e_58_, 0);
v_expr_116_ = lean_ctor_get(v_e_58_, 1);
lean_inc_ref(v_expr_116_);
v___x_117_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_expr_116_, v_a_59_);
v_fst_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_fst_118_);
v_snd_119_ = lean_ctor_get(v___x_117_, 1);
lean_inc(v_snd_119_);
lean_dec_ref(v___x_117_);
v___x_120_ = lean_ptr_addr(v_expr_116_);
v___x_121_ = lean_ptr_addr(v_fst_118_);
v___x_122_ = lean_usize_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_inc(v_data_115_);
v___x_123_ = l_Lean_Expr_mdata___override(v_data_115_, v_fst_118_);
v___x_124_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_123_, v_snd_119_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
lean_dec(v_fst_118_);
lean_inc_ref(v_e_58_);
v___x_125_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_snd_119_);
return v___x_125_;
}
}
case 8:
{
lean_object* v_declName_126_; lean_object* v_type_127_; lean_object* v_value_128_; lean_object* v_body_129_; uint8_t v_nondep_130_; lean_object* v___x_131_; lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v___x_134_; lean_object* v_fst_135_; lean_object* v_snd_136_; lean_object* v___x_137_; lean_object* v_fst_138_; lean_object* v_snd_139_; uint8_t v___y_141_; size_t v___x_150_; size_t v___x_151_; uint8_t v___x_152_; 
v_declName_126_ = lean_ctor_get(v_e_58_, 0);
v_type_127_ = lean_ctor_get(v_e_58_, 1);
v_value_128_ = lean_ctor_get(v_e_58_, 2);
v_body_129_ = lean_ctor_get(v_e_58_, 3);
v_nondep_130_ = lean_ctor_get_uint8(v_e_58_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_127_);
lean_inc_ref_n(v_f_x3f_56_, 2);
v___x_131_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_type_127_, v_a_59_);
v_fst_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_fst_132_);
v_snd_133_ = lean_ctor_get(v___x_131_, 1);
lean_inc(v_snd_133_);
lean_dec_ref(v___x_131_);
lean_inc_ref(v_value_128_);
v___x_134_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_value_128_, v_snd_133_);
v_fst_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_fst_135_);
v_snd_136_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_snd_136_);
lean_dec_ref(v___x_134_);
lean_inc_ref(v_body_129_);
v___x_137_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_body_129_, v_snd_136_);
v_fst_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_fst_138_);
v_snd_139_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_snd_139_);
lean_dec_ref(v___x_137_);
v___x_150_ = lean_ptr_addr(v_type_127_);
v___x_151_ = lean_ptr_addr(v_fst_132_);
v___x_152_ = lean_usize_dec_eq(v___x_150_, v___x_151_);
if (v___x_152_ == 0)
{
v___y_141_ = v___x_152_;
goto v___jp_140_;
}
else
{
size_t v___x_153_; size_t v___x_154_; uint8_t v___x_155_; 
v___x_153_ = lean_ptr_addr(v_value_128_);
v___x_154_ = lean_ptr_addr(v_fst_135_);
v___x_155_ = lean_usize_dec_eq(v___x_153_, v___x_154_);
v___y_141_ = v___x_155_;
goto v___jp_140_;
}
v___jp_140_:
{
if (v___y_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_inc(v_declName_126_);
v___x_142_ = l_Lean_Expr_letE___override(v_declName_126_, v_fst_132_, v_fst_135_, v_fst_138_, v_nondep_130_);
v___x_143_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_142_, v_snd_139_);
return v___x_143_;
}
else
{
size_t v___x_144_; size_t v___x_145_; uint8_t v___x_146_; 
v___x_144_ = lean_ptr_addr(v_body_129_);
v___x_145_ = lean_ptr_addr(v_fst_138_);
v___x_146_ = lean_usize_dec_eq(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_inc(v_declName_126_);
v___x_147_ = l_Lean_Expr_letE___override(v_declName_126_, v_fst_132_, v_fst_135_, v_fst_138_, v_nondep_130_);
v___x_148_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_147_, v_snd_139_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; 
lean_dec(v_fst_138_);
lean_dec(v_fst_135_);
lean_dec(v_fst_132_);
lean_inc_ref(v_e_58_);
v___x_149_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_snd_139_);
return v___x_149_;
}
}
}
}
case 5:
{
lean_object* v_fn_156_; lean_object* v_arg_157_; lean_object* v___x_158_; lean_object* v_fst_159_; lean_object* v_snd_160_; lean_object* v___x_161_; lean_object* v_fst_162_; lean_object* v_snd_163_; uint8_t v___y_165_; size_t v___x_169_; size_t v___x_170_; uint8_t v___x_171_; 
v_fn_156_ = lean_ctor_get(v_e_58_, 0);
v_arg_157_ = lean_ctor_get(v_e_58_, 1);
lean_inc_ref(v_fn_156_);
lean_inc_ref(v_f_x3f_56_);
v___x_158_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_fn_156_, v_a_59_);
v_fst_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_fst_159_);
v_snd_160_ = lean_ctor_get(v___x_158_, 1);
lean_inc(v_snd_160_);
lean_dec_ref(v___x_158_);
lean_inc_ref(v_arg_157_);
v___x_161_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_arg_157_, v_snd_160_);
v_fst_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_fst_162_);
v_snd_163_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_snd_163_);
lean_dec_ref(v___x_161_);
v___x_169_ = lean_ptr_addr(v_fn_156_);
v___x_170_ = lean_ptr_addr(v_fst_159_);
v___x_171_ = lean_usize_dec_eq(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
v___y_165_ = v___x_171_;
goto v___jp_164_;
}
else
{
size_t v___x_172_; size_t v___x_173_; uint8_t v___x_174_; 
v___x_172_ = lean_ptr_addr(v_arg_157_);
v___x_173_ = lean_ptr_addr(v_fst_162_);
v___x_174_ = lean_usize_dec_eq(v___x_172_, v___x_173_);
v___y_165_ = v___x_174_;
goto v___jp_164_;
}
v___jp_164_:
{
if (v___y_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = l_Lean_Expr_app___override(v_fst_159_, v_fst_162_);
v___x_167_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_166_, v_snd_163_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
lean_dec(v_fst_162_);
lean_dec(v_fst_159_);
lean_inc_ref(v_e_58_);
v___x_168_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_snd_163_);
return v___x_168_;
}
}
}
case 11:
{
lean_object* v_typeName_175_; lean_object* v_idx_176_; lean_object* v_struct_177_; lean_object* v___x_178_; lean_object* v_fst_179_; lean_object* v_snd_180_; size_t v___x_181_; size_t v___x_182_; uint8_t v___x_183_; 
v_typeName_175_ = lean_ctor_get(v_e_58_, 0);
v_idx_176_ = lean_ctor_get(v_e_58_, 1);
v_struct_177_ = lean_ctor_get(v_e_58_, 2);
lean_inc_ref(v_struct_177_);
v___x_178_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_56_, v_size_57_, v_struct_177_, v_a_59_);
v_fst_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc(v_snd_180_);
lean_dec_ref(v___x_178_);
v___x_181_ = lean_ptr_addr(v_struct_177_);
v___x_182_ = lean_ptr_addr(v_fst_179_);
v___x_183_ = lean_usize_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_inc(v_idx_176_);
lean_inc(v_typeName_175_);
v___x_184_ = l_Lean_Expr_proj___override(v_typeName_175_, v_idx_176_, v_fst_179_);
v___x_185_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_184_, v_snd_180_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; 
lean_dec(v_fst_179_);
lean_inc_ref(v_e_58_);
v___x_186_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_snd_180_);
return v___x_186_;
}
}
case 3:
{
lean_object* v_u_187_; lean_object* v___x_188_; size_t v___x_189_; size_t v___x_190_; uint8_t v___x_191_; 
v_u_187_ = lean_ctor_get(v_e_58_, 0);
lean_inc(v_u_187_);
v___x_188_ = l_Lean_Level_replace(v_f_x3f_56_, v_u_187_);
v___x_189_ = lean_ptr_addr(v_u_187_);
v___x_190_ = lean_ptr_addr(v___x_188_);
v___x_191_ = lean_usize_dec_eq(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = l_Lean_Expr_sort___override(v___x_188_);
v___x_193_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_192_, v_a_59_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; 
lean_dec(v___x_188_);
lean_inc_ref(v_e_58_);
v___x_194_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_a_59_);
return v___x_194_;
}
}
case 4:
{
lean_object* v_declName_195_; lean_object* v_us_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_declName_195_ = lean_ctor_get(v_e_58_, 0);
v_us_196_ = lean_ctor_get(v_e_58_, 1);
v___x_197_ = lean_box(0);
lean_inc(v_us_196_);
v___x_198_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_56_, v_us_196_, v___x_197_);
v___x_199_ = l_ptrEqList___redArg(v_us_196_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_inc(v_declName_195_);
v___x_200_ = l_Lean_Expr_const___override(v_declName_195_, v___x_198_);
v___x_201_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v___x_200_, v_a_59_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
lean_dec(v___x_198_);
lean_inc_ref(v_e_58_);
v___x_202_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_63_, v_e_58_, v_e_58_, v_a_59_);
return v___x_202_;
}
}
default: 
{
lean_object* v___x_203_; 
lean_dec_ref(v_f_x3f_56_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_e_58_);
lean_ctor_set(v___x_203_, 1, v_a_59_);
return v___x_203_;
}
}
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref(v_e_58_);
lean_dec_ref(v_f_x3f_56_);
v___x_204_ = lean_array_uget(v_results_61_, v___x_63_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_a_59_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* v_f_x3f_206_, lean_object* v_size_207_, lean_object* v_e_208_, lean_object* v_a_209_){
_start:
{
size_t v_size_boxed_210_; lean_object* v_res_211_; 
v_size_boxed_210_ = lean_unbox_usize(v_size_207_);
lean_dec(v_size_207_);
v_res_211_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_206_, v_size_boxed_210_, v_e_208_, v_a_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* v_f_x3f_212_, size_t v_size_213_, lean_object* v_e_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_212_, v_size_213_, v_e_214_, v_a_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object* v_f_x3f_217_, lean_object* v_size_218_, lean_object* v_e_219_, lean_object* v_a_220_){
_start:
{
size_t v_size_boxed_221_; lean_object* v_res_222_; 
v_size_boxed_221_ = lean_unbox_usize(v_size_218_);
lean_dec(v_size_218_);
v_res_222_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(v_f_x3f_217_, v_size_boxed_221_, v_e_219_, v_a_220_);
return v_res_222_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr));
v___x_227_ = lean_unsigned_to_nat(8191u);
v___x_228_ = lean_mk_array(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_box(0);
v___x_233_ = ((lean_object*)(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2));
v___x_234_ = l_Lean_Expr_const___override(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3);
v___x_236_ = lean_unsigned_to_nat(8191u);
v___x_237_ = lean_mk_array(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4);
v___x_239_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* v_f_x3f_242_, lean_object* v_e_243_){
_start:
{
size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_fst_247_; 
v___x_244_ = ((size_t)8191ULL);
v___x_245_ = l_Lean_Expr_ReplaceLevelImpl_initCache;
v___x_246_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_242_, v___x_244_, v_e_243_, v___x_245_);
v_fst_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_fst_247_);
lean_dec_ref(v___x_246_);
return v_fst_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object* v_f_x3f_248_, lean_object* v_x_249_){
_start:
{
switch(lean_obj_tag(v_x_249_))
{
case 7:
{
lean_object* v_binderName_250_; lean_object* v_binderType_251_; lean_object* v_body_252_; uint8_t v_binderInfo_253_; lean_object* v_d_254_; lean_object* v_b_255_; uint8_t v___y_257_; size_t v___x_261_; size_t v___x_262_; uint8_t v___x_263_; 
v_binderName_250_ = lean_ctor_get(v_x_249_, 0);
v_binderType_251_ = lean_ctor_get(v_x_249_, 1);
v_body_252_ = lean_ctor_get(v_x_249_, 2);
v_binderInfo_253_ = lean_ctor_get_uint8(v_x_249_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_251_);
lean_inc_ref(v_f_x3f_248_);
v_d_254_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_binderType_251_);
lean_inc_ref(v_body_252_);
v_b_255_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_body_252_);
v___x_261_ = lean_ptr_addr(v_binderType_251_);
v___x_262_ = lean_ptr_addr(v_d_254_);
v___x_263_ = lean_usize_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
v___y_257_ = v___x_263_;
goto v___jp_256_;
}
else
{
size_t v___x_264_; size_t v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_ptr_addr(v_body_252_);
v___x_265_ = lean_ptr_addr(v_b_255_);
v___x_266_ = lean_usize_dec_eq(v___x_264_, v___x_265_);
v___y_257_ = v___x_266_;
goto v___jp_256_;
}
v___jp_256_:
{
if (v___y_257_ == 0)
{
lean_object* v___x_258_; 
lean_inc(v_binderName_250_);
lean_dec_ref_known(v_x_249_, 3);
v___x_258_ = l_Lean_Expr_forallE___override(v_binderName_250_, v_d_254_, v_b_255_, v_binderInfo_253_);
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_253_, v_binderInfo_253_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_inc(v_binderName_250_);
lean_dec_ref_known(v_x_249_, 3);
v___x_260_ = l_Lean_Expr_forallE___override(v_binderName_250_, v_d_254_, v_b_255_, v_binderInfo_253_);
return v___x_260_;
}
else
{
lean_dec_ref(v_b_255_);
lean_dec_ref(v_d_254_);
return v_x_249_;
}
}
}
}
case 6:
{
lean_object* v_binderName_267_; lean_object* v_binderType_268_; lean_object* v_body_269_; uint8_t v_binderInfo_270_; lean_object* v_d_271_; lean_object* v_b_272_; uint8_t v___y_274_; size_t v___x_278_; size_t v___x_279_; uint8_t v___x_280_; 
v_binderName_267_ = lean_ctor_get(v_x_249_, 0);
v_binderType_268_ = lean_ctor_get(v_x_249_, 1);
v_body_269_ = lean_ctor_get(v_x_249_, 2);
v_binderInfo_270_ = lean_ctor_get_uint8(v_x_249_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_268_);
lean_inc_ref(v_f_x3f_248_);
v_d_271_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_binderType_268_);
lean_inc_ref(v_body_269_);
v_b_272_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_body_269_);
v___x_278_ = lean_ptr_addr(v_binderType_268_);
v___x_279_ = lean_ptr_addr(v_d_271_);
v___x_280_ = lean_usize_dec_eq(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
v___y_274_ = v___x_280_;
goto v___jp_273_;
}
else
{
size_t v___x_281_; size_t v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_ptr_addr(v_body_269_);
v___x_282_ = lean_ptr_addr(v_b_272_);
v___x_283_ = lean_usize_dec_eq(v___x_281_, v___x_282_);
v___y_274_ = v___x_283_;
goto v___jp_273_;
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
lean_object* v___x_275_; 
lean_inc(v_binderName_267_);
lean_dec_ref_known(v_x_249_, 3);
v___x_275_ = l_Lean_Expr_lam___override(v_binderName_267_, v_d_271_, v_b_272_, v_binderInfo_270_);
return v___x_275_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_270_, v_binderInfo_270_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_inc(v_binderName_267_);
lean_dec_ref_known(v_x_249_, 3);
v___x_277_ = l_Lean_Expr_lam___override(v_binderName_267_, v_d_271_, v_b_272_, v_binderInfo_270_);
return v___x_277_;
}
else
{
lean_dec_ref(v_b_272_);
lean_dec_ref(v_d_271_);
return v_x_249_;
}
}
}
}
case 10:
{
lean_object* v_data_284_; lean_object* v_expr_285_; lean_object* v_b_286_; size_t v___x_287_; size_t v___x_288_; uint8_t v___x_289_; 
v_data_284_ = lean_ctor_get(v_x_249_, 0);
v_expr_285_ = lean_ctor_get(v_x_249_, 1);
lean_inc_ref(v_expr_285_);
v_b_286_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_expr_285_);
v___x_287_ = lean_ptr_addr(v_expr_285_);
v___x_288_ = lean_ptr_addr(v_b_286_);
v___x_289_ = lean_usize_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_inc(v_data_284_);
lean_dec_ref_known(v_x_249_, 2);
v___x_290_ = l_Lean_Expr_mdata___override(v_data_284_, v_b_286_);
return v___x_290_;
}
else
{
lean_dec_ref(v_b_286_);
return v_x_249_;
}
}
case 8:
{
lean_object* v_declName_291_; lean_object* v_type_292_; lean_object* v_value_293_; lean_object* v_body_294_; uint8_t v_nondep_295_; lean_object* v_t_296_; lean_object* v_v_297_; lean_object* v_b_298_; uint8_t v___y_300_; size_t v___x_306_; size_t v___x_307_; uint8_t v___x_308_; 
v_declName_291_ = lean_ctor_get(v_x_249_, 0);
v_type_292_ = lean_ctor_get(v_x_249_, 1);
v_value_293_ = lean_ctor_get(v_x_249_, 2);
v_body_294_ = lean_ctor_get(v_x_249_, 3);
v_nondep_295_ = lean_ctor_get_uint8(v_x_249_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_292_);
lean_inc_ref_n(v_f_x3f_248_, 2);
v_t_296_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_type_292_);
lean_inc_ref(v_value_293_);
v_v_297_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_value_293_);
lean_inc_ref(v_body_294_);
v_b_298_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_body_294_);
v___x_306_ = lean_ptr_addr(v_type_292_);
v___x_307_ = lean_ptr_addr(v_t_296_);
v___x_308_ = lean_usize_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
v___y_300_ = v___x_308_;
goto v___jp_299_;
}
else
{
size_t v___x_309_; size_t v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_ptr_addr(v_value_293_);
v___x_310_ = lean_ptr_addr(v_v_297_);
v___x_311_ = lean_usize_dec_eq(v___x_309_, v___x_310_);
v___y_300_ = v___x_311_;
goto v___jp_299_;
}
v___jp_299_:
{
if (v___y_300_ == 0)
{
lean_object* v___x_301_; 
lean_inc(v_declName_291_);
lean_dec_ref_known(v_x_249_, 4);
v___x_301_ = l_Lean_Expr_letE___override(v_declName_291_, v_t_296_, v_v_297_, v_b_298_, v_nondep_295_);
return v___x_301_;
}
else
{
size_t v___x_302_; size_t v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_ptr_addr(v_body_294_);
v___x_303_ = lean_ptr_addr(v_b_298_);
v___x_304_ = lean_usize_dec_eq(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_inc(v_declName_291_);
lean_dec_ref_known(v_x_249_, 4);
v___x_305_ = l_Lean_Expr_letE___override(v_declName_291_, v_t_296_, v_v_297_, v_b_298_, v_nondep_295_);
return v___x_305_;
}
else
{
lean_dec_ref(v_b_298_);
lean_dec_ref(v_v_297_);
lean_dec_ref(v_t_296_);
return v_x_249_;
}
}
}
}
case 5:
{
lean_object* v_fn_312_; lean_object* v_arg_313_; lean_object* v_f_314_; lean_object* v_a_315_; uint8_t v___y_317_; size_t v___x_319_; size_t v___x_320_; uint8_t v___x_321_; 
v_fn_312_ = lean_ctor_get(v_x_249_, 0);
v_arg_313_ = lean_ctor_get(v_x_249_, 1);
lean_inc_ref(v_fn_312_);
lean_inc_ref(v_f_x3f_248_);
v_f_314_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_fn_312_);
lean_inc_ref(v_arg_313_);
v_a_315_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_arg_313_);
v___x_319_ = lean_ptr_addr(v_fn_312_);
v___x_320_ = lean_ptr_addr(v_f_314_);
v___x_321_ = lean_usize_dec_eq(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
v___y_317_ = v___x_321_;
goto v___jp_316_;
}
else
{
size_t v___x_322_; size_t v___x_323_; uint8_t v___x_324_; 
v___x_322_ = lean_ptr_addr(v_arg_313_);
v___x_323_ = lean_ptr_addr(v_a_315_);
v___x_324_ = lean_usize_dec_eq(v___x_322_, v___x_323_);
v___y_317_ = v___x_324_;
goto v___jp_316_;
}
v___jp_316_:
{
if (v___y_317_ == 0)
{
lean_object* v___x_318_; 
lean_dec_ref_known(v_x_249_, 2);
v___x_318_ = l_Lean_Expr_app___override(v_f_314_, v_a_315_);
return v___x_318_;
}
else
{
lean_dec_ref(v_a_315_);
lean_dec_ref(v_f_314_);
return v_x_249_;
}
}
}
case 11:
{
lean_object* v_typeName_325_; lean_object* v_idx_326_; lean_object* v_struct_327_; lean_object* v_b_328_; size_t v___x_329_; size_t v___x_330_; uint8_t v___x_331_; 
v_typeName_325_ = lean_ctor_get(v_x_249_, 0);
v_idx_326_ = lean_ctor_get(v_x_249_, 1);
v_struct_327_ = lean_ctor_get(v_x_249_, 2);
lean_inc_ref(v_struct_327_);
v_b_328_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_248_, v_struct_327_);
v___x_329_ = lean_ptr_addr(v_struct_327_);
v___x_330_ = lean_ptr_addr(v_b_328_);
v___x_331_ = lean_usize_dec_eq(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_inc(v_idx_326_);
lean_inc(v_typeName_325_);
lean_dec_ref_known(v_x_249_, 3);
v___x_332_ = l_Lean_Expr_proj___override(v_typeName_325_, v_idx_326_, v_b_328_);
return v___x_332_;
}
else
{
lean_dec_ref(v_b_328_);
return v_x_249_;
}
}
case 3:
{
lean_object* v_u_333_; lean_object* v___x_334_; size_t v___x_335_; size_t v___x_336_; uint8_t v___x_337_; 
v_u_333_ = lean_ctor_get(v_x_249_, 0);
lean_inc(v_u_333_);
v___x_334_ = l_Lean_Level_replace(v_f_x3f_248_, v_u_333_);
v___x_335_ = lean_ptr_addr(v_u_333_);
v___x_336_ = lean_ptr_addr(v___x_334_);
v___x_337_ = lean_usize_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_dec_ref_known(v_x_249_, 1);
v___x_338_ = l_Lean_Expr_sort___override(v___x_334_);
return v___x_338_;
}
else
{
lean_dec(v___x_334_);
return v_x_249_;
}
}
case 4:
{
lean_object* v_declName_339_; lean_object* v_us_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_declName_339_ = lean_ctor_get(v_x_249_, 0);
v_us_340_ = lean_ctor_get(v_x_249_, 1);
v___x_341_ = lean_box(0);
lean_inc(v_us_340_);
v___x_342_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_248_, v_us_340_, v___x_341_);
v___x_343_ = l_ptrEqList___redArg(v_us_340_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_inc(v_declName_339_);
lean_dec_ref_known(v_x_249_, 2);
v___x_344_ = l_Lean_Expr_const___override(v_declName_339_, v___x_342_);
return v___x_344_;
}
else
{
lean_dec(v___x_342_);
return v_x_249_;
}
}
default: 
{
lean_dec_ref(v_f_x3f_248_);
return v_x_249_;
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
