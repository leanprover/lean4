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
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t v_i_19_, lean_object* v_key_20_, lean_object* v_result_21_, lean_object* v_a_22_){
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
LEAN_EXPORT void l_Lean_Expr_ReplaceLevelImpl_cache_0interp(lean_interpreter_value* stack)
{
size_t v_i_19_ = stack[0].m_num;
lean_object* v_key_20_ = stack[1].m_obj;
lean_object* v_result_21_ = stack[2].m_obj;
lean_object* v_a_22_ = stack[3].m_obj;
lean_object* v_res_35_;
v_res_35_ = l_Lean_Expr_ReplaceLevelImpl_cache(v_i_19_, v_key_20_, v_result_21_, v_a_22_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* v_i_36_, lean_object* v_key_37_, lean_object* v_result_38_, lean_object* v_a_39_){
_start:
{
size_t v_i_boxed_40_; lean_object* v_res_41_; 
v_i_boxed_40_ = lean_unbox_usize(v_i_36_);
lean_dec(v_i_36_);
v_res_41_ = l_Lean_Expr_ReplaceLevelImpl_cache(v_i_boxed_40_, v_key_37_, v_result_38_, v_a_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object* v_f_x3f_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
if (lean_obj_tag(v_a_43_) == 0)
{
lean_object* v___x_45_; 
lean_dec_ref(v_f_x3f_42_);
v___x_45_ = l_List_reverse___redArg(v_a_44_);
return v___x_45_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_56_; 
v_head_46_ = lean_ctor_get(v_a_43_, 0);
v_tail_47_ = lean_ctor_get(v_a_43_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v_a_43_);
if (v_isSharedCheck_56_ == 0)
{
v___x_49_ = v_a_43_;
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_tail_47_);
lean_inc(v_head_46_);
lean_dec(v_a_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
lean_inc_ref(v_f_x3f_42_);
v___x_51_ = l_Lean_Level_replace(v_f_x3f_42_, v_head_46_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 1, v_a_44_);
lean_ctor_set(v___x_49_, 0, v___x_51_);
v___x_53_ = v___x_49_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_a_44_);
v___x_53_ = v_reuseFailAlloc_55_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
v_a_43_ = v_tail_47_;
v_a_44_ = v___x_53_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* v_f_x3f_57_, size_t v_size_58_, lean_object* v_e_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_keys_61_; lean_object* v_results_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; size_t v___x_66_; uint8_t v___x_67_; 
v_keys_61_ = lean_ctor_get(v_a_60_, 0);
v_results_62_ = lean_ctor_get(v_a_60_, 1);
v___x_63_ = lean_ptr_addr(v_e_59_);
v___x_64_ = lean_usize_mod(v___x_63_, v_size_58_);
v___x_65_ = lean_array_uget_borrowed(v_keys_61_, v___x_64_);
v___x_66_ = lean_ptr_addr(v___x_65_);
v___x_67_ = lean_usize_dec_eq(v___x_66_, v___x_63_);
if (v___x_67_ == 0)
{
switch(lean_obj_tag(v_e_59_))
{
case 7:
{
lean_object* v_binderName_68_; lean_object* v_binderType_69_; lean_object* v_body_70_; uint8_t v_binderInfo_71_; lean_object* v___x_72_; lean_object* v_fst_73_; lean_object* v_snd_74_; lean_object* v___x_75_; lean_object* v_fst_76_; lean_object* v_snd_77_; size_t v___x_78_; size_t v___x_79_; uint8_t v___x_80_; 
v_binderName_68_ = lean_ctor_get(v_e_59_, 0);
v_binderType_69_ = lean_ctor_get(v_e_59_, 1);
v_body_70_ = lean_ctor_get(v_e_59_, 2);
v_binderInfo_71_ = lean_ctor_get_uint8(v_e_59_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_69_);
lean_inc_ref(v_f_x3f_57_);
v___x_72_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_binderType_69_, v_a_60_);
v_fst_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_fst_73_);
v_snd_74_ = lean_ctor_get(v___x_72_, 1);
lean_inc(v_snd_74_);
lean_dec_ref(v___x_72_);
lean_inc_ref(v_body_70_);
v___x_75_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_body_70_, v_snd_74_);
v_fst_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_fst_76_);
v_snd_77_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_snd_77_);
lean_dec_ref(v___x_75_);
v___x_78_ = lean_ptr_addr(v_binderType_69_);
v___x_79_ = lean_ptr_addr(v_fst_73_);
v___x_80_ = lean_usize_dec_eq(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_inc(v_binderName_68_);
v___x_81_ = l_Lean_Expr_forallE___override(v_binderName_68_, v_fst_73_, v_fst_76_, v_binderInfo_71_);
v___x_82_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_81_, v_snd_77_);
return v___x_82_;
}
else
{
size_t v___x_83_; size_t v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_ptr_addr(v_body_70_);
v___x_84_ = lean_ptr_addr(v_fst_76_);
v___x_85_ = lean_usize_dec_eq(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_inc(v_binderName_68_);
v___x_86_ = l_Lean_Expr_forallE___override(v_binderName_68_, v_fst_73_, v_fst_76_, v_binderInfo_71_);
v___x_87_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_86_, v_snd_77_);
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_71_, v_binderInfo_71_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_inc(v_binderName_68_);
v___x_89_ = l_Lean_Expr_forallE___override(v_binderName_68_, v_fst_73_, v_fst_76_, v_binderInfo_71_);
v___x_90_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_89_, v_snd_77_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_dec(v_fst_76_);
lean_dec(v_fst_73_);
lean_inc_ref(v_e_59_);
v___x_91_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_snd_77_);
return v___x_91_;
}
}
}
}
case 6:
{
lean_object* v_binderName_92_; lean_object* v_binderType_93_; lean_object* v_body_94_; uint8_t v_binderInfo_95_; lean_object* v___x_96_; lean_object* v_fst_97_; lean_object* v_snd_98_; lean_object* v___x_99_; lean_object* v_fst_100_; lean_object* v_snd_101_; size_t v___x_102_; size_t v___x_103_; uint8_t v___x_104_; 
v_binderName_92_ = lean_ctor_get(v_e_59_, 0);
v_binderType_93_ = lean_ctor_get(v_e_59_, 1);
v_body_94_ = lean_ctor_get(v_e_59_, 2);
v_binderInfo_95_ = lean_ctor_get_uint8(v_e_59_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_93_);
lean_inc_ref(v_f_x3f_57_);
v___x_96_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_binderType_93_, v_a_60_);
v_fst_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_fst_97_);
v_snd_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_snd_98_);
lean_dec_ref(v___x_96_);
lean_inc_ref(v_body_94_);
v___x_99_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_body_94_, v_snd_98_);
v_fst_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_fst_100_);
v_snd_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_snd_101_);
lean_dec_ref(v___x_99_);
v___x_102_ = lean_ptr_addr(v_binderType_93_);
v___x_103_ = lean_ptr_addr(v_fst_97_);
v___x_104_ = lean_usize_dec_eq(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_inc(v_binderName_92_);
v___x_105_ = l_Lean_Expr_lam___override(v_binderName_92_, v_fst_97_, v_fst_100_, v_binderInfo_95_);
v___x_106_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_105_, v_snd_101_);
return v___x_106_;
}
else
{
size_t v___x_107_; size_t v___x_108_; uint8_t v___x_109_; 
v___x_107_ = lean_ptr_addr(v_body_94_);
v___x_108_ = lean_ptr_addr(v_fst_100_);
v___x_109_ = lean_usize_dec_eq(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_inc(v_binderName_92_);
v___x_110_ = l_Lean_Expr_lam___override(v_binderName_92_, v_fst_97_, v_fst_100_, v_binderInfo_95_);
v___x_111_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_110_, v_snd_101_);
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
v___x_112_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_95_, v_binderInfo_95_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_inc(v_binderName_92_);
v___x_113_ = l_Lean_Expr_lam___override(v_binderName_92_, v_fst_97_, v_fst_100_, v_binderInfo_95_);
v___x_114_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_113_, v_snd_101_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; 
lean_dec(v_fst_100_);
lean_dec(v_fst_97_);
lean_inc_ref(v_e_59_);
v___x_115_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_snd_101_);
return v___x_115_;
}
}
}
}
case 10:
{
lean_object* v_data_116_; lean_object* v_expr_117_; lean_object* v___x_118_; lean_object* v_fst_119_; lean_object* v_snd_120_; size_t v___x_121_; size_t v___x_122_; uint8_t v___x_123_; 
v_data_116_ = lean_ctor_get(v_e_59_, 0);
v_expr_117_ = lean_ctor_get(v_e_59_, 1);
lean_inc_ref(v_expr_117_);
v___x_118_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_expr_117_, v_a_60_);
v_fst_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_fst_119_);
v_snd_120_ = lean_ctor_get(v___x_118_, 1);
lean_inc(v_snd_120_);
lean_dec_ref(v___x_118_);
v___x_121_ = lean_ptr_addr(v_expr_117_);
v___x_122_ = lean_ptr_addr(v_fst_119_);
v___x_123_ = lean_usize_dec_eq(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_inc(v_data_116_);
v___x_124_ = l_Lean_Expr_mdata___override(v_data_116_, v_fst_119_);
v___x_125_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_124_, v_snd_120_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; 
lean_dec(v_fst_119_);
lean_inc_ref(v_e_59_);
v___x_126_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_snd_120_);
return v___x_126_;
}
}
case 8:
{
lean_object* v_declName_127_; lean_object* v_type_128_; lean_object* v_value_129_; lean_object* v_body_130_; uint8_t v_nondep_131_; lean_object* v___x_132_; lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v___x_135_; lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_138_; lean_object* v_fst_139_; lean_object* v_snd_140_; size_t v___x_141_; size_t v___x_142_; uint8_t v___x_143_; 
v_declName_127_ = lean_ctor_get(v_e_59_, 0);
v_type_128_ = lean_ctor_get(v_e_59_, 1);
v_value_129_ = lean_ctor_get(v_e_59_, 2);
v_body_130_ = lean_ctor_get(v_e_59_, 3);
v_nondep_131_ = lean_ctor_get_uint8(v_e_59_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_128_);
lean_inc_ref_n(v_f_x3f_57_, 2);
v___x_132_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_type_128_, v_a_60_);
v_fst_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_fst_133_);
v_snd_134_ = lean_ctor_get(v___x_132_, 1);
lean_inc(v_snd_134_);
lean_dec_ref(v___x_132_);
lean_inc_ref(v_value_129_);
v___x_135_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_value_129_, v_snd_134_);
v_fst_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_fst_136_);
v_snd_137_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_snd_137_);
lean_dec_ref(v___x_135_);
lean_inc_ref(v_body_130_);
v___x_138_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_body_130_, v_snd_137_);
v_fst_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_fst_139_);
v_snd_140_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_snd_140_);
lean_dec_ref(v___x_138_);
v___x_141_ = lean_ptr_addr(v_type_128_);
v___x_142_ = lean_ptr_addr(v_fst_133_);
v___x_143_ = lean_usize_dec_eq(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_inc(v_declName_127_);
v___x_144_ = l_Lean_Expr_letE___override(v_declName_127_, v_fst_133_, v_fst_136_, v_fst_139_, v_nondep_131_);
v___x_145_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_144_, v_snd_140_);
return v___x_145_;
}
else
{
size_t v___x_146_; size_t v___x_147_; uint8_t v___x_148_; 
v___x_146_ = lean_ptr_addr(v_value_129_);
v___x_147_ = lean_ptr_addr(v_fst_136_);
v___x_148_ = lean_usize_dec_eq(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc(v_declName_127_);
v___x_149_ = l_Lean_Expr_letE___override(v_declName_127_, v_fst_133_, v_fst_136_, v_fst_139_, v_nondep_131_);
v___x_150_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_149_, v_snd_140_);
return v___x_150_;
}
else
{
size_t v___x_151_; size_t v___x_152_; uint8_t v___x_153_; 
v___x_151_ = lean_ptr_addr(v_body_130_);
v___x_152_ = lean_ptr_addr(v_fst_139_);
v___x_153_ = lean_usize_dec_eq(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_inc(v_declName_127_);
v___x_154_ = l_Lean_Expr_letE___override(v_declName_127_, v_fst_133_, v_fst_136_, v_fst_139_, v_nondep_131_);
v___x_155_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_154_, v_snd_140_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; 
lean_dec(v_fst_139_);
lean_dec(v_fst_136_);
lean_dec(v_fst_133_);
lean_inc_ref(v_e_59_);
v___x_156_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_snd_140_);
return v___x_156_;
}
}
}
}
case 5:
{
lean_object* v_fn_157_; lean_object* v_arg_158_; lean_object* v___x_159_; lean_object* v_fst_160_; lean_object* v_snd_161_; lean_object* v___x_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; size_t v___x_165_; size_t v___x_166_; uint8_t v___x_167_; 
v_fn_157_ = lean_ctor_get(v_e_59_, 0);
v_arg_158_ = lean_ctor_get(v_e_59_, 1);
lean_inc_ref(v_fn_157_);
lean_inc_ref(v_f_x3f_57_);
v___x_159_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_fn_157_, v_a_60_);
v_fst_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_fst_160_);
v_snd_161_ = lean_ctor_get(v___x_159_, 1);
lean_inc(v_snd_161_);
lean_dec_ref(v___x_159_);
lean_inc_ref(v_arg_158_);
v___x_162_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_arg_158_, v_snd_161_);
v_fst_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_fst_163_);
v_snd_164_ = lean_ctor_get(v___x_162_, 1);
lean_inc(v_snd_164_);
lean_dec_ref(v___x_162_);
v___x_165_ = lean_ptr_addr(v_fn_157_);
v___x_166_ = lean_ptr_addr(v_fst_160_);
v___x_167_ = lean_usize_dec_eq(v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = l_Lean_Expr_app___override(v_fst_160_, v_fst_163_);
v___x_169_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_168_, v_snd_164_);
return v___x_169_;
}
else
{
size_t v___x_170_; size_t v___x_171_; uint8_t v___x_172_; 
v___x_170_ = lean_ptr_addr(v_arg_158_);
v___x_171_ = lean_ptr_addr(v_fst_163_);
v___x_172_ = lean_usize_dec_eq(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l_Lean_Expr_app___override(v_fst_160_, v_fst_163_);
v___x_174_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_173_, v_snd_164_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; 
lean_dec(v_fst_163_);
lean_dec(v_fst_160_);
lean_inc_ref(v_e_59_);
v___x_175_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_snd_164_);
return v___x_175_;
}
}
}
case 11:
{
lean_object* v_typeName_176_; lean_object* v_idx_177_; lean_object* v_struct_178_; lean_object* v___x_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; size_t v___x_182_; size_t v___x_183_; uint8_t v___x_184_; 
v_typeName_176_ = lean_ctor_get(v_e_59_, 0);
v_idx_177_ = lean_ctor_get(v_e_59_, 1);
v_struct_178_ = lean_ctor_get(v_e_59_, 2);
lean_inc_ref(v_struct_178_);
v___x_179_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_struct_178_, v_a_60_);
v_fst_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_fst_180_);
v_snd_181_ = lean_ctor_get(v___x_179_, 1);
lean_inc(v_snd_181_);
lean_dec_ref(v___x_179_);
v___x_182_ = lean_ptr_addr(v_struct_178_);
v___x_183_ = lean_ptr_addr(v_fst_180_);
v___x_184_ = lean_usize_dec_eq(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_inc(v_idx_177_);
lean_inc(v_typeName_176_);
v___x_185_ = l_Lean_Expr_proj___override(v_typeName_176_, v_idx_177_, v_fst_180_);
v___x_186_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_185_, v_snd_181_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
lean_dec(v_fst_180_);
lean_inc_ref(v_e_59_);
v___x_187_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_snd_181_);
return v___x_187_;
}
}
case 3:
{
lean_object* v_u_188_; lean_object* v___x_189_; size_t v___x_190_; size_t v___x_191_; uint8_t v___x_192_; 
v_u_188_ = lean_ctor_get(v_e_59_, 0);
lean_inc(v_u_188_);
v___x_189_ = l_Lean_Level_replace(v_f_x3f_57_, v_u_188_);
v___x_190_ = lean_ptr_addr(v_u_188_);
v___x_191_ = lean_ptr_addr(v___x_189_);
v___x_192_ = lean_usize_dec_eq(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = l_Lean_Expr_sort___override(v___x_189_);
v___x_194_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_193_, v_a_60_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; 
lean_dec(v___x_189_);
lean_inc_ref(v_e_59_);
v___x_195_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_a_60_);
return v___x_195_;
}
}
case 4:
{
lean_object* v_declName_196_; lean_object* v_us_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_declName_196_ = lean_ctor_get(v_e_59_, 0);
v_us_197_ = lean_ctor_get(v_e_59_, 1);
v___x_198_ = lean_box(0);
lean_inc(v_us_197_);
v___x_199_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_57_, v_us_197_, v___x_198_);
v___x_200_ = l_ptrEqList___redArg(v_us_197_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_inc(v_declName_196_);
v___x_201_ = l_Lean_Expr_const___override(v_declName_196_, v___x_199_);
v___x_202_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v___x_201_, v_a_60_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
lean_dec(v___x_199_);
lean_inc_ref(v_e_59_);
v___x_203_ = l_Lean_Expr_ReplaceLevelImpl_cache(v___x_64_, v_e_59_, v_e_59_, v_a_60_);
return v___x_203_;
}
}
default: 
{
lean_object* v___x_204_; 
lean_dec_ref(v_f_x3f_57_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_e_59_);
lean_ctor_set(v___x_204_, 1, v_a_60_);
return v___x_204_;
}
}
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref(v_e_59_);
lean_dec_ref(v_f_x3f_57_);
v___x_205_ = lean_array_uget(v_results_62_, v___x_64_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_a_60_);
return v___x_206_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_x3f_57_ = stack[0].m_obj;
size_t v_size_58_ = stack[1].m_num;
lean_object* v_e_59_ = stack[2].m_obj;
lean_object* v_a_60_ = stack[3].m_obj;
lean_object* v_res_207_;
v_res_207_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_57_, v_size_58_, v_e_59_, v_a_60_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* v_f_x3f_208_, lean_object* v_size_209_, lean_object* v_e_210_, lean_object* v_a_211_){
_start:
{
size_t v_size_boxed_212_; lean_object* v_res_213_; 
v_size_boxed_212_ = lean_unbox_usize(v_size_209_);
lean_dec(v_size_209_);
v_res_213_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_208_, v_size_boxed_212_, v_e_210_, v_a_211_);
return v_res_213_;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* v_f_x3f_214_, size_t v_size_215_, lean_object* v_e_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_214_, v_size_215_, v_e_216_, v_a_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_x3f_214_ = stack[0].m_obj;
size_t v_size_215_ = stack[1].m_num;
lean_object* v_e_216_ = stack[2].m_obj;
lean_object* v_a_217_ = stack[3].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(v_f_x3f_214_, v_size_215_, v_e_216_, v_a_217_);
stack->m_obj
 = v_res_219_;
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
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr));
v___x_230_ = lean_unsigned_to_nat(8191u);
v___x_231_ = lean_mk_array(v___x_230_, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_box(0);
v___x_236_ = ((lean_object*)(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2));
v___x_237_ = l_Lean_Expr_const___override(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3);
v___x_239_ = lean_unsigned_to_nat(8191u);
v___x_240_ = lean_mk_array(v___x_239_, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4);
v___x_242_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* v_f_x3f_245_, lean_object* v_e_246_){
_start:
{
size_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_fst_250_; 
v___x_247_ = ((size_t)8191ULL);
v___x_248_ = l_Lean_Expr_ReplaceLevelImpl_initCache;
v___x_249_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_245_, v___x_247_, v_e_246_, v___x_248_);
v_fst_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_fst_250_);
lean_dec_ref(v___x_249_);
return v_fst_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object* v_f_x3f_251_, lean_object* v_x_252_){
_start:
{
switch(lean_obj_tag(v_x_252_))
{
case 7:
{
lean_object* v_binderName_253_; lean_object* v_binderType_254_; lean_object* v_body_255_; uint8_t v_binderInfo_256_; lean_object* v_d_257_; lean_object* v_b_258_; size_t v___x_259_; size_t v___x_260_; uint8_t v___x_261_; 
v_binderName_253_ = lean_ctor_get(v_x_252_, 0);
v_binderType_254_ = lean_ctor_get(v_x_252_, 1);
v_body_255_ = lean_ctor_get(v_x_252_, 2);
v_binderInfo_256_ = lean_ctor_get_uint8(v_x_252_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_254_);
lean_inc_ref(v_f_x3f_251_);
v_d_257_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_binderType_254_);
lean_inc_ref(v_body_255_);
v_b_258_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_body_255_);
v___x_259_ = lean_ptr_addr(v_binderType_254_);
v___x_260_ = lean_ptr_addr(v_d_257_);
v___x_261_ = lean_usize_dec_eq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_inc(v_binderName_253_);
lean_dec_ref_known(v_x_252_, 3);
v___x_262_ = l_Lean_Expr_forallE___override(v_binderName_253_, v_d_257_, v_b_258_, v_binderInfo_256_);
return v___x_262_;
}
else
{
size_t v___x_263_; size_t v___x_264_; uint8_t v___x_265_; 
v___x_263_ = lean_ptr_addr(v_body_255_);
v___x_264_ = lean_ptr_addr(v_b_258_);
v___x_265_ = lean_usize_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
lean_inc(v_binderName_253_);
lean_dec_ref_known(v_x_252_, 3);
v___x_266_ = l_Lean_Expr_forallE___override(v_binderName_253_, v_d_257_, v_b_258_, v_binderInfo_256_);
return v___x_266_;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_256_, v_binderInfo_256_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_inc(v_binderName_253_);
lean_dec_ref_known(v_x_252_, 3);
v___x_268_ = l_Lean_Expr_forallE___override(v_binderName_253_, v_d_257_, v_b_258_, v_binderInfo_256_);
return v___x_268_;
}
else
{
lean_dec_ref(v_b_258_);
lean_dec_ref(v_d_257_);
return v_x_252_;
}
}
}
}
case 6:
{
lean_object* v_binderName_269_; lean_object* v_binderType_270_; lean_object* v_body_271_; uint8_t v_binderInfo_272_; lean_object* v_d_273_; lean_object* v_b_274_; size_t v___x_275_; size_t v___x_276_; uint8_t v___x_277_; 
v_binderName_269_ = lean_ctor_get(v_x_252_, 0);
v_binderType_270_ = lean_ctor_get(v_x_252_, 1);
v_body_271_ = lean_ctor_get(v_x_252_, 2);
v_binderInfo_272_ = lean_ctor_get_uint8(v_x_252_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_270_);
lean_inc_ref(v_f_x3f_251_);
v_d_273_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_binderType_270_);
lean_inc_ref(v_body_271_);
v_b_274_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_body_271_);
v___x_275_ = lean_ptr_addr(v_binderType_270_);
v___x_276_ = lean_ptr_addr(v_d_273_);
v___x_277_ = lean_usize_dec_eq(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_inc(v_binderName_269_);
lean_dec_ref_known(v_x_252_, 3);
v___x_278_ = l_Lean_Expr_lam___override(v_binderName_269_, v_d_273_, v_b_274_, v_binderInfo_272_);
return v___x_278_;
}
else
{
size_t v___x_279_; size_t v___x_280_; uint8_t v___x_281_; 
v___x_279_ = lean_ptr_addr(v_body_271_);
v___x_280_ = lean_ptr_addr(v_b_274_);
v___x_281_ = lean_usize_dec_eq(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_inc(v_binderName_269_);
lean_dec_ref_known(v_x_252_, 3);
v___x_282_ = l_Lean_Expr_lam___override(v_binderName_269_, v_d_273_, v_b_274_, v_binderInfo_272_);
return v___x_282_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_272_, v_binderInfo_272_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_inc(v_binderName_269_);
lean_dec_ref_known(v_x_252_, 3);
v___x_284_ = l_Lean_Expr_lam___override(v_binderName_269_, v_d_273_, v_b_274_, v_binderInfo_272_);
return v___x_284_;
}
else
{
lean_dec_ref(v_b_274_);
lean_dec_ref(v_d_273_);
return v_x_252_;
}
}
}
}
case 10:
{
lean_object* v_data_285_; lean_object* v_expr_286_; lean_object* v_b_287_; size_t v___x_288_; size_t v___x_289_; uint8_t v___x_290_; 
v_data_285_ = lean_ctor_get(v_x_252_, 0);
v_expr_286_ = lean_ctor_get(v_x_252_, 1);
lean_inc_ref(v_expr_286_);
v_b_287_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_expr_286_);
v___x_288_ = lean_ptr_addr(v_expr_286_);
v___x_289_ = lean_ptr_addr(v_b_287_);
v___x_290_ = lean_usize_dec_eq(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
lean_inc(v_data_285_);
lean_dec_ref_known(v_x_252_, 2);
v___x_291_ = l_Lean_Expr_mdata___override(v_data_285_, v_b_287_);
return v___x_291_;
}
else
{
lean_dec_ref(v_b_287_);
return v_x_252_;
}
}
case 8:
{
lean_object* v_declName_292_; lean_object* v_type_293_; lean_object* v_value_294_; lean_object* v_body_295_; uint8_t v_nondep_296_; lean_object* v_t_297_; lean_object* v_v_298_; lean_object* v_b_299_; size_t v___x_300_; size_t v___x_301_; uint8_t v___x_302_; 
v_declName_292_ = lean_ctor_get(v_x_252_, 0);
v_type_293_ = lean_ctor_get(v_x_252_, 1);
v_value_294_ = lean_ctor_get(v_x_252_, 2);
v_body_295_ = lean_ctor_get(v_x_252_, 3);
v_nondep_296_ = lean_ctor_get_uint8(v_x_252_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_293_);
lean_inc_ref_n(v_f_x3f_251_, 2);
v_t_297_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_type_293_);
lean_inc_ref(v_value_294_);
v_v_298_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_value_294_);
lean_inc_ref(v_body_295_);
v_b_299_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_body_295_);
v___x_300_ = lean_ptr_addr(v_type_293_);
v___x_301_ = lean_ptr_addr(v_t_297_);
v___x_302_ = lean_usize_dec_eq(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_inc(v_declName_292_);
lean_dec_ref_known(v_x_252_, 4);
v___x_303_ = l_Lean_Expr_letE___override(v_declName_292_, v_t_297_, v_v_298_, v_b_299_, v_nondep_296_);
return v___x_303_;
}
else
{
size_t v___x_304_; size_t v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_ptr_addr(v_value_294_);
v___x_305_ = lean_ptr_addr(v_v_298_);
v___x_306_ = lean_usize_dec_eq(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_inc(v_declName_292_);
lean_dec_ref_known(v_x_252_, 4);
v___x_307_ = l_Lean_Expr_letE___override(v_declName_292_, v_t_297_, v_v_298_, v_b_299_, v_nondep_296_);
return v___x_307_;
}
else
{
size_t v___x_308_; size_t v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_ptr_addr(v_body_295_);
v___x_309_ = lean_ptr_addr(v_b_299_);
v___x_310_ = lean_usize_dec_eq(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_inc(v_declName_292_);
lean_dec_ref_known(v_x_252_, 4);
v___x_311_ = l_Lean_Expr_letE___override(v_declName_292_, v_t_297_, v_v_298_, v_b_299_, v_nondep_296_);
return v___x_311_;
}
else
{
lean_dec_ref(v_b_299_);
lean_dec_ref(v_v_298_);
lean_dec_ref(v_t_297_);
return v_x_252_;
}
}
}
}
case 5:
{
lean_object* v_fn_312_; lean_object* v_arg_313_; lean_object* v_f_314_; lean_object* v_a_315_; size_t v___x_316_; size_t v___x_317_; uint8_t v___x_318_; 
v_fn_312_ = lean_ctor_get(v_x_252_, 0);
v_arg_313_ = lean_ctor_get(v_x_252_, 1);
lean_inc_ref(v_fn_312_);
lean_inc_ref(v_f_x3f_251_);
v_f_314_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_fn_312_);
lean_inc_ref(v_arg_313_);
v_a_315_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_arg_313_);
v___x_316_ = lean_ptr_addr(v_fn_312_);
v___x_317_ = lean_ptr_addr(v_f_314_);
v___x_318_ = lean_usize_dec_eq(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
lean_dec_ref_known(v_x_252_, 2);
v___x_319_ = l_Lean_Expr_app___override(v_f_314_, v_a_315_);
return v___x_319_;
}
else
{
size_t v___x_320_; size_t v___x_321_; uint8_t v___x_322_; 
v___x_320_ = lean_ptr_addr(v_arg_313_);
v___x_321_ = lean_ptr_addr(v_a_315_);
v___x_322_ = lean_usize_dec_eq(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref_known(v_x_252_, 2);
v___x_323_ = l_Lean_Expr_app___override(v_f_314_, v_a_315_);
return v___x_323_;
}
else
{
lean_dec_ref(v_a_315_);
lean_dec_ref(v_f_314_);
return v_x_252_;
}
}
}
case 11:
{
lean_object* v_typeName_324_; lean_object* v_idx_325_; lean_object* v_struct_326_; lean_object* v_b_327_; size_t v___x_328_; size_t v___x_329_; uint8_t v___x_330_; 
v_typeName_324_ = lean_ctor_get(v_x_252_, 0);
v_idx_325_ = lean_ctor_get(v_x_252_, 1);
v_struct_326_ = lean_ctor_get(v_x_252_, 2);
lean_inc_ref(v_struct_326_);
v_b_327_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_251_, v_struct_326_);
v___x_328_ = lean_ptr_addr(v_struct_326_);
v___x_329_ = lean_ptr_addr(v_b_327_);
v___x_330_ = lean_usize_dec_eq(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_inc(v_idx_325_);
lean_inc(v_typeName_324_);
lean_dec_ref_known(v_x_252_, 3);
v___x_331_ = l_Lean_Expr_proj___override(v_typeName_324_, v_idx_325_, v_b_327_);
return v___x_331_;
}
else
{
lean_dec_ref(v_b_327_);
return v_x_252_;
}
}
case 3:
{
lean_object* v_u_332_; lean_object* v___x_333_; size_t v___x_334_; size_t v___x_335_; uint8_t v___x_336_; 
v_u_332_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_u_332_);
v___x_333_ = l_Lean_Level_replace(v_f_x3f_251_, v_u_332_);
v___x_334_ = lean_ptr_addr(v_u_332_);
v___x_335_ = lean_ptr_addr(v___x_333_);
v___x_336_ = lean_usize_dec_eq(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref_known(v_x_252_, 1);
v___x_337_ = l_Lean_Expr_sort___override(v___x_333_);
return v___x_337_;
}
else
{
lean_dec(v___x_333_);
return v_x_252_;
}
}
case 4:
{
lean_object* v_declName_338_; lean_object* v_us_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_declName_338_ = lean_ctor_get(v_x_252_, 0);
v_us_339_ = lean_ctor_get(v_x_252_, 1);
v___x_340_ = lean_box(0);
lean_inc(v_us_339_);
v___x_341_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_251_, v_us_339_, v___x_340_);
v___x_342_ = l_ptrEqList___redArg(v_us_339_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_inc(v_declName_338_);
lean_dec_ref_known(v_x_252_, 2);
v___x_343_ = l_Lean_Expr_const___override(v_declName_338_, v___x_341_);
return v___x_343_;
}
else
{
lean_dec(v___x_341_);
return v_x_252_;
}
}
default: 
{
lean_dec_ref(v_f_x3f_251_);
return v_x_252_;
}
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ReplaceLevel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
