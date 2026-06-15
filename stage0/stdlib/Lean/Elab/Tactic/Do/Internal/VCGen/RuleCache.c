// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Split public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction public import Lean.Elab.Tactic.Do.Internal.VCGen.Util
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSimpSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_cache_3_, lean_object* v_key_4_, lean_object* v_toPure_5_, lean_object* v_b_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc(v_b_6_);
v___x_7_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1_, v_inst_2_, v_cache_3_, v_key_4_, v_b_6_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_b_6_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
v___x_9_ = lean_apply_2(v_toPure_5_, lean_box(0), v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_cache_13_, lean_object* v_key_14_, lean_object* v_fallback_15_){
_start:
{
lean_object* v_toApplicative_16_; lean_object* v_toBind_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_30_; 
v_toApplicative_16_ = lean_ctor_get(v_inst_10_, 0);
v_toBind_17_ = lean_ctor_get(v_inst_10_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_inst_10_);
if (v_isSharedCheck_30_ == 0)
{
v___x_19_ = v_inst_10_;
v_isShared_20_ = v_isSharedCheck_30_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_toBind_17_);
lean_inc(v_toApplicative_16_);
lean_dec(v_inst_10_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_30_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v_toPure_21_; lean_object* v___x_22_; 
v_toPure_21_ = lean_ctor_get(v_toApplicative_16_, 1);
lean_inc(v_toPure_21_);
lean_dec_ref(v_toApplicative_16_);
lean_inc(v_key_14_);
lean_inc_ref(v_inst_12_);
lean_inc_ref(v_inst_11_);
v___x_22_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_11_, v_inst_12_, v_cache_13_, v_key_14_);
if (lean_obj_tag(v___x_22_) == 1)
{
lean_object* v_val_23_; lean_object* v___x_25_; 
lean_dec(v_toBind_17_);
lean_dec(v_fallback_15_);
lean_dec(v_key_14_);
lean_dec_ref(v_inst_12_);
lean_dec_ref(v_inst_11_);
v_val_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_val_23_);
lean_dec_ref_known(v___x_22_, 1);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v_cache_13_);
lean_ctor_set(v___x_19_, 0, v_val_23_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_val_23_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_cache_13_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; 
v___x_26_ = lean_apply_2(v_toPure_21_, lean_box(0), v___x_25_);
return v___x_26_;
}
}
else
{
lean_object* v___f_28_; lean_object* v___x_29_; 
lean_dec(v___x_22_);
lean_del_object(v___x_19_);
v___f_28_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_28_, 0, v_inst_11_);
lean_closure_set(v___f_28_, 1, v_inst_12_);
lean_closure_set(v___f_28_, 2, v_cache_13_);
lean_closure_set(v___f_28_, 3, v_key_14_);
lean_closure_set(v___f_28_, 4, v_toPure_21_);
v___x_29_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v_fallback_15_, v___f_28_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM(lean_object* v_m_31_, lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_cache_37_, lean_object* v_key_38_, lean_object* v_fallback_39_){
_start:
{
lean_object* v_toApplicative_40_; lean_object* v_toBind_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_54_; 
v_toApplicative_40_ = lean_ctor_get(v_inst_34_, 0);
v_toBind_41_ = lean_ctor_get(v_inst_34_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_inst_34_);
if (v_isSharedCheck_54_ == 0)
{
v___x_43_ = v_inst_34_;
v_isShared_44_ = v_isSharedCheck_54_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_toBind_41_);
lean_inc(v_toApplicative_40_);
lean_dec(v_inst_34_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_54_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v_toPure_45_; lean_object* v___x_46_; 
v_toPure_45_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_inc(v_toPure_45_);
lean_dec_ref(v_toApplicative_40_);
lean_inc(v_key_38_);
lean_inc_ref(v_inst_36_);
lean_inc_ref(v_inst_35_);
v___x_46_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_35_, v_inst_36_, v_cache_37_, v_key_38_);
if (lean_obj_tag(v___x_46_) == 1)
{
lean_object* v_val_47_; lean_object* v___x_49_; 
lean_dec(v_toBind_41_);
lean_dec(v_fallback_39_);
lean_dec(v_key_38_);
lean_dec_ref(v_inst_36_);
lean_dec_ref(v_inst_35_);
v_val_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v___x_46_, 1);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v_cache_37_);
lean_ctor_set(v___x_43_, 0, v_val_47_);
v___x_49_ = v___x_43_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_val_47_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_cache_37_);
v___x_49_ = v_reuseFailAlloc_51_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; 
v___x_50_ = lean_apply_2(v_toPure_45_, lean_box(0), v___x_49_);
return v___x_50_;
}
}
else
{
lean_object* v___f_52_; lean_object* v___x_53_; 
lean_dec(v___x_46_);
lean_del_object(v___x_43_);
v___f_52_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_52_, 0, v_inst_35_);
lean_closure_set(v___f_52_, 1, v_inst_36_);
lean_closure_set(v___f_52_, 2, v_cache_37_);
lean_closure_set(v___f_52_, 3, v_key_38_);
lean_closure_set(v___f_52_, 4, v_toPure_45_);
v___x_53_ = lean_apply_4(v_toBind_41_, lean_box(0), lean_box(0), v_fallback_39_, v___f_52_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(lean_object* v_specThm_55_){
_start:
{
lean_object* v_proof_56_; 
v_proof_56_ = lean_ctor_get(v_specThm_55_, 1);
lean_inc_ref(v_proof_56_);
lean_dec_ref(v_specThm_55_);
if (lean_obj_tag(v_proof_56_) == 0)
{
lean_object* v_declName_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
v_declName_57_ = lean_ctor_get(v_proof_56_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v_proof_56_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v_proof_56_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_declName_57_);
lean_dec(v_proof_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
lean_ctor_set_tag(v___x_59_, 1);
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_declName_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
else
{
lean_object* v___x_65_; 
lean_dec_ref(v_proof_56_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object* v_kind_66_, lean_object* v_specThm_67_, lean_object* v_m_68_, lean_object* v_00_u03c3s_69_, lean_object* v_ps_70_, lean_object* v_instWP_71_, lean_object* v_excessArgs_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
if (lean_obj_tag(v_kind_66_) == 0)
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpec(v_specThm_67_, v_m_68_, v_00_u03c3s_69_, v_ps_70_, v_instWP_71_, v_excessArgs_72_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSimpSpec(v_specThm_67_, v_m_68_, v_00_u03c3s_69_, v_ps_70_, v_instWP_71_, v_excessArgs_72_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object** _args){
lean_object* v_kind_87_ = _args[0];
lean_object* v_specThm_88_ = _args[1];
lean_object* v_m_89_ = _args[2];
lean_object* v_00_u03c3s_90_ = _args[3];
lean_object* v_ps_91_ = _args[4];
lean_object* v_instWP_92_ = _args[5];
lean_object* v_excessArgs_93_ = _args[6];
lean_object* v___y_94_ = _args[7];
lean_object* v___y_95_ = _args[8];
lean_object* v___y_96_ = _args[9];
lean_object* v___y_97_ = _args[10];
lean_object* v___y_98_ = _args[11];
lean_object* v___y_99_ = _args[12];
lean_object* v___y_100_ = _args[13];
lean_object* v___y_101_ = _args[14];
lean_object* v___y_102_ = _args[15];
lean_object* v___y_103_ = _args[16];
lean_object* v___y_104_ = _args[17];
lean_object* v___y_105_ = _args[18];
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_kind_87_, v_specThm_88_, v_m_89_, v_00_u03c3s_90_, v_ps_91_, v_instWP_92_, v_excessArgs_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec_ref(v_kind_87_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_a_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v_key_110_; lean_object* v_value_111_; lean_object* v_tail_112_; uint8_t v___y_114_; lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v_fst_119_; lean_object* v_snd_120_; uint8_t v___x_121_; 
v_key_110_ = lean_ctor_get(v_x_108_, 0);
v_value_111_ = lean_ctor_get(v_x_108_, 1);
v_tail_112_ = lean_ctor_get(v_x_108_, 2);
v_fst_117_ = lean_ctor_get(v_key_110_, 0);
v_snd_118_ = lean_ctor_get(v_key_110_, 1);
v_fst_119_ = lean_ctor_get(v_a_107_, 0);
v_snd_120_ = lean_ctor_get(v_a_107_, 1);
v___x_121_ = lean_name_eq(v_fst_117_, v_fst_119_);
if (v___x_121_ == 0)
{
v___y_114_ = v___x_121_;
goto v___jp_113_;
}
else
{
lean_object* v_fst_122_; lean_object* v_snd_123_; lean_object* v_fst_124_; lean_object* v_snd_125_; uint8_t v___x_126_; 
v_fst_122_ = lean_ctor_get(v_snd_118_, 0);
v_snd_123_ = lean_ctor_get(v_snd_118_, 1);
v_fst_124_ = lean_ctor_get(v_snd_120_, 0);
v_snd_125_ = lean_ctor_get(v_snd_120_, 1);
v___x_126_ = lean_expr_eqv(v_fst_122_, v_fst_124_);
if (v___x_126_ == 0)
{
v___y_114_ = v___x_126_;
goto v___jp_113_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_eq(v_snd_123_, v_snd_125_);
v___y_114_ = v___x_127_;
goto v___jp_113_;
}
}
v___jp_113_:
{
if (v___y_114_ == 0)
{
v_x_108_ = v_tail_112_;
goto _start;
}
else
{
lean_object* v___x_116_; 
lean_inc(v_value_111_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_value_111_);
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_128_, v_x_129_);
lean_dec(v_x_129_);
lean_dec_ref(v_a_128_);
return v_res_130_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_131_; uint64_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1723u);
v___x_132_ = lean_uint64_of_nat(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_buckets_135_; lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_138_; uint64_t v___y_140_; 
v_buckets_135_ = lean_ctor_get(v_m_133_, 1);
v_fst_136_ = lean_ctor_get(v_a_134_, 0);
v_snd_137_ = lean_ctor_get(v_a_134_, 1);
v___x_138_ = lean_array_get_size(v_buckets_135_);
if (lean_obj_tag(v_fst_136_) == 0)
{
uint64_t v___x_160_; 
v___x_160_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_140_ = v___x_160_;
goto v___jp_139_;
}
else
{
uint64_t v_hash_161_; 
v_hash_161_ = lean_ctor_get_uint64(v_fst_136_, sizeof(void*)*2);
v___y_140_ = v_hash_161_;
goto v___jp_139_;
}
v___jp_139_:
{
lean_object* v_fst_141_; lean_object* v_snd_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v_fold_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_fst_141_ = lean_ctor_get(v_snd_137_, 0);
v_snd_142_ = lean_ctor_get(v_snd_137_, 1);
v___x_143_ = l_Lean_Expr_hash(v_fst_141_);
v___x_144_ = lean_uint64_of_nat(v_snd_142_);
v___x_145_ = lean_uint64_mix_hash(v___x_143_, v___x_144_);
v___x_146_ = lean_uint64_mix_hash(v___y_140_, v___x_145_);
v___x_147_ = 32ULL;
v___x_148_ = lean_uint64_shift_right(v___x_146_, v___x_147_);
v_fold_149_ = lean_uint64_xor(v___x_146_, v___x_148_);
v___x_150_ = 16ULL;
v___x_151_ = lean_uint64_shift_right(v_fold_149_, v___x_150_);
v___x_152_ = lean_uint64_xor(v_fold_149_, v___x_151_);
v___x_153_ = lean_uint64_to_usize(v___x_152_);
v___x_154_ = lean_usize_of_nat(v___x_138_);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_sub(v___x_154_, v___x_155_);
v___x_157_ = lean_usize_land(v___x_153_, v___x_156_);
v___x_158_ = lean_array_uget_borrowed(v_buckets_135_, v___x_157_);
v___x_159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_134_, v___x_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_162_, v_a_163_);
lean_dec_ref(v_a_163_);
lean_dec_ref(v_m_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
return v_x_165_;
}
else
{
lean_object* v_key_167_; lean_object* v_value_168_; lean_object* v_tail_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_203_; 
v_key_167_ = lean_ctor_get(v_x_166_, 0);
v_value_168_ = lean_ctor_get(v_x_166_, 1);
v_tail_169_ = lean_ctor_get(v_x_166_, 2);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_203_ == 0)
{
v___x_171_ = v_x_166_;
v_isShared_172_ = v_isSharedCheck_203_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_tail_169_);
lean_inc(v_value_168_);
lean_inc(v_key_167_);
lean_dec(v_x_166_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_203_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_fst_173_; lean_object* v_snd_174_; lean_object* v___x_175_; uint64_t v___y_177_; 
v_fst_173_ = lean_ctor_get(v_key_167_, 0);
v_snd_174_ = lean_ctor_get(v_key_167_, 1);
v___x_175_ = lean_array_get_size(v_x_165_);
if (lean_obj_tag(v_fst_173_) == 0)
{
uint64_t v___x_201_; 
v___x_201_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_177_ = v___x_201_;
goto v___jp_176_;
}
else
{
uint64_t v_hash_202_; 
v_hash_202_ = lean_ctor_get_uint64(v_fst_173_, sizeof(void*)*2);
v___y_177_ = v_hash_202_;
goto v___jp_176_;
}
v___jp_176_:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; uint64_t v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v_fold_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v_fst_178_ = lean_ctor_get(v_snd_174_, 0);
v_snd_179_ = lean_ctor_get(v_snd_174_, 1);
v___x_180_ = l_Lean_Expr_hash(v_fst_178_);
v___x_181_ = lean_uint64_of_nat(v_snd_179_);
v___x_182_ = lean_uint64_mix_hash(v___x_180_, v___x_181_);
v___x_183_ = lean_uint64_mix_hash(v___y_177_, v___x_182_);
v___x_184_ = 32ULL;
v___x_185_ = lean_uint64_shift_right(v___x_183_, v___x_184_);
v_fold_186_ = lean_uint64_xor(v___x_183_, v___x_185_);
v___x_187_ = 16ULL;
v___x_188_ = lean_uint64_shift_right(v_fold_186_, v___x_187_);
v___x_189_ = lean_uint64_xor(v_fold_186_, v___x_188_);
v___x_190_ = lean_uint64_to_usize(v___x_189_);
v___x_191_ = lean_usize_of_nat(v___x_175_);
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_sub(v___x_191_, v___x_192_);
v___x_194_ = lean_usize_land(v___x_190_, v___x_193_);
v___x_195_ = lean_array_uget_borrowed(v_x_165_, v___x_194_);
lean_inc(v___x_195_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 2, v___x_195_);
v___x_197_ = v___x_171_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_key_167_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_value_168_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v___x_195_);
v___x_197_ = v_reuseFailAlloc_200_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = lean_array_uset(v_x_165_, v___x_194_, v___x_197_);
v_x_165_ = v___x_198_;
v_x_166_ = v_tail_169_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_204_, lean_object* v_source_205_, lean_object* v_target_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_array_get_size(v_source_205_);
v___x_208_ = lean_nat_dec_lt(v_i_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_dec_ref(v_source_205_);
lean_dec(v_i_204_);
return v_target_206_;
}
else
{
lean_object* v_es_209_; lean_object* v___x_210_; lean_object* v_source_211_; lean_object* v_target_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_es_209_ = lean_array_fget(v_source_205_, v_i_204_);
v___x_210_ = lean_box(0);
v_source_211_ = lean_array_fset(v_source_205_, v_i_204_, v___x_210_);
v_target_212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_206_, v_es_209_);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_i_204_, v___x_213_);
lean_dec(v_i_204_);
v_i_204_ = v___x_214_;
v_source_205_ = v_source_211_;
v_target_206_ = v_target_212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(lean_object* v_data_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_nbuckets_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_217_ = lean_array_get_size(v_data_216_);
v___x_218_ = lean_unsigned_to_nat(2u);
v_nbuckets_219_ = lean_nat_mul(v___x_217_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_box(0);
v___x_222_ = lean_mk_array(v_nbuckets_219_, v___x_221_);
v___x_223_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v___x_220_, v_data_216_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(lean_object* v_a_224_, lean_object* v_x_225_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
else
{
lean_object* v_key_227_; lean_object* v_tail_228_; uint8_t v___y_230_; lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v_fst_234_; lean_object* v_snd_235_; uint8_t v___x_236_; 
v_key_227_ = lean_ctor_get(v_x_225_, 0);
v_tail_228_ = lean_ctor_get(v_x_225_, 2);
v_fst_232_ = lean_ctor_get(v_key_227_, 0);
v_snd_233_ = lean_ctor_get(v_key_227_, 1);
v_fst_234_ = lean_ctor_get(v_a_224_, 0);
v_snd_235_ = lean_ctor_get(v_a_224_, 1);
v___x_236_ = lean_name_eq(v_fst_232_, v_fst_234_);
if (v___x_236_ == 0)
{
v___y_230_ = v___x_236_;
goto v___jp_229_;
}
else
{
lean_object* v_fst_237_; lean_object* v_snd_238_; lean_object* v_fst_239_; lean_object* v_snd_240_; uint8_t v___x_241_; 
v_fst_237_ = lean_ctor_get(v_snd_233_, 0);
v_snd_238_ = lean_ctor_get(v_snd_233_, 1);
v_fst_239_ = lean_ctor_get(v_snd_235_, 0);
v_snd_240_ = lean_ctor_get(v_snd_235_, 1);
v___x_241_ = lean_expr_eqv(v_fst_237_, v_fst_239_);
if (v___x_241_ == 0)
{
v___y_230_ = v___x_241_;
goto v___jp_229_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = lean_nat_dec_eq(v_snd_238_, v_snd_240_);
v___y_230_ = v___x_242_;
goto v___jp_229_;
}
}
v___jp_229_:
{
if (v___y_230_ == 0)
{
v_x_225_ = v_tail_228_;
goto _start;
}
else
{
return v___y_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_243_, lean_object* v_x_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_243_, v_x_244_);
lean_dec(v_x_244_);
lean_dec_ref(v_a_243_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(lean_object* v_a_247_, lean_object* v_b_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_dec(v_b_248_);
lean_dec_ref(v_a_247_);
return v_x_249_;
}
else
{
lean_object* v_key_250_; lean_object* v_value_251_; lean_object* v_tail_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_276_; 
v_key_250_ = lean_ctor_get(v_x_249_, 0);
v_value_251_ = lean_ctor_get(v_x_249_, 1);
v_tail_252_ = lean_ctor_get(v_x_249_, 2);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_276_ == 0)
{
v___x_254_ = v_x_249_;
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_tail_252_);
lean_inc(v_value_251_);
lean_inc(v_key_250_);
lean_dec(v_x_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___y_257_; lean_object* v_fst_265_; lean_object* v_snd_266_; lean_object* v_fst_267_; lean_object* v_snd_268_; uint8_t v___x_269_; 
v_fst_265_ = lean_ctor_get(v_key_250_, 0);
v_snd_266_ = lean_ctor_get(v_key_250_, 1);
v_fst_267_ = lean_ctor_get(v_a_247_, 0);
v_snd_268_ = lean_ctor_get(v_a_247_, 1);
v___x_269_ = lean_name_eq(v_fst_265_, v_fst_267_);
if (v___x_269_ == 0)
{
v___y_257_ = v___x_269_;
goto v___jp_256_;
}
else
{
lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v_fst_272_; lean_object* v_snd_273_; uint8_t v___x_274_; 
v_fst_270_ = lean_ctor_get(v_snd_266_, 0);
v_snd_271_ = lean_ctor_get(v_snd_266_, 1);
v_fst_272_ = lean_ctor_get(v_snd_268_, 0);
v_snd_273_ = lean_ctor_get(v_snd_268_, 1);
v___x_274_ = lean_expr_eqv(v_fst_270_, v_fst_272_);
if (v___x_274_ == 0)
{
v___y_257_ = v___x_274_;
goto v___jp_256_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_eq(v_snd_271_, v_snd_273_);
v___y_257_ = v___x_275_;
goto v___jp_256_;
}
}
v___jp_256_:
{
if (v___y_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_247_, v_b_248_, v_tail_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 2, v___x_258_);
v___x_260_ = v___x_254_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_key_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_value_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
else
{
lean_object* v___x_263_; 
lean_dec(v_value_251_);
lean_dec(v_key_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_b_248_);
lean_ctor_set(v___x_254_, 0, v_a_247_);
v___x_263_ = v___x_254_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_247_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_b_248_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_tail_252_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object* v_m_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_size_280_; lean_object* v_buckets_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_335_; 
v_size_280_ = lean_ctor_get(v_m_277_, 0);
v_buckets_281_ = lean_ctor_get(v_m_277_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_m_277_);
if (v_isSharedCheck_335_ == 0)
{
v___x_283_ = v_m_277_;
v_isShared_284_ = v_isSharedCheck_335_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_buckets_281_);
lean_inc(v_size_280_);
lean_dec(v_m_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_335_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_fst_285_; lean_object* v_snd_286_; lean_object* v___x_287_; uint64_t v___y_289_; 
v_fst_285_ = lean_ctor_get(v_a_278_, 0);
v_snd_286_ = lean_ctor_get(v_a_278_, 1);
v___x_287_ = lean_array_get_size(v_buckets_281_);
if (lean_obj_tag(v_fst_285_) == 0)
{
uint64_t v___x_333_; 
v___x_333_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_289_ = v___x_333_;
goto v___jp_288_;
}
else
{
uint64_t v_hash_334_; 
v_hash_334_ = lean_ctor_get_uint64(v_fst_285_, sizeof(void*)*2);
v___y_289_ = v_hash_334_;
goto v___jp_288_;
}
v___jp_288_:
{
lean_object* v_fst_290_; lean_object* v_snd_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v_fold_298_; uint64_t v___x_299_; uint64_t v___x_300_; uint64_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; lean_object* v_bkt_307_; uint8_t v___x_308_; 
v_fst_290_ = lean_ctor_get(v_snd_286_, 0);
v_snd_291_ = lean_ctor_get(v_snd_286_, 1);
v___x_292_ = l_Lean_Expr_hash(v_fst_290_);
v___x_293_ = lean_uint64_of_nat(v_snd_291_);
v___x_294_ = lean_uint64_mix_hash(v___x_292_, v___x_293_);
v___x_295_ = lean_uint64_mix_hash(v___y_289_, v___x_294_);
v___x_296_ = 32ULL;
v___x_297_ = lean_uint64_shift_right(v___x_295_, v___x_296_);
v_fold_298_ = lean_uint64_xor(v___x_295_, v___x_297_);
v___x_299_ = 16ULL;
v___x_300_ = lean_uint64_shift_right(v_fold_298_, v___x_299_);
v___x_301_ = lean_uint64_xor(v_fold_298_, v___x_300_);
v___x_302_ = lean_uint64_to_usize(v___x_301_);
v___x_303_ = lean_usize_of_nat(v___x_287_);
v___x_304_ = ((size_t)1ULL);
v___x_305_ = lean_usize_sub(v___x_303_, v___x_304_);
v___x_306_ = lean_usize_land(v___x_302_, v___x_305_);
v_bkt_307_ = lean_array_uget_borrowed(v_buckets_281_, v___x_306_);
v___x_308_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_278_, v_bkt_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v_size_x27_310_; lean_object* v___x_311_; lean_object* v_buckets_x27_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v_size_x27_310_ = lean_nat_add(v_size_280_, v___x_309_);
lean_dec(v_size_280_);
lean_inc(v_bkt_307_);
v___x_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_311_, 0, v_a_278_);
lean_ctor_set(v___x_311_, 1, v_b_279_);
lean_ctor_set(v___x_311_, 2, v_bkt_307_);
v_buckets_x27_312_ = lean_array_uset(v_buckets_281_, v___x_306_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(4u);
v___x_314_ = lean_nat_mul(v_size_x27_310_, v___x_313_);
v___x_315_ = lean_unsigned_to_nat(3u);
v___x_316_ = lean_nat_div(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_array_get_size(v_buckets_x27_312_);
v___x_318_ = lean_nat_dec_le(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
if (v___x_318_ == 0)
{
lean_object* v_val_319_; lean_object* v___x_321_; 
v_val_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_buckets_x27_312_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_val_319_);
lean_ctor_set(v___x_283_, 0, v_size_x27_310_);
v___x_321_ = v___x_283_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_size_x27_310_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_val_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v___x_324_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_buckets_x27_312_);
lean_ctor_set(v___x_283_, 0, v_size_x27_310_);
v___x_324_ = v___x_283_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_size_x27_310_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_buckets_x27_312_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v___x_326_; lean_object* v_buckets_x27_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_inc(v_bkt_307_);
v___x_326_ = lean_box(0);
v_buckets_x27_327_ = lean_array_uset(v_buckets_281_, v___x_306_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_278_, v_b_279_, v_bkt_307_);
v___x_329_ = lean_array_uset(v_buckets_x27_327_, v___x_306_, v___x_328_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_329_);
v___x_331_ = v___x_283_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_size_280_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_336_, lean_object* v_m_337_, lean_object* v_00_u03c3s_338_, lean_object* v_ps_339_, lean_object* v_instWP_340_, lean_object* v_excessArgs_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; lean_object* v_kind_355_; lean_object* v___x_356_; 
v___x_354_ = lean_st_ref_get(v_a_343_);
v_kind_355_ = lean_ctor_get(v_specThm_336_, 2);
lean_inc_ref(v_kind_355_);
lean_inc_ref(v_specThm_336_);
v___x_356_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(v_specThm_336_);
if (lean_obj_tag(v___x_356_) == 1)
{
lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_391_; 
v_val_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_391_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_391_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_391_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_specBackwardRuleCache_361_; lean_object* v_splitBackwardRuleCache_362_; lean_object* v_invariants_363_; lean_object* v_vcs_364_; lean_object* v_simpState_365_; lean_object* v_fuel_366_; lean_object* v_inlineHandledInvariants_367_; uint8_t v_preTacFailed_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_390_; 
v_specBackwardRuleCache_361_ = lean_ctor_get(v___x_354_, 0);
v_splitBackwardRuleCache_362_ = lean_ctor_get(v___x_354_, 1);
v_invariants_363_ = lean_ctor_get(v___x_354_, 2);
v_vcs_364_ = lean_ctor_get(v___x_354_, 3);
v_simpState_365_ = lean_ctor_get(v___x_354_, 4);
v_fuel_366_ = lean_ctor_get(v___x_354_, 5);
v_inlineHandledInvariants_367_ = lean_ctor_get(v___x_354_, 6);
v_preTacFailed_368_ = lean_ctor_get_uint8(v___x_354_, sizeof(void*)*7);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_390_ == 0)
{
v___x_370_ = v___x_354_;
v_isShared_371_ = v_isSharedCheck_390_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_inlineHandledInvariants_367_);
lean_inc(v_fuel_366_);
lean_inc(v_simpState_365_);
lean_inc(v_vcs_364_);
lean_inc(v_invariants_363_);
lean_inc(v_splitBackwardRuleCache_362_);
lean_inc(v_specBackwardRuleCache_361_);
lean_dec(v___x_354_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_390_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = lean_array_get_size(v_excessArgs_341_);
lean_inc_ref(v_m_337_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_m_337_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_val_357_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_361_, v___x_384_);
if (lean_obj_tag(v___x_385_) == 1)
{
lean_object* v_val_386_; 
lean_dec_ref_known(v___x_384_, 2);
lean_dec_ref(v_kind_355_);
lean_dec_ref(v_excessArgs_341_);
lean_dec_ref(v_instWP_340_);
lean_dec_ref(v_ps_339_);
lean_dec_ref(v_00_u03c3s_338_);
lean_dec_ref(v_m_337_);
lean_dec_ref(v_specThm_336_);
v_val_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___x_385_, 1);
v_fst_373_ = v_val_386_;
v_snd_374_ = v_specBackwardRuleCache_361_;
goto v___jp_372_;
}
else
{
lean_object* v___x_387_; 
lean_dec(v___x_385_);
v___x_387_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_kind_355_, v_specThm_336_, v_m_337_, v_00_u03c3s_338_, v_ps_339_, v_instWP_340_, v_excessArgs_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec_ref(v_kind_355_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_n(v_a_388_, 2);
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_specBackwardRuleCache_361_, v___x_384_, v_a_388_);
v_fst_373_ = v_a_388_;
v_snd_374_ = v___x_389_;
goto v___jp_372_;
}
else
{
lean_dec_ref_known(v___x_384_, 2);
lean_del_object(v___x_370_);
lean_dec_ref(v_inlineHandledInvariants_367_);
lean_dec(v_fuel_366_);
lean_dec_ref(v_simpState_365_);
lean_dec_ref(v_vcs_364_);
lean_dec_ref(v_invariants_363_);
lean_dec_ref(v_splitBackwardRuleCache_362_);
lean_dec_ref(v_specBackwardRuleCache_361_);
lean_del_object(v___x_359_);
return v___x_387_;
}
}
v___jp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_snd_374_);
v___x_376_ = v___x_370_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_snd_374_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_splitBackwardRuleCache_362_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_invariants_363_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_vcs_364_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_simpState_365_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v_fuel_366_);
lean_ctor_set(v_reuseFailAlloc_381_, 6, v_inlineHandledInvariants_367_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*7, v_preTacFailed_368_);
v___x_376_ = v_reuseFailAlloc_381_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_st_ref_set(v_a_343_, v___x_376_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 0);
lean_ctor_set(v___x_359_, 0, v_fst_373_);
v___x_379_ = v___x_359_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_fst_373_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v___x_356_);
lean_dec(v___x_354_);
v___x_392_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_kind_355_, v_specThm_336_, v_m_337_, v_00_u03c3s_338_, v_ps_339_, v_instWP_340_, v_excessArgs_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec_ref(v_kind_355_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object** _args){
lean_object* v_specThm_393_ = _args[0];
lean_object* v_m_394_ = _args[1];
lean_object* v_00_u03c3s_395_ = _args[2];
lean_object* v_ps_396_ = _args[3];
lean_object* v_instWP_397_ = _args[4];
lean_object* v_excessArgs_398_ = _args[5];
lean_object* v_a_399_ = _args[6];
lean_object* v_a_400_ = _args[7];
lean_object* v_a_401_ = _args[8];
lean_object* v_a_402_ = _args[9];
lean_object* v_a_403_ = _args[10];
lean_object* v_a_404_ = _args[11];
lean_object* v_a_405_ = _args[12];
lean_object* v_a_406_ = _args[13];
lean_object* v_a_407_ = _args[14];
lean_object* v_a_408_ = _args[15];
lean_object* v_a_409_ = _args[16];
lean_object* v_a_410_ = _args[17];
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_393_, v_m_394_, v_00_u03c3s_395_, v_ps_396_, v_instWP_397_, v_excessArgs_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_412_, lean_object* v_m_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_413_, v_a_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_416_, v_m_417_, v_a_418_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_m_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_a_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_m_421_, v_a_422_, v_b_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_429_, v_a_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_a_430_);
return v_res_432_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(lean_object* v_00_u03b2_433_, lean_object* v_a_434_, lean_object* v_x_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_437_, lean_object* v_a_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(v_00_u03b2_437_, v_a_438_, v_x_439_);
lean_dec(v_x_439_);
lean_dec_ref(v_a_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3(lean_object* v_00_u03b2_442_, lean_object* v_data_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_data_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4(lean_object* v_00_u03b2_445_, lean_object* v_a_446_, lean_object* v_b_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_446_, v_b_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_450_, lean_object* v_i_451_, lean_object* v_source_452_, lean_object* v_target_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v_i_451_, v_source_452_, v_target_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_455_, lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(lean_object* v_splitInfo_465_, lean_object* v_m_466_, lean_object* v_00_u03c3s_467_, lean_object* v_ps_468_, lean_object* v_instWP_469_, lean_object* v_excessArgs_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_specBackwardRuleCache_480_; lean_object* v_invariants_481_; lean_object* v_vcs_482_; lean_object* v_simpState_483_; lean_object* v_fuel_484_; lean_object* v_inlineHandledInvariants_485_; uint8_t v_preTacFailed_486_; lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___y_493_; 
switch(lean_obj_tag(v_splitInfo_465_))
{
case 0:
{
lean_object* v___x_511_; 
v___x_511_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1));
v___y_493_ = v___x_511_;
goto v___jp_492_;
}
case 1:
{
lean_object* v___x_512_; 
v___x_512_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3));
v___y_493_ = v___x_512_;
goto v___jp_492_;
}
default: 
{
lean_object* v_matcherApp_513_; lean_object* v_matcherName_514_; 
v_matcherApp_513_ = lean_ctor_get(v_splitInfo_465_, 0);
v_matcherName_514_ = lean_ctor_get(v_matcherApp_513_, 1);
lean_inc(v_matcherName_514_);
v___y_493_ = v_matcherName_514_;
goto v___jp_492_;
}
}
v___jp_479_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_489_, 0, v_specBackwardRuleCache_480_);
lean_ctor_set(v___x_489_, 1, v_snd_488_);
lean_ctor_set(v___x_489_, 2, v_invariants_481_);
lean_ctor_set(v___x_489_, 3, v_vcs_482_);
lean_ctor_set(v___x_489_, 4, v_simpState_483_);
lean_ctor_set(v___x_489_, 5, v_fuel_484_);
lean_ctor_set(v___x_489_, 6, v_inlineHandledInvariants_485_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*7, v_preTacFailed_486_);
v___x_490_ = lean_st_ref_set(v_a_471_, v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_fst_487_);
return v___x_491_;
}
v___jp_492_:
{
lean_object* v___x_494_; lean_object* v_specBackwardRuleCache_495_; lean_object* v_splitBackwardRuleCache_496_; lean_object* v_invariants_497_; lean_object* v_vcs_498_; lean_object* v_simpState_499_; lean_object* v_fuel_500_; lean_object* v_inlineHandledInvariants_501_; uint8_t v_preTacFailed_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_494_ = lean_st_ref_get(v_a_471_);
v_specBackwardRuleCache_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc_ref(v_specBackwardRuleCache_495_);
v_splitBackwardRuleCache_496_ = lean_ctor_get(v___x_494_, 1);
lean_inc_ref(v_splitBackwardRuleCache_496_);
v_invariants_497_ = lean_ctor_get(v___x_494_, 2);
lean_inc_ref(v_invariants_497_);
v_vcs_498_ = lean_ctor_get(v___x_494_, 3);
lean_inc_ref(v_vcs_498_);
v_simpState_499_ = lean_ctor_get(v___x_494_, 4);
lean_inc_ref(v_simpState_499_);
v_fuel_500_ = lean_ctor_get(v___x_494_, 5);
lean_inc(v_fuel_500_);
v_inlineHandledInvariants_501_ = lean_ctor_get(v___x_494_, 6);
lean_inc_ref(v_inlineHandledInvariants_501_);
v_preTacFailed_502_ = lean_ctor_get_uint8(v___x_494_, sizeof(void*)*7);
lean_dec(v___x_494_);
v___x_503_ = lean_array_get_size(v_excessArgs_470_);
lean_inc_ref(v_m_466_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_m_466_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___y_493_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_496_, v___x_505_);
if (lean_obj_tag(v___x_506_) == 1)
{
lean_object* v_val_507_; 
lean_dec_ref_known(v___x_505_, 2);
lean_dec_ref(v_excessArgs_470_);
lean_dec_ref(v_instWP_469_);
lean_dec_ref(v_ps_468_);
lean_dec_ref(v_00_u03c3s_467_);
lean_dec_ref(v_m_466_);
lean_dec_ref(v_splitInfo_465_);
v_val_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v___x_506_, 1);
v_specBackwardRuleCache_480_ = v_specBackwardRuleCache_495_;
v_invariants_481_ = v_invariants_497_;
v_vcs_482_ = v_vcs_498_;
v_simpState_483_ = v_simpState_499_;
v_fuel_484_ = v_fuel_500_;
v_inlineHandledInvariants_485_ = v_inlineHandledInvariants_501_;
v_preTacFailed_486_ = v_preTacFailed_502_;
v_fst_487_ = v_val_507_;
v_snd_488_ = v_splitBackwardRuleCache_496_;
goto v___jp_479_;
}
else
{
lean_object* v___x_508_; 
lean_dec(v___x_506_);
v___x_508_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_465_, v_m_466_, v_00_u03c3s_467_, v_ps_468_, v_instWP_469_, v_excessArgs_470_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc_n(v_a_509_, 2);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_splitBackwardRuleCache_496_, v___x_505_, v_a_509_);
v_specBackwardRuleCache_480_ = v_specBackwardRuleCache_495_;
v_invariants_481_ = v_invariants_497_;
v_vcs_482_ = v_vcs_498_;
v_simpState_483_ = v_simpState_499_;
v_fuel_484_ = v_fuel_500_;
v_inlineHandledInvariants_485_ = v_inlineHandledInvariants_501_;
v_preTacFailed_486_ = v_preTacFailed_502_;
v_fst_487_ = v_a_509_;
v_snd_488_ = v___x_510_;
goto v___jp_479_;
}
else
{
lean_dec_ref_known(v___x_505_, 2);
lean_dec_ref(v_inlineHandledInvariants_501_);
lean_dec(v_fuel_500_);
lean_dec_ref(v_simpState_499_);
lean_dec_ref(v_vcs_498_);
lean_dec_ref(v_invariants_497_);
lean_dec_ref(v_splitBackwardRuleCache_496_);
lean_dec_ref(v_specBackwardRuleCache_495_);
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___boxed(lean_object* v_splitInfo_515_, lean_object* v_m_516_, lean_object* v_00_u03c3s_517_, lean_object* v_ps_518_, lean_object* v_instWP_519_, lean_object* v_excessArgs_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_splitInfo_515_, v_m_516_, v_00_u03c3s_517_, v_ps_518_, v_instWP_519_, v_excessArgs_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(lean_object* v_splitInfo_530_, lean_object* v_m_531_, lean_object* v_00_u03c3s_532_, lean_object* v_ps_533_, lean_object* v_instWP_534_, lean_object* v_excessArgs_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_splitInfo_530_, v_m_531_, v_00_u03c3s_532_, v_ps_533_, v_instWP_534_, v_excessArgs_535_, v_a_537_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___boxed(lean_object** _args){
lean_object* v_splitInfo_549_ = _args[0];
lean_object* v_m_550_ = _args[1];
lean_object* v_00_u03c3s_551_ = _args[2];
lean_object* v_ps_552_ = _args[3];
lean_object* v_instWP_553_ = _args[4];
lean_object* v_excessArgs_554_ = _args[5];
lean_object* v_a_555_ = _args[6];
lean_object* v_a_556_ = _args[7];
lean_object* v_a_557_ = _args[8];
lean_object* v_a_558_ = _args[9];
lean_object* v_a_559_ = _args[10];
lean_object* v_a_560_ = _args[11];
lean_object* v_a_561_ = _args[12];
lean_object* v_a_562_ = _args[13];
lean_object* v_a_563_ = _args[14];
lean_object* v_a_564_ = _args[15];
lean_object* v_a_565_ = _args[16];
lean_object* v_a_566_ = _args[17];
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(v_splitInfo_549_, v_m_550_, v_00_u03c3s_551_, v_ps_552_, v_instWP_553_, v_excessArgs_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_567_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
}
#ifdef __cplusplus
}
#endif
