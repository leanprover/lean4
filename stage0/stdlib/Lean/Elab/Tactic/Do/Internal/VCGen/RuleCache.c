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
lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_392_; 
v_val_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_392_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_392_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_392_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_specBackwardRuleCache_361_; lean_object* v_splitBackwardRuleCache_362_; lean_object* v_invariants_363_; lean_object* v_vcs_364_; lean_object* v_simpState_365_; lean_object* v_jps_366_; lean_object* v_fuel_367_; lean_object* v_inlineHandledInvariants_368_; uint8_t v_preTacFailed_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_391_; 
v_specBackwardRuleCache_361_ = lean_ctor_get(v___x_354_, 0);
v_splitBackwardRuleCache_362_ = lean_ctor_get(v___x_354_, 1);
v_invariants_363_ = lean_ctor_get(v___x_354_, 2);
v_vcs_364_ = lean_ctor_get(v___x_354_, 3);
v_simpState_365_ = lean_ctor_get(v___x_354_, 4);
v_jps_366_ = lean_ctor_get(v___x_354_, 5);
v_fuel_367_ = lean_ctor_get(v___x_354_, 6);
v_inlineHandledInvariants_368_ = lean_ctor_get(v___x_354_, 7);
v_preTacFailed_369_ = lean_ctor_get_uint8(v___x_354_, sizeof(void*)*8);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_391_ == 0)
{
v___x_371_ = v___x_354_;
v_isShared_372_ = v_isSharedCheck_391_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_inlineHandledInvariants_368_);
lean_inc(v_fuel_367_);
lean_inc(v_jps_366_);
lean_inc(v_simpState_365_);
lean_inc(v_vcs_364_);
lean_inc(v_invariants_363_);
lean_inc(v_splitBackwardRuleCache_362_);
lean_inc(v_specBackwardRuleCache_361_);
lean_dec(v___x_354_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_391_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v_fst_374_; lean_object* v_snd_375_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_array_get_size(v_excessArgs_341_);
lean_inc_ref(v_m_337_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_m_337_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_val_357_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_361_, v___x_385_);
if (lean_obj_tag(v___x_386_) == 1)
{
lean_object* v_val_387_; 
lean_dec_ref_known(v___x_385_, 2);
lean_dec_ref(v_kind_355_);
lean_dec_ref(v_excessArgs_341_);
lean_dec_ref(v_instWP_340_);
lean_dec_ref(v_ps_339_);
lean_dec_ref(v_00_u03c3s_338_);
lean_dec_ref(v_m_337_);
lean_dec_ref(v_specThm_336_);
v_val_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_386_, 1);
v_fst_374_ = v_val_387_;
v_snd_375_ = v_specBackwardRuleCache_361_;
goto v___jp_373_;
}
else
{
lean_object* v___x_388_; 
lean_dec(v___x_386_);
v___x_388_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_kind_355_, v_specThm_336_, v_m_337_, v_00_u03c3s_338_, v_ps_339_, v_instWP_340_, v_excessArgs_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec_ref(v_kind_355_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_n(v_a_389_, 2);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_specBackwardRuleCache_361_, v___x_385_, v_a_389_);
v_fst_374_ = v_a_389_;
v_snd_375_ = v___x_390_;
goto v___jp_373_;
}
else
{
lean_dec_ref_known(v___x_385_, 2);
lean_del_object(v___x_371_);
lean_dec_ref(v_inlineHandledInvariants_368_);
lean_dec(v_fuel_367_);
lean_dec(v_jps_366_);
lean_dec_ref(v_simpState_365_);
lean_dec_ref(v_vcs_364_);
lean_dec_ref(v_invariants_363_);
lean_dec_ref(v_splitBackwardRuleCache_362_);
lean_dec_ref(v_specBackwardRuleCache_361_);
lean_del_object(v___x_359_);
return v___x_388_;
}
}
v___jp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v_snd_375_);
v___x_377_ = v___x_371_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_snd_375_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_splitBackwardRuleCache_362_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_invariants_363_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_vcs_364_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v_simpState_365_);
lean_ctor_set(v_reuseFailAlloc_382_, 5, v_jps_366_);
lean_ctor_set(v_reuseFailAlloc_382_, 6, v_fuel_367_);
lean_ctor_set(v_reuseFailAlloc_382_, 7, v_inlineHandledInvariants_368_);
lean_ctor_set_uint8(v_reuseFailAlloc_382_, sizeof(void*)*8, v_preTacFailed_369_);
v___x_377_ = v_reuseFailAlloc_382_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_st_ref_set(v_a_343_, v___x_377_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 0);
lean_ctor_set(v___x_359_, 0, v_fst_374_);
v___x_380_ = v___x_359_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_fst_374_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
else
{
lean_object* v___x_393_; 
lean_dec(v___x_356_);
lean_dec(v___x_354_);
v___x_393_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_kind_355_, v_specThm_336_, v_m_337_, v_00_u03c3s_338_, v_ps_339_, v_instWP_340_, v_excessArgs_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec_ref(v_kind_355_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object** _args){
lean_object* v_specThm_394_ = _args[0];
lean_object* v_m_395_ = _args[1];
lean_object* v_00_u03c3s_396_ = _args[2];
lean_object* v_ps_397_ = _args[3];
lean_object* v_instWP_398_ = _args[4];
lean_object* v_excessArgs_399_ = _args[5];
lean_object* v_a_400_ = _args[6];
lean_object* v_a_401_ = _args[7];
lean_object* v_a_402_ = _args[8];
lean_object* v_a_403_ = _args[9];
lean_object* v_a_404_ = _args[10];
lean_object* v_a_405_ = _args[11];
lean_object* v_a_406_ = _args[12];
lean_object* v_a_407_ = _args[13];
lean_object* v_a_408_ = _args[14];
lean_object* v_a_409_ = _args[15];
lean_object* v_a_410_ = _args[16];
lean_object* v_a_411_ = _args[17];
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_394_, v_m_395_, v_00_u03c3s_396_, v_ps_397_, v_instWP_398_, v_excessArgs_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_413_, lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_414_, v_a_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_417_, lean_object* v_m_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_417_, v_m_418_, v_a_419_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_m_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object* v_00_u03b2_421_, lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_b_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_m_422_, v_a_423_, v_b_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_426_, lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_430_, lean_object* v_a_431_, lean_object* v_x_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_430_, v_a_431_, v_x_432_);
lean_dec(v_x_432_);
lean_dec_ref(v_a_431_);
return v_res_433_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(lean_object* v_00_u03b2_434_, lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(v_00_u03b2_438_, v_a_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec_ref(v_a_439_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3(lean_object* v_00_u03b2_443_, lean_object* v_data_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_data_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_b_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_447_, v_b_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_451_, lean_object* v_i_452_, lean_object* v_source_453_, lean_object* v_target_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v_i_452_, v_source_453_, v_target_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_457_, v_x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(lean_object* v_splitInfo_466_, lean_object* v_m_467_, lean_object* v_00_u03c3s_468_, lean_object* v_ps_469_, lean_object* v_instWP_470_, lean_object* v_excessArgs_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_specBackwardRuleCache_481_; lean_object* v_invariants_482_; lean_object* v_vcs_483_; lean_object* v_simpState_484_; lean_object* v_jps_485_; lean_object* v_fuel_486_; lean_object* v_inlineHandledInvariants_487_; uint8_t v_preTacFailed_488_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___y_495_; 
switch(lean_obj_tag(v_splitInfo_466_))
{
case 0:
{
lean_object* v___x_514_; 
v___x_514_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1));
v___y_495_ = v___x_514_;
goto v___jp_494_;
}
case 1:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3));
v___y_495_ = v___x_515_;
goto v___jp_494_;
}
default: 
{
lean_object* v_matcherApp_516_; lean_object* v_matcherName_517_; 
v_matcherApp_516_ = lean_ctor_get(v_splitInfo_466_, 0);
v_matcherName_517_ = lean_ctor_get(v_matcherApp_516_, 1);
lean_inc(v_matcherName_517_);
v___y_495_ = v_matcherName_517_;
goto v___jp_494_;
}
}
v___jp_480_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_491_, 0, v_specBackwardRuleCache_481_);
lean_ctor_set(v___x_491_, 1, v_snd_490_);
lean_ctor_set(v___x_491_, 2, v_invariants_482_);
lean_ctor_set(v___x_491_, 3, v_vcs_483_);
lean_ctor_set(v___x_491_, 4, v_simpState_484_);
lean_ctor_set(v___x_491_, 5, v_jps_485_);
lean_ctor_set(v___x_491_, 6, v_fuel_486_);
lean_ctor_set(v___x_491_, 7, v_inlineHandledInvariants_487_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*8, v_preTacFailed_488_);
v___x_492_ = lean_st_ref_set(v_a_472_, v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_fst_489_);
return v___x_493_;
}
v___jp_494_:
{
lean_object* v___x_496_; lean_object* v_specBackwardRuleCache_497_; lean_object* v_splitBackwardRuleCache_498_; lean_object* v_invariants_499_; lean_object* v_vcs_500_; lean_object* v_simpState_501_; lean_object* v_jps_502_; lean_object* v_fuel_503_; lean_object* v_inlineHandledInvariants_504_; uint8_t v_preTacFailed_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_496_ = lean_st_ref_get(v_a_472_);
v_specBackwardRuleCache_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc_ref(v_specBackwardRuleCache_497_);
v_splitBackwardRuleCache_498_ = lean_ctor_get(v___x_496_, 1);
lean_inc_ref(v_splitBackwardRuleCache_498_);
v_invariants_499_ = lean_ctor_get(v___x_496_, 2);
lean_inc_ref(v_invariants_499_);
v_vcs_500_ = lean_ctor_get(v___x_496_, 3);
lean_inc_ref(v_vcs_500_);
v_simpState_501_ = lean_ctor_get(v___x_496_, 4);
lean_inc_ref(v_simpState_501_);
v_jps_502_ = lean_ctor_get(v___x_496_, 5);
lean_inc(v_jps_502_);
v_fuel_503_ = lean_ctor_get(v___x_496_, 6);
lean_inc(v_fuel_503_);
v_inlineHandledInvariants_504_ = lean_ctor_get(v___x_496_, 7);
lean_inc_ref(v_inlineHandledInvariants_504_);
v_preTacFailed_505_ = lean_ctor_get_uint8(v___x_496_, sizeof(void*)*8);
lean_dec(v___x_496_);
v___x_506_ = lean_array_get_size(v_excessArgs_471_);
lean_inc_ref(v_m_467_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_m_467_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___y_495_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_498_, v___x_508_);
if (lean_obj_tag(v___x_509_) == 1)
{
lean_object* v_val_510_; 
lean_dec_ref_known(v___x_508_, 2);
lean_dec_ref(v_excessArgs_471_);
lean_dec_ref(v_instWP_470_);
lean_dec_ref(v_ps_469_);
lean_dec_ref(v_00_u03c3s_468_);
lean_dec_ref(v_m_467_);
lean_dec_ref(v_splitInfo_466_);
v_val_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_509_, 1);
v_specBackwardRuleCache_481_ = v_specBackwardRuleCache_497_;
v_invariants_482_ = v_invariants_499_;
v_vcs_483_ = v_vcs_500_;
v_simpState_484_ = v_simpState_501_;
v_jps_485_ = v_jps_502_;
v_fuel_486_ = v_fuel_503_;
v_inlineHandledInvariants_487_ = v_inlineHandledInvariants_504_;
v_preTacFailed_488_ = v_preTacFailed_505_;
v_fst_489_ = v_val_510_;
v_snd_490_ = v_splitBackwardRuleCache_498_;
goto v___jp_480_;
}
else
{
lean_object* v___x_511_; 
lean_dec(v___x_509_);
v___x_511_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_466_, v_m_467_, v_00_u03c3s_468_, v_ps_469_, v_instWP_470_, v_excessArgs_471_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc_n(v_a_512_, 2);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_splitBackwardRuleCache_498_, v___x_508_, v_a_512_);
v_specBackwardRuleCache_481_ = v_specBackwardRuleCache_497_;
v_invariants_482_ = v_invariants_499_;
v_vcs_483_ = v_vcs_500_;
v_simpState_484_ = v_simpState_501_;
v_jps_485_ = v_jps_502_;
v_fuel_486_ = v_fuel_503_;
v_inlineHandledInvariants_487_ = v_inlineHandledInvariants_504_;
v_preTacFailed_488_ = v_preTacFailed_505_;
v_fst_489_ = v_a_512_;
v_snd_490_ = v___x_513_;
goto v___jp_480_;
}
else
{
lean_dec_ref_known(v___x_508_, 2);
lean_dec_ref(v_inlineHandledInvariants_504_);
lean_dec(v_fuel_503_);
lean_dec(v_jps_502_);
lean_dec_ref(v_simpState_501_);
lean_dec_ref(v_vcs_500_);
lean_dec_ref(v_invariants_499_);
lean_dec_ref(v_splitBackwardRuleCache_498_);
lean_dec_ref(v_specBackwardRuleCache_497_);
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___boxed(lean_object* v_splitInfo_518_, lean_object* v_m_519_, lean_object* v_00_u03c3s_520_, lean_object* v_ps_521_, lean_object* v_instWP_522_, lean_object* v_excessArgs_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_splitInfo_518_, v_m_519_, v_00_u03c3s_520_, v_ps_521_, v_instWP_522_, v_excessArgs_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(lean_object* v_splitInfo_533_, lean_object* v_m_534_, lean_object* v_00_u03c3s_535_, lean_object* v_ps_536_, lean_object* v_instWP_537_, lean_object* v_excessArgs_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_splitInfo_533_, v_m_534_, v_00_u03c3s_535_, v_ps_536_, v_instWP_537_, v_excessArgs_538_, v_a_540_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___boxed(lean_object** _args){
lean_object* v_splitInfo_552_ = _args[0];
lean_object* v_m_553_ = _args[1];
lean_object* v_00_u03c3s_554_ = _args[2];
lean_object* v_ps_555_ = _args[3];
lean_object* v_instWP_556_ = _args[4];
lean_object* v_excessArgs_557_ = _args[5];
lean_object* v_a_558_ = _args[6];
lean_object* v_a_559_ = _args[7];
lean_object* v_a_560_ = _args[8];
lean_object* v_a_561_ = _args[9];
lean_object* v_a_562_ = _args[10];
lean_object* v_a_563_ = _args[11];
lean_object* v_a_564_ = _args[12];
lean_object* v_a_565_ = _args[13];
lean_object* v_a_566_ = _args[14];
lean_object* v_a_567_ = _args[15];
lean_object* v_a_568_ = _args[16];
lean_object* v_a_569_ = _args[17];
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(v_splitInfo_552_, v_m_553_, v_00_u03c3s_554_, v_ps_555_, v_instWP_556_, v_excessArgs_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
return v_res_570_;
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
