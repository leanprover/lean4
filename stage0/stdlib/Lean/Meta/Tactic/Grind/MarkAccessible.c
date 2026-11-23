// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MarkAccessible
// Imports: public import Lean.Meta.Tactic.Revert import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkAccessible_0__Lean_Meta_Grind_grindMark___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "__grind_mark"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkAccessible_0__Lean_Meta_Grind_grindMark___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkAccessible_0__Lean_Meta_Grind_grindMark___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkAccessible_0__Lean_Meta_Grind_grindMark = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkAccessible_0__Lean_Meta_Grind_grindMark___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markGrindName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f(lean_object* v_name_3_){
_start:
{
if (lean_obj_tag(v_name_3_) == 1)
{
lean_object* v_pre_4_; lean_object* v_str_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_pre_4_ = lean_ctor_get(v_name_3_, 0);
v_str_5_ = lean_ctor_get(v_name_3_, 1);
v___x_6_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkAccessible_0__Lean_Meta_Grind_grindMark___closed__0));
v___x_7_ = lean_string_dec_eq(v_str_5_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
lean_inc(v_pre_4_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_pre_4_);
return v___x_9_;
}
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f___boxed(lean_object* v_name_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_11_);
lean_dec(v_name_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markGrindName(lean_object* v_userName_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkAccessible_0__Lean_Meta_Grind_grindMark___closed__0));
v___x_15_ = l_Lean_Name_str___override(v_userName_13_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(lean_object* v_mvarId_16_, lean_object* v_x_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_16_, v_x_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_23_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_23_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg___boxed(lean_object* v_mvarId_40_, lean_object* v_x_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_40_, v_x_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(lean_object* v_00_u03b1_48_, lean_object* v_mvarId_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___boxed(lean_object* v_00_u03b1_57_, lean_object* v_mvarId_58_, lean_object* v_x_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(v_00_u03b1_57_, v_mvarId_58_, v_x_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_ks_70_; lean_object* v_vs_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_95_; 
v_ks_70_ = lean_ctor_get(v_x_66_, 0);
v_vs_71_ = lean_ctor_get(v_x_66_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_95_ == 0)
{
v___x_73_ = v_x_66_;
v_isShared_74_ = v_isSharedCheck_95_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_vs_71_);
lean_inc(v_ks_70_);
lean_dec(v_x_66_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_95_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_array_get_size(v_ks_70_);
v___x_76_ = lean_nat_dec_lt(v_x_67_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
lean_dec(v_x_67_);
v___x_77_ = lean_array_push(v_ks_70_, v_x_68_);
v___x_78_ = lean_array_push(v_vs_71_, v_x_69_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_78_);
lean_ctor_set(v___x_73_, 0, v___x_77_);
v___x_80_ = v___x_73_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v_k_x27_82_; uint8_t v___x_83_; 
v_k_x27_82_ = lean_array_fget_borrowed(v_ks_70_, v_x_67_);
v___x_83_ = l_Lean_instBEqMVarId_beq(v_x_68_, v_k_x27_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_85_; 
if (v_isShared_74_ == 0)
{
v___x_85_ = v___x_73_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_ks_70_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_vs_71_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_x_67_, v___x_86_);
lean_dec(v_x_67_);
v_x_66_ = v___x_85_;
v_x_67_ = v___x_87_;
goto _start;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = lean_array_fset(v_ks_70_, v_x_67_, v_x_68_);
v___x_91_ = lean_array_fset(v_vs_71_, v_x_67_, v_x_69_);
lean_dec(v_x_67_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_91_);
lean_ctor_set(v___x_73_, 0, v___x_90_);
v___x_93_ = v___x_73_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_96_, lean_object* v_k_97_, lean_object* v_v_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_96_, v___x_99_, v_k_97_, v_v_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(lean_object* v_x_102_, size_t v_x_103_, size_t v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v_es_107_; size_t v___x_108_; size_t v___x_109_; lean_object* v_j_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_es_107_ = lean_ctor_get(v_x_102_, 0);
v___x_108_ = ((size_t)31ULL);
v___x_109_ = lean_usize_land(v_x_103_, v___x_108_);
v_j_110_ = lean_usize_to_nat(v___x_109_);
v___x_111_ = lean_array_get_size(v_es_107_);
v___x_112_ = lean_nat_dec_lt(v_j_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec(v_j_110_);
lean_dec(v_x_106_);
lean_dec(v_x_105_);
return v_x_102_;
}
else
{
lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_151_; 
lean_inc_ref(v_es_107_);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v_x_102_, 0);
lean_dec(v_unused_152_);
v___x_114_ = v_x_102_;
v_isShared_115_ = v_isSharedCheck_151_;
goto v_resetjp_113_;
}
else
{
lean_dec(v_x_102_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_151_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_v_116_; lean_object* v___x_117_; lean_object* v_xs_x27_118_; lean_object* v___y_120_; 
v_v_116_ = lean_array_fget(v_es_107_, v_j_110_);
v___x_117_ = lean_box(0);
v_xs_x27_118_ = lean_array_fset(v_es_107_, v_j_110_, v___x_117_);
switch(lean_obj_tag(v_v_116_))
{
case 0:
{
lean_object* v_key_125_; lean_object* v_val_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
v_key_125_ = lean_ctor_get(v_v_116_, 0);
v_val_126_ = lean_ctor_get(v_v_116_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_v_116_);
if (v_isSharedCheck_136_ == 0)
{
v___x_128_ = v_v_116_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_val_126_);
lean_inc(v_key_125_);
lean_dec(v_v_116_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
uint8_t v___x_130_; 
v___x_130_ = l_Lean_instBEqMVarId_beq(v_x_105_, v_key_125_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_del_object(v___x_128_);
v___x_131_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_125_, v_val_126_, v_x_105_, v_x_106_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
v___y_120_ = v___x_132_;
goto v___jp_119_;
}
else
{
lean_object* v___x_134_; 
lean_dec(v_val_126_);
lean_dec(v_key_125_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_x_106_);
lean_ctor_set(v___x_128_, 0, v_x_105_);
v___x_134_ = v___x_128_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_x_105_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_x_106_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v___y_120_ = v___x_134_;
goto v___jp_119_;
}
}
}
}
case 1:
{
lean_object* v_node_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_149_; 
v_node_137_ = lean_ctor_get(v_v_116_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_v_116_);
if (v_isSharedCheck_149_ == 0)
{
v___x_139_ = v_v_116_;
v_isShared_140_ = v_isSharedCheck_149_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_node_137_);
lean_dec(v_v_116_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_149_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_141_ = ((size_t)5ULL);
v___x_142_ = lean_usize_shift_right(v_x_103_, v___x_141_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_x_104_, v___x_143_);
v___x_145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_node_137_, v___x_142_, v___x_144_, v_x_105_, v_x_106_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_145_);
v___x_147_ = v___x_139_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
v___y_120_ = v___x_147_;
goto v___jp_119_;
}
}
}
default: 
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v_x_105_);
lean_ctor_set(v___x_150_, 1, v_x_106_);
v___y_120_ = v___x_150_;
goto v___jp_119_;
}
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_array_fset(v_xs_x27_118_, v_j_110_, v___y_120_);
lean_dec(v_j_110_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_121_);
v___x_123_ = v___x_114_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
else
{
lean_object* v_ks_153_; lean_object* v_vs_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_172_; 
v_ks_153_ = lean_ctor_get(v_x_102_, 0);
v_vs_154_ = lean_ctor_get(v_x_102_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_172_ == 0)
{
v___x_156_ = v_x_102_;
v_isShared_157_ = v_isSharedCheck_172_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_vs_154_);
lean_inc(v_ks_153_);
lean_dec(v_x_102_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_172_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_ks_153_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_vs_154_);
v___x_159_ = v_reuseFailAlloc_171_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v_newNode_160_; size_t v___x_161_; uint8_t v___x_162_; 
v_newNode_160_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v___x_159_, v_x_105_, v_x_106_);
v___x_161_ = ((size_t)7ULL);
v___x_162_ = lean_usize_dec_le(v___x_161_, v_x_104_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_160_);
v___x_164_ = lean_unsigned_to_nat(4u);
v___x_165_ = lean_nat_dec_lt(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
if (v___x_165_ == 0)
{
lean_object* v_ks_166_; lean_object* v_vs_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_ks_166_ = lean_ctor_get(v_newNode_160_, 0);
lean_inc_ref(v_ks_166_);
v_vs_167_ = lean_ctor_get(v_newNode_160_, 1);
lean_inc_ref(v_vs_167_);
lean_dec_ref(v_newNode_160_);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_x_104_, v_ks_166_, v_vs_167_, v___x_168_, v___x_169_);
lean_dec_ref(v_vs_167_);
lean_dec_ref(v_ks_166_);
return v___x_170_;
}
else
{
return v_newNode_160_;
}
}
else
{
return v_newNode_160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_173_, lean_object* v_keys_174_, lean_object* v_vals_175_, lean_object* v_i_176_, lean_object* v_entries_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_array_get_size(v_keys_174_);
v___x_179_ = lean_nat_dec_lt(v_i_176_, v___x_178_);
if (v___x_179_ == 0)
{
lean_dec(v_i_176_);
return v_entries_177_;
}
else
{
lean_object* v_k_180_; lean_object* v_v_181_; uint64_t v___x_182_; size_t v_h_183_; size_t v___x_184_; lean_object* v___x_185_; size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v_h_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_k_180_ = lean_array_fget_borrowed(v_keys_174_, v_i_176_);
v_v_181_ = lean_array_fget_borrowed(v_vals_175_, v_i_176_);
v___x_182_ = l_Lean_instHashableMVarId_hash(v_k_180_);
v_h_183_ = lean_uint64_to_usize(v___x_182_);
v___x_184_ = ((size_t)5ULL);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_sub(v_depth_173_, v___x_186_);
v___x_188_ = lean_usize_mul(v___x_184_, v___x_187_);
v_h_189_ = lean_usize_shift_right(v_h_183_, v___x_188_);
v___x_190_ = lean_nat_add(v_i_176_, v___x_185_);
lean_dec(v_i_176_);
lean_inc(v_v_181_);
lean_inc(v_k_180_);
v___x_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_entries_177_, v_h_189_, v_depth_173_, v_k_180_, v_v_181_);
v_i_176_ = v___x_190_;
v_entries_177_ = v___x_191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_193_, lean_object* v_keys_194_, lean_object* v_vals_195_, lean_object* v_i_196_, lean_object* v_entries_197_){
_start:
{
size_t v_depth_boxed_198_; lean_object* v_res_199_; 
v_depth_boxed_198_ = lean_unbox_usize(v_depth_193_);
lean_dec(v_depth_193_);
v_res_199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_198_, v_keys_194_, v_vals_195_, v_i_196_, v_entries_197_);
lean_dec_ref(v_vals_195_);
lean_dec_ref(v_keys_194_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
size_t v_x_2783__boxed_205_; size_t v_x_2784__boxed_206_; lean_object* v_res_207_; 
v_x_2783__boxed_205_ = lean_unbox_usize(v_x_201_);
lean_dec(v_x_201_);
v_x_2784__boxed_206_ = lean_unbox_usize(v_x_202_);
lean_dec(v_x_202_);
v_res_207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_200_, v_x_2783__boxed_205_, v_x_2784__boxed_206_, v_x_203_, v_x_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint64_t v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v___x_211_ = l_Lean_instHashableMVarId_hash(v_x_209_);
v___x_212_ = lean_uint64_to_usize(v___x_211_);
v___x_213_ = ((size_t)1ULL);
v___x_214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_208_, v___x_212_, v___x_213_, v_x_209_, v_x_210_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(lean_object* v_mvarId_215_, lean_object* v_val_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_mctx_220_; lean_object* v_cache_221_; lean_object* v_zetaDeltaFVarIds_222_; lean_object* v_postponed_223_; lean_object* v_diag_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_252_; 
v___x_219_ = lean_st_ref_take(v___y_217_);
v_mctx_220_ = lean_ctor_get(v___x_219_, 0);
v_cache_221_ = lean_ctor_get(v___x_219_, 1);
v_zetaDeltaFVarIds_222_ = lean_ctor_get(v___x_219_, 2);
v_postponed_223_ = lean_ctor_get(v___x_219_, 3);
v_diag_224_ = lean_ctor_get(v___x_219_, 4);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_252_ == 0)
{
v___x_226_ = v___x_219_;
v_isShared_227_ = v_isSharedCheck_252_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_diag_224_);
lean_inc(v_postponed_223_);
lean_inc(v_zetaDeltaFVarIds_222_);
lean_inc(v_cache_221_);
lean_inc(v_mctx_220_);
lean_dec(v___x_219_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_252_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_depth_228_; lean_object* v_levelAssignDepth_229_; lean_object* v_lmvarCounter_230_; lean_object* v_mvarCounter_231_; lean_object* v_lDecls_232_; lean_object* v_decls_233_; lean_object* v_userNames_234_; lean_object* v_lAssignment_235_; lean_object* v_eAssignment_236_; lean_object* v_dAssignment_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_251_; 
v_depth_228_ = lean_ctor_get(v_mctx_220_, 0);
v_levelAssignDepth_229_ = lean_ctor_get(v_mctx_220_, 1);
v_lmvarCounter_230_ = lean_ctor_get(v_mctx_220_, 2);
v_mvarCounter_231_ = lean_ctor_get(v_mctx_220_, 3);
v_lDecls_232_ = lean_ctor_get(v_mctx_220_, 4);
v_decls_233_ = lean_ctor_get(v_mctx_220_, 5);
v_userNames_234_ = lean_ctor_get(v_mctx_220_, 6);
v_lAssignment_235_ = lean_ctor_get(v_mctx_220_, 7);
v_eAssignment_236_ = lean_ctor_get(v_mctx_220_, 8);
v_dAssignment_237_ = lean_ctor_get(v_mctx_220_, 9);
v_isSharedCheck_251_ = !lean_is_exclusive(v_mctx_220_);
if (v_isSharedCheck_251_ == 0)
{
v___x_239_ = v_mctx_220_;
v_isShared_240_ = v_isSharedCheck_251_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_dAssignment_237_);
lean_inc(v_eAssignment_236_);
lean_inc(v_lAssignment_235_);
lean_inc(v_userNames_234_);
lean_inc(v_decls_233_);
lean_inc(v_lDecls_232_);
lean_inc(v_mvarCounter_231_);
lean_inc(v_lmvarCounter_230_);
lean_inc(v_levelAssignDepth_229_);
lean_inc(v_depth_228_);
lean_dec(v_mctx_220_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_251_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = lean_box(0);
v___x_242_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_eAssignment_236_, v_mvarId_215_, v_val_216_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 8, v___x_242_);
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_depth_228_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_levelAssignDepth_229_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_lmvarCounter_230_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_mvarCounter_231_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_lDecls_232_);
lean_ctor_set(v_reuseFailAlloc_250_, 5, v_decls_233_);
lean_ctor_set(v_reuseFailAlloc_250_, 6, v_userNames_234_);
lean_ctor_set(v_reuseFailAlloc_250_, 7, v_lAssignment_235_);
lean_ctor_set(v_reuseFailAlloc_250_, 8, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_250_, 9, v_dAssignment_237_);
v___x_244_ = v_reuseFailAlloc_250_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_244_);
v___x_246_ = v___x_226_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_cache_221_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_zetaDeltaFVarIds_222_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_postponed_223_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_diag_224_);
v___x_246_ = v_reuseFailAlloc_249_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_st_ref_put(v___y_217_, v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_241_);
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg___boxed(lean_object* v_mvarId_253_, lean_object* v_val_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_253_, v_val_254_, v___y_255_);
lean_dec(v___y_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(lean_object* v_upperBound_258_, lean_object* v___x_259_, lean_object* v_a_260_, lean_object* v_b_261_){
_start:
{
lean_object* v_a_264_; uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_lt(v_a_260_, v_upperBound_258_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec(v_a_260_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_b_261_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_nat_sub(v___x_259_, v_a_260_);
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_sub(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
v___x_273_ = l_Lean_LocalContext_getAt_x3f(v_b_261_, v___x_272_);
lean_dec(v___x_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
v_a_264_ = v_b_261_;
goto v___jp_263_;
}
else
{
lean_object* v_val_274_; uint8_t v___x_275_; 
v_val_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v___x_273_, 1);
v___x_275_ = l_Lean_LocalDecl_isImplementationDetail(v_val_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = l_Lean_LocalDecl_userName(v_val_274_);
v___x_277_ = l_Lean_Name_hasMacroScopes(v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = l_Lean_Meta_Grind_markGrindName(v___x_276_);
v___x_279_ = l_Lean_LocalDecl_fvarId(v_val_274_);
lean_dec(v_val_274_);
v___x_280_ = l_Lean_LocalContext_setUserName(v_b_261_, v___x_279_, v___x_278_);
v_a_264_ = v___x_280_;
goto v___jp_263_;
}
else
{
lean_dec(v___x_276_);
lean_dec(v_val_274_);
v_a_264_ = v_b_261_;
goto v___jp_263_;
}
}
else
{
lean_dec(v_val_274_);
v_a_264_ = v_b_261_;
goto v___jp_263_;
}
}
}
v___jp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_a_260_, v___x_265_);
lean_dec(v_a_260_);
v_a_260_ = v___x_266_;
v_b_261_ = v_a_264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg___boxed(lean_object* v_upperBound_281_, lean_object* v___x_282_, lean_object* v_a_283_, lean_object* v_b_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_281_, v___x_282_, v_a_283_, v_b_284_);
lean_dec(v___x_282_);
lean_dec(v_upperBound_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0(lean_object* v_mvarId_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
lean_inc(v_mvarId_287_);
v___x_293_ = l_Lean_MVarId_getDecl(v_mvarId_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_userName_295_; lean_object* v_lctx_296_; lean_object* v_type_297_; lean_object* v_localInstances_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v_userName_295_ = lean_ctor_get(v_a_294_, 0);
lean_inc(v_userName_295_);
v_lctx_296_ = lean_ctor_get(v_a_294_, 1);
lean_inc_ref_n(v_lctx_296_, 2);
v_type_297_ = lean_ctor_get(v_a_294_, 2);
lean_inc_ref(v_type_297_);
v_localInstances_298_ = lean_ctor_get(v_a_294_, 4);
lean_inc_ref(v_localInstances_298_);
lean_dec(v_a_294_);
v___x_299_ = lean_local_ctx_num_indices(v_lctx_296_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v___x_299_, v___x_299_, v___x_300_, v_lctx_296_);
lean_dec(v___x_299_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; uint8_t v___x_303_; lean_object* v___x_304_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v___x_303_ = 2;
v___x_304_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_302_, v_localInstances_298_, v_type_297_, v___x_303_, v_userName_295_, v___x_300_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_n(v_a_305_, 2);
lean_dec_ref_known(v___x_304_, 1);
v___x_306_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_287_, v_a_305_, v___y_289_);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v___x_306_, 0);
lean_dec(v_unused_315_);
v___x_308_ = v___x_306_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_dec(v___x_306_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_Expr_mvarId_x21(v_a_305_);
lean_dec(v_a_305_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_mvarId_287_);
v_a_316_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_304_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_304_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_localInstances_298_);
lean_dec_ref(v_type_297_);
lean_dec(v_userName_295_);
lean_dec(v_mvarId_287_);
v_a_324_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_301_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_301_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v_mvarId_287_);
v_a_332_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_293_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_293_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0___boxed(lean_object* v_mvarId_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_MVarId_markAccessible___lam__0(v_mvarId_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible(lean_object* v_mvarId_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; 
lean_inc(v_mvarId_347_);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_MVarId_markAccessible___lam__0___boxed), 6, 1);
lean_closure_set(v___f_353_, 0, v_mvarId_347_);
v___x_354_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_347_, v___f_353_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___boxed(lean_object* v_mvarId_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_MVarId_markAccessible(v_mvarId_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(lean_object* v_mvarId_362_, lean_object* v_val_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_362_, v_val_363_, v___y_365_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___boxed(lean_object* v_mvarId_370_, lean_object* v_val_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(v_mvarId_370_, v_val_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(lean_object* v_upperBound_378_, lean_object* v___x_379_, lean_object* v_inst_380_, lean_object* v_R_381_, lean_object* v_a_382_, lean_object* v_b_383_, lean_object* v_c_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_378_, v___x_379_, v_a_382_, v_b_383_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___boxed(lean_object* v_upperBound_391_, lean_object* v___x_392_, lean_object* v_inst_393_, lean_object* v_R_394_, lean_object* v_a_395_, lean_object* v_b_396_, lean_object* v_c_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(v_upperBound_391_, v___x_392_, v_inst_393_, v_R_394_, v_a_395_, v_b_396_, v_c_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___x_392_);
lean_dec(v_upperBound_391_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0(lean_object* v_00_u03b2_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_x_405_, v_x_406_, v_x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_409_, lean_object* v_x_410_, size_t v_x_411_, size_t v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_410_, v_x_411_, v_x_412_, v_x_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
size_t v_x_3199__boxed_422_; size_t v_x_3200__boxed_423_; lean_object* v_res_424_; 
v_x_3199__boxed_422_ = lean_unbox_usize(v_x_418_);
lean_dec(v_x_418_);
v_x_3200__boxed_423_ = lean_unbox_usize(v_x_419_);
lean_dec(v_x_419_);
v_res_424_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(v_00_u03b2_416_, v_x_417_, v_x_3199__boxed_422_, v_x_3200__boxed_423_, v_x_420_, v_x_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_425_, lean_object* v_n_426_, lean_object* v_k_427_, lean_object* v_v_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v_n_426_, v_k_427_, v_v_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_430_, size_t v_depth_431_, lean_object* v_keys_432_, lean_object* v_vals_433_, lean_object* v_heq_434_, lean_object* v_i_435_, lean_object* v_entries_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_431_, v_keys_432_, v_vals_433_, v_i_435_, v_entries_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_438_, lean_object* v_depth_439_, lean_object* v_keys_440_, lean_object* v_vals_441_, lean_object* v_heq_442_, lean_object* v_i_443_, lean_object* v_entries_444_){
_start:
{
size_t v_depth_boxed_445_; lean_object* v_res_446_; 
v_depth_boxed_445_ = lean_unbox_usize(v_depth_439_);
lean_dec(v_depth_439_);
v_res_446_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_438_, v_depth_boxed_445_, v_keys_440_, v_vals_441_, v_heq_442_, v_i_443_, v_entries_444_);
lean_dec_ref(v_vals_441_);
lean_dec_ref(v_keys_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_448_, v_x_449_, v_x_450_, v_x_451_);
return v___x_452_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MarkAccessible(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_MarkAccessible(builtin);
}
#ifdef __cplusplus
}
#endif
