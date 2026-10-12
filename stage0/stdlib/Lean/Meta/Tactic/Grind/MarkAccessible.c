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
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(lean_object* v_mvarId_16_, lean_object* v_x_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_16_ = stack[0].m_obj;
lean_object* v_x_17_ = stack[1].m_obj;
lean_object* v___y_18_ = stack[2].m_obj;
lean_object* v___y_19_ = stack[3].m_obj;
lean_object* v___y_20_ = stack[4].m_obj;
lean_object* v___y_21_ = stack[5].m_obj;
lean_object* v_res_40_;
v_res_40_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_16_, v_x_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg___boxed(lean_object* v_mvarId_41_, lean_object* v_x_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_41_, v_x_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
return v_res_48_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(lean_object* v_00_u03b1_49_, lean_object* v_mvarId_50_, lean_object* v_x_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_50_, v_x_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
return v___x_57_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_50_ = stack[1].m_obj;
lean_object* v_x_51_ = stack[2].m_obj;
lean_object* v___y_52_ = stack[3].m_obj;
lean_object* v___y_53_ = stack[4].m_obj;
lean_object* v___y_54_ = stack[5].m_obj;
lean_object* v___y_55_ = stack[6].m_obj;
lean_object* v_res_58_;
v_res_58_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(lean_box(0), v_mvarId_50_, v_x_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___boxed(lean_object* v_00_u03b1_59_, lean_object* v_mvarId_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(v_00_u03b1_59_, v_mvarId_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_ks_72_; lean_object* v_vs_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_97_; 
v_ks_72_ = lean_ctor_get(v_x_68_, 0);
v_vs_73_ = lean_ctor_get(v_x_68_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_68_);
if (v_isSharedCheck_97_ == 0)
{
v___x_75_ = v_x_68_;
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_vs_73_);
lean_inc(v_ks_72_);
lean_dec(v_x_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_array_get_size(v_ks_72_);
v___x_78_ = lean_nat_dec_lt(v_x_69_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
lean_dec(v_x_69_);
v___x_79_ = lean_array_push(v_ks_72_, v_x_70_);
v___x_80_ = lean_array_push(v_vs_73_, v_x_71_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_80_);
lean_ctor_set(v___x_75_, 0, v___x_79_);
v___x_82_ = v___x_75_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
else
{
lean_object* v_k_x27_84_; uint8_t v___x_85_; 
v_k_x27_84_ = lean_array_fget_borrowed(v_ks_72_, v_x_69_);
v___x_85_ = l_Lean_instBEqMVarId_beq(v_x_70_, v_k_x27_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_87_; 
if (v_isShared_76_ == 0)
{
v___x_87_ = v___x_75_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_ks_72_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_vs_73_);
v___x_87_ = v_reuseFailAlloc_91_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_add(v_x_69_, v___x_88_);
lean_dec(v_x_69_);
v_x_68_ = v___x_87_;
v_x_69_ = v___x_89_;
goto _start;
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_92_ = lean_array_fset(v_ks_72_, v_x_69_, v_x_70_);
v___x_93_ = lean_array_fset(v_vs_73_, v_x_69_, v_x_71_);
lean_dec(v_x_69_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_93_);
lean_ctor_set(v___x_75_, 0, v___x_92_);
v___x_95_ = v___x_75_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_98_, lean_object* v_k_99_, lean_object* v_v_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_98_, v___x_101_, v_k_99_, v_v_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_103_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(lean_object* v_x_104_, size_t v_x_105_, size_t v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v_es_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v_j_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_es_109_ = lean_ctor_get(v_x_104_, 0);
v___x_110_ = ((size_t)31ULL);
v___x_111_ = lean_usize_land(v_x_105_, v___x_110_);
v_j_112_ = lean_usize_to_nat(v___x_111_);
v___x_113_ = lean_array_get_size(v_es_109_);
v___x_114_ = lean_nat_dec_lt(v_j_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec(v_j_112_);
lean_dec(v_x_108_);
lean_dec(v_x_107_);
return v_x_104_;
}
else
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_153_; 
lean_inc_ref(v_es_109_);
v_isSharedCheck_153_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v_x_104_, 0);
lean_dec(v_unused_154_);
v___x_116_ = v_x_104_;
v_isShared_117_ = v_isSharedCheck_153_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_x_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_153_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_v_118_; lean_object* v___x_119_; lean_object* v_xs_x27_120_; lean_object* v___y_122_; 
v_v_118_ = lean_array_fget(v_es_109_, v_j_112_);
v___x_119_ = lean_box(0);
v_xs_x27_120_ = lean_array_fset(v_es_109_, v_j_112_, v___x_119_);
switch(lean_obj_tag(v_v_118_))
{
case 0:
{
lean_object* v_key_127_; lean_object* v_val_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_138_; 
v_key_127_ = lean_ctor_get(v_v_118_, 0);
v_val_128_ = lean_ctor_get(v_v_118_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_v_118_);
if (v_isSharedCheck_138_ == 0)
{
v___x_130_ = v_v_118_;
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_val_128_);
lean_inc(v_key_127_);
lean_dec(v_v_118_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
uint8_t v___x_132_; 
v___x_132_ = l_Lean_instBEqMVarId_beq(v_x_107_, v_key_127_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_del_object(v___x_130_);
v___x_133_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_127_, v_val_128_, v_x_107_, v_x_108_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v___y_122_ = v___x_134_;
goto v___jp_121_;
}
else
{
lean_object* v___x_136_; 
lean_dec(v_val_128_);
lean_dec(v_key_127_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_x_108_);
lean_ctor_set(v___x_130_, 0, v_x_107_);
v___x_136_ = v___x_130_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_x_107_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_x_108_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v___y_122_ = v___x_136_;
goto v___jp_121_;
}
}
}
}
case 1:
{
lean_object* v_node_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
v_node_139_ = lean_ctor_get(v_v_118_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_v_118_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v_v_118_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_node_139_);
lean_dec(v_v_118_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_143_ = ((size_t)5ULL);
v___x_144_ = lean_usize_shift_right(v_x_105_, v___x_143_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_x_106_, v___x_145_);
v___x_147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_node_139_, v___x_144_, v___x_146_, v_x_107_, v_x_108_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_147_);
v___x_149_ = v___x_141_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v___y_122_ = v___x_149_;
goto v___jp_121_;
}
}
}
default: 
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_x_107_);
lean_ctor_set(v___x_152_, 1, v_x_108_);
v___y_122_ = v___x_152_;
goto v___jp_121_;
}
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_array_fset(v_xs_x27_120_, v_j_112_, v___y_122_);
lean_dec(v_j_112_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_123_);
v___x_125_ = v___x_116_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
else
{
lean_object* v_ks_155_; lean_object* v_vs_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_174_; 
v_ks_155_ = lean_ctor_get(v_x_104_, 0);
v_vs_156_ = lean_ctor_get(v_x_104_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_174_ == 0)
{
v___x_158_ = v_x_104_;
v_isShared_159_ = v_isSharedCheck_174_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_vs_156_);
lean_inc(v_ks_155_);
lean_dec(v_x_104_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_174_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_ks_155_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_vs_156_);
v___x_161_ = v_reuseFailAlloc_173_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v_newNode_162_; size_t v___x_163_; uint8_t v___x_164_; 
v_newNode_162_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v___x_161_, v_x_107_, v_x_108_);
v___x_163_ = ((size_t)7ULL);
v___x_164_ = lean_usize_dec_le(v___x_163_, v_x_106_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_165_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_162_);
v___x_166_ = lean_unsigned_to_nat(4u);
v___x_167_ = lean_nat_dec_lt(v___x_165_, v___x_166_);
lean_dec(v___x_165_);
if (v___x_167_ == 0)
{
lean_object* v_ks_168_; lean_object* v_vs_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_ks_168_ = lean_ctor_get(v_newNode_162_, 0);
lean_inc_ref(v_ks_168_);
v_vs_169_ = lean_ctor_get(v_newNode_162_, 1);
lean_inc_ref(v_vs_169_);
lean_dec_ref(v_newNode_162_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_x_106_, v_ks_168_, v_vs_169_, v___x_170_, v___x_171_);
lean_dec_ref(v_vs_169_);
lean_dec_ref(v_ks_168_);
return v___x_172_;
}
else
{
return v_newNode_162_;
}
}
else
{
return v_newNode_162_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_104_ = stack[0].m_obj;
size_t v_x_105_ = stack[1].m_num;
size_t v_x_106_ = stack[2].m_num;
lean_object* v_x_107_ = stack[3].m_obj;
lean_object* v_x_108_ = stack[4].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_104_, v_x_105_, v_x_106_, v_x_107_, v_x_108_);
stack->m_obj
 = v_res_175_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_176_, lean_object* v_keys_177_, lean_object* v_vals_178_, lean_object* v_i_179_, lean_object* v_entries_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_array_get_size(v_keys_177_);
v___x_182_ = lean_nat_dec_lt(v_i_179_, v___x_181_);
if (v___x_182_ == 0)
{
lean_dec(v_i_179_);
return v_entries_180_;
}
else
{
lean_object* v_k_183_; lean_object* v_v_184_; uint64_t v___x_185_; size_t v_h_186_; size_t v___x_187_; lean_object* v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v_h_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_k_183_ = lean_array_fget_borrowed(v_keys_177_, v_i_179_);
v_v_184_ = lean_array_fget_borrowed(v_vals_178_, v_i_179_);
v___x_185_ = l_Lean_instHashableMVarId_hash(v_k_183_);
v_h_186_ = lean_uint64_to_usize(v___x_185_);
v___x_187_ = ((size_t)5ULL);
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_sub(v_depth_176_, v___x_189_);
v___x_191_ = lean_usize_mul(v___x_187_, v___x_190_);
v_h_192_ = lean_usize_shift_right(v_h_186_, v___x_191_);
v___x_193_ = lean_nat_add(v_i_179_, v___x_188_);
lean_dec(v_i_179_);
lean_inc(v_v_184_);
lean_inc(v_k_183_);
v___x_194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_entries_180_, v_h_192_, v_depth_176_, v_k_183_, v_v_184_);
v_i_179_ = v___x_193_;
v_entries_180_ = v___x_194_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_176_ = stack[0].m_num;
lean_object* v_keys_177_ = stack[1].m_obj;
lean_object* v_vals_178_ = stack[2].m_obj;
lean_object* v_i_179_ = stack[3].m_obj;
lean_object* v_entries_180_ = stack[4].m_obj;
lean_object* v_res_196_;
v_res_196_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_176_, v_keys_177_, v_vals_178_, v_i_179_, v_entries_180_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_197_, lean_object* v_keys_198_, lean_object* v_vals_199_, lean_object* v_i_200_, lean_object* v_entries_201_){
_start:
{
size_t v_depth_boxed_202_; lean_object* v_res_203_; 
v_depth_boxed_202_ = lean_unbox_usize(v_depth_197_);
lean_dec(v_depth_197_);
v_res_203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_202_, v_keys_198_, v_vals_199_, v_i_200_, v_entries_201_);
lean_dec_ref(v_vals_199_);
lean_dec_ref(v_keys_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
size_t v_x_2860__boxed_209_; size_t v_x_2861__boxed_210_; lean_object* v_res_211_; 
v_x_2860__boxed_209_ = lean_unbox_usize(v_x_205_);
lean_dec(v_x_205_);
v_x_2861__boxed_210_ = lean_unbox_usize(v_x_206_);
lean_dec(v_x_206_);
v_res_211_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_204_, v_x_2860__boxed_209_, v_x_2861__boxed_210_, v_x_207_, v_x_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
uint64_t v___x_215_; size_t v___x_216_; size_t v___x_217_; lean_object* v___x_218_; 
v___x_215_ = l_Lean_instHashableMVarId_hash(v_x_213_);
v___x_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_212_, v___x_216_, v___x_217_, v_x_213_, v_x_214_);
return v___x_218_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(lean_object* v_mvarId_219_, lean_object* v_val_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_mctx_224_; lean_object* v_cache_225_; lean_object* v_zetaDeltaFVarIds_226_; lean_object* v_postponed_227_; lean_object* v_diag_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_258_; 
v___x_223_ = lean_st_ref_take(v___y_221_);
v_mctx_224_ = lean_ctor_get(v___x_223_, 0);
v_cache_225_ = lean_ctor_get(v___x_223_, 1);
v_zetaDeltaFVarIds_226_ = lean_ctor_get(v___x_223_, 2);
v_postponed_227_ = lean_ctor_get(v___x_223_, 3);
v_diag_228_ = lean_ctor_get(v___x_223_, 4);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_258_ == 0)
{
v___x_230_ = v___x_223_;
v_isShared_231_ = v_isSharedCheck_258_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_diag_228_);
lean_inc(v_postponed_227_);
lean_inc(v_zetaDeltaFVarIds_226_);
lean_inc(v_cache_225_);
lean_inc(v_mctx_224_);
lean_dec(v___x_223_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_258_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_depth_232_; lean_object* v_levelAssignDepth_233_; lean_object* v_lmvarCounter_234_; lean_object* v_mvarCounter_235_; lean_object* v_lDecls_236_; lean_object* v_decls_237_; lean_object* v_userNames_238_; lean_object* v_lAssignment_239_; lean_object* v_eAssignment_240_; lean_object* v_dAssignment_241_; lean_object* v_instanceTypedMVars_242_; lean_object* v_synthNormMemo_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_257_; 
v_depth_232_ = lean_ctor_get(v_mctx_224_, 0);
v_levelAssignDepth_233_ = lean_ctor_get(v_mctx_224_, 1);
v_lmvarCounter_234_ = lean_ctor_get(v_mctx_224_, 2);
v_mvarCounter_235_ = lean_ctor_get(v_mctx_224_, 3);
v_lDecls_236_ = lean_ctor_get(v_mctx_224_, 4);
v_decls_237_ = lean_ctor_get(v_mctx_224_, 5);
v_userNames_238_ = lean_ctor_get(v_mctx_224_, 6);
v_lAssignment_239_ = lean_ctor_get(v_mctx_224_, 7);
v_eAssignment_240_ = lean_ctor_get(v_mctx_224_, 8);
v_dAssignment_241_ = lean_ctor_get(v_mctx_224_, 9);
v_instanceTypedMVars_242_ = lean_ctor_get(v_mctx_224_, 10);
v_synthNormMemo_243_ = lean_ctor_get(v_mctx_224_, 11);
v_isSharedCheck_257_ = !lean_is_exclusive(v_mctx_224_);
if (v_isSharedCheck_257_ == 0)
{
v___x_245_ = v_mctx_224_;
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_synthNormMemo_243_);
lean_inc(v_instanceTypedMVars_242_);
lean_inc(v_dAssignment_241_);
lean_inc(v_eAssignment_240_);
lean_inc(v_lAssignment_239_);
lean_inc(v_userNames_238_);
lean_inc(v_decls_237_);
lean_inc(v_lDecls_236_);
lean_inc(v_mvarCounter_235_);
lean_inc(v_lmvarCounter_234_);
lean_inc(v_levelAssignDepth_233_);
lean_inc(v_depth_232_);
lean_dec(v_mctx_224_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_box(0);
v___x_248_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_eAssignment_240_, v_mvarId_219_, v_val_220_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 8, v___x_248_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_depth_232_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_levelAssignDepth_233_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_lmvarCounter_234_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_mvarCounter_235_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_lDecls_236_);
lean_ctor_set(v_reuseFailAlloc_256_, 5, v_decls_237_);
lean_ctor_set(v_reuseFailAlloc_256_, 6, v_userNames_238_);
lean_ctor_set(v_reuseFailAlloc_256_, 7, v_lAssignment_239_);
lean_ctor_set(v_reuseFailAlloc_256_, 8, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_256_, 9, v_dAssignment_241_);
lean_ctor_set(v_reuseFailAlloc_256_, 10, v_instanceTypedMVars_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 11, v_synthNormMemo_243_);
v___x_250_ = v_reuseFailAlloc_256_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_250_);
v___x_252_ = v___x_230_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_cache_225_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_zetaDeltaFVarIds_226_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_postponed_227_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_diag_228_);
v___x_252_ = v_reuseFailAlloc_255_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_st_ref_put(v___y_221_, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_247_);
return v___x_254_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_219_ = stack[0].m_obj;
lean_object* v_val_220_ = stack[1].m_obj;
lean_object* v___y_221_ = stack[2].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_219_, v_val_220_, v___y_221_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg___boxed(lean_object* v_mvarId_260_, lean_object* v_val_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_260_, v_val_261_, v___y_262_);
lean_dec(v___y_262_);
return v_res_264_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(lean_object* v_upperBound_265_, lean_object* v___x_266_, lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
lean_object* v_a_271_; uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_lt(v_a_267_, v_upperBound_265_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v_a_267_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_b_268_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_nat_sub(v___x_266_, v_a_267_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_sub(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
v___x_280_ = l_Lean_LocalContext_getAt_x3f(v_b_268_, v___x_279_);
lean_dec(v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
v_a_271_ = v_b_268_;
goto v___jp_270_;
}
else
{
lean_object* v_val_281_; uint8_t v___x_282_; 
v_val_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = l_Lean_LocalDecl_isImplementationDetail(v_val_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = l_Lean_LocalDecl_userName(v_val_281_);
v___x_284_ = l_Lean_Name_hasMacroScopes(v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Meta_Grind_markGrindName(v___x_283_);
v___x_286_ = l_Lean_LocalDecl_fvarId(v_val_281_);
lean_dec(v_val_281_);
v___x_287_ = l_Lean_LocalContext_setUserName(v_b_268_, v___x_286_, v___x_285_);
v_a_271_ = v___x_287_;
goto v___jp_270_;
}
else
{
lean_dec(v___x_283_);
lean_dec(v_val_281_);
v_a_271_ = v_b_268_;
goto v___jp_270_;
}
}
else
{
lean_dec(v_val_281_);
v_a_271_ = v_b_268_;
goto v___jp_270_;
}
}
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_a_267_, v___x_272_);
lean_dec(v_a_267_);
v_a_267_ = v___x_273_;
v_b_268_ = v_a_271_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_265_ = stack[0].m_obj;
lean_object* v___x_266_ = stack[1].m_obj;
lean_object* v_a_267_ = stack[2].m_obj;
lean_object* v_b_268_ = stack[3].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_265_, v___x_266_, v_a_267_, v_b_268_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg___boxed(lean_object* v_upperBound_289_, lean_object* v___x_290_, lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_289_, v___x_290_, v_a_291_, v_b_292_);
lean_dec(v___x_290_);
lean_dec(v_upperBound_289_);
return v_res_294_;
}
}
lean_object* l_Lean_MVarId_markAccessible___lam__0(lean_object* v_mvarId_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
lean_inc(v_mvarId_295_);
v___x_301_ = l_Lean_MVarId_getDecl(v_mvarId_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_userName_303_; lean_object* v_lctx_304_; lean_object* v_type_305_; lean_object* v_localInstances_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v_userName_303_ = lean_ctor_get(v_a_302_, 0);
lean_inc(v_userName_303_);
v_lctx_304_ = lean_ctor_get(v_a_302_, 1);
lean_inc_ref_n(v_lctx_304_, 2);
v_type_305_ = lean_ctor_get(v_a_302_, 2);
lean_inc_ref(v_type_305_);
v_localInstances_306_ = lean_ctor_get(v_a_302_, 4);
lean_inc_ref(v_localInstances_306_);
lean_dec(v_a_302_);
v___x_307_ = lean_local_ctx_num_indices(v_lctx_304_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v___x_307_, v___x_307_, v___x_308_, v_lctx_304_);
lean_dec(v___x_307_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; uint8_t v___x_311_; lean_object* v___x_312_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v___x_311_ = 2;
v___x_312_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_310_, v_localInstances_306_, v_type_305_, v___x_311_, v_userName_303_, v___x_308_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_n(v_a_313_, 2);
lean_dec_ref_known(v___x_312_, 1);
v___x_314_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_295_, v_a_313_, v___y_297_);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v___x_314_, 0);
lean_dec(v_unused_323_);
v___x_316_ = v___x_314_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___x_314_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = l_Lean_Expr_mvarId_x21(v_a_313_);
lean_dec(v_a_313_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_318_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_mvarId_295_);
v_a_324_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_312_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_312_);
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
lean_dec_ref(v_localInstances_306_);
lean_dec_ref(v_type_305_);
lean_dec(v_userName_303_);
lean_dec(v_mvarId_295_);
v_a_332_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_309_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_309_);
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
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_mvarId_295_);
v_a_340_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_301_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_301_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_markAccessible___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_295_ = stack[0].m_obj;
lean_object* v___y_296_ = stack[1].m_obj;
lean_object* v___y_297_ = stack[2].m_obj;
lean_object* v___y_298_ = stack[3].m_obj;
lean_object* v___y_299_ = stack[4].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_Lean_MVarId_markAccessible___lam__0(v_mvarId_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0___boxed(lean_object* v_mvarId_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_MVarId_markAccessible___lam__0(v_mvarId_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_355_;
}
}
lean_object* l_Lean_MVarId_markAccessible(lean_object* v_mvarId_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___f_362_; lean_object* v___x_363_; 
lean_inc(v_mvarId_356_);
v___f_362_ = lean_alloc_closure((void*)(l_Lean_MVarId_markAccessible___lam__0___boxed), 6, 1);
lean_closure_set(v___f_362_, 0, v_mvarId_356_);
v___x_363_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_356_, v___f_362_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_363_;
}
}
LEAN_EXPORT void l_Lean_MVarId_markAccessible_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_356_ = stack[0].m_obj;
lean_object* v_a_357_ = stack[1].m_obj;
lean_object* v_a_358_ = stack[2].m_obj;
lean_object* v_a_359_ = stack[3].m_obj;
lean_object* v_a_360_ = stack[4].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_Lean_MVarId_markAccessible(v_mvarId_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___boxed(lean_object* v_mvarId_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_MVarId_markAccessible(v_mvarId_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(lean_object* v_mvarId_372_, lean_object* v_val_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_372_, v_val_373_, v___y_375_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_372_ = stack[0].m_obj;
lean_object* v_val_373_ = stack[1].m_obj;
lean_object* v___y_374_ = stack[2].m_obj;
lean_object* v___y_375_ = stack[3].m_obj;
lean_object* v___y_376_ = stack[4].m_obj;
lean_object* v___y_377_ = stack[5].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(v_mvarId_372_, v_val_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___boxed(lean_object* v_mvarId_381_, lean_object* v_val_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(v_mvarId_381_, v_val_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_388_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(lean_object* v_upperBound_389_, lean_object* v___x_390_, lean_object* v_inst_391_, lean_object* v_R_392_, lean_object* v_a_393_, lean_object* v_b_394_, lean_object* v_c_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_389_, v___x_390_, v_a_393_, v_b_394_);
return v___x_401_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_389_ = stack[0].m_obj;
lean_object* v___x_390_ = stack[1].m_obj;
lean_object* v_a_393_ = stack[4].m_obj;
lean_object* v_b_394_ = stack[5].m_obj;
lean_object* v___y_396_ = stack[7].m_obj;
lean_object* v___y_397_ = stack[8].m_obj;
lean_object* v___y_398_ = stack[9].m_obj;
lean_object* v___y_399_ = stack[10].m_obj;
lean_object* v_res_402_;
v_res_402_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(v_upperBound_389_, v___x_390_, lean_box(0), lean_box(0), v_a_393_, v_b_394_, lean_box(0), v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___boxed(lean_object* v_upperBound_403_, lean_object* v___x_404_, lean_object* v_inst_405_, lean_object* v_R_406_, lean_object* v_a_407_, lean_object* v_b_408_, lean_object* v_c_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(v_upperBound_403_, v___x_404_, v_inst_405_, v_R_406_, v_a_407_, v_b_408_, v_c_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___x_404_);
lean_dec(v_upperBound_403_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_x_417_, v_x_418_, v_x_419_);
return v___x_420_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_421_, lean_object* v_x_422_, size_t v_x_423_, size_t v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_422_, v_x_423_, v_x_424_, v_x_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_422_ = stack[1].m_obj;
size_t v_x_423_ = stack[2].m_num;
size_t v_x_424_ = stack[3].m_num;
lean_object* v_x_425_ = stack[4].m_obj;
lean_object* v_x_426_ = stack[5].m_obj;
lean_object* v_res_428_;
v_res_428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(lean_box(0), v_x_422_, v_x_423_, v_x_424_, v_x_425_, v_x_426_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
size_t v_x_3503__boxed_435_; size_t v_x_3504__boxed_436_; lean_object* v_res_437_; 
v_x_3503__boxed_435_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_x_3504__boxed_436_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(v_00_u03b2_429_, v_x_430_, v_x_3503__boxed_435_, v_x_3504__boxed_436_, v_x_433_, v_x_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_438_, lean_object* v_n_439_, lean_object* v_k_440_, lean_object* v_v_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v_n_439_, v_k_440_, v_v_441_);
return v___x_442_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_443_, size_t v_depth_444_, lean_object* v_keys_445_, lean_object* v_vals_446_, lean_object* v_heq_447_, lean_object* v_i_448_, lean_object* v_entries_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_444_, v_keys_445_, v_vals_446_, v_i_448_, v_entries_449_);
return v___x_450_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_444_ = stack[1].m_num;
lean_object* v_keys_445_ = stack[2].m_obj;
lean_object* v_vals_446_ = stack[3].m_obj;
lean_object* v_i_448_ = stack[5].m_obj;
lean_object* v_entries_449_ = stack[6].m_obj;
lean_object* v_res_451_;
v_res_451_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(lean_box(0), v_depth_444_, v_keys_445_, v_vals_446_, lean_box(0), v_i_448_, v_entries_449_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_452_, lean_object* v_depth_453_, lean_object* v_keys_454_, lean_object* v_vals_455_, lean_object* v_heq_456_, lean_object* v_i_457_, lean_object* v_entries_458_){
_start:
{
size_t v_depth_boxed_459_; lean_object* v_res_460_; 
v_depth_boxed_459_ = lean_unbox_usize(v_depth_453_);
lean_dec(v_depth_453_);
v_res_460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_452_, v_depth_boxed_459_, v_keys_454_, v_vals_455_, v_heq_456_, v_i_457_, v_entries_458_);
lean_dec_ref(v_vals_455_);
lean_dec_ref(v_keys_454_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_462_, v_x_463_, v_x_464_, v_x_465_);
return v___x_466_;
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
