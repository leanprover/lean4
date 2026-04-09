// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injection
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Clear import Lean.Meta.AppBuilder import Lean.Meta.CtorRecognizer
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorAppCore_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_8_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(v_mvarId_25_, v_x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1(lean_object* v_00_u03b1_33_, lean_object* v_mvarId_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(v_mvarId_34_, v_x_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___boxed(lean_object* v_00_u03b1_42_, lean_object* v_mvarId_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1(v_00_u03b1_42_, v_mvarId_43_, v_x_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_ks_55_; lean_object* v_vs_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_80_; 
v_ks_55_ = lean_ctor_get(v_x_51_, 0);
v_vs_56_ = lean_ctor_get(v_x_51_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_80_ == 0)
{
v___x_58_ = v_x_51_;
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_vs_56_);
lean_inc(v_ks_55_);
lean_dec(v_x_51_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_array_get_size(v_ks_55_);
v___x_61_ = lean_nat_dec_lt(v_x_52_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
lean_dec(v_x_52_);
v___x_62_ = lean_array_push(v_ks_55_, v_x_53_);
v___x_63_ = lean_array_push(v_vs_56_, v_x_54_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_63_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_65_ = v___x_58_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
else
{
lean_object* v_k_x27_67_; uint8_t v___x_68_; 
v_k_x27_67_ = lean_array_fget_borrowed(v_ks_55_, v_x_52_);
v___x_68_ = l_Lean_instBEqMVarId_beq(v_x_53_, v_k_x27_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_59_ == 0)
{
v___x_70_ = v___x_58_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_ks_55_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_vs_56_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_x_52_, v___x_71_);
lean_dec(v_x_52_);
v_x_51_ = v___x_70_;
v_x_52_ = v___x_72_;
goto _start;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = lean_array_fset(v_ks_55_, v_x_52_, v_x_53_);
v___x_76_ = lean_array_fset(v_vs_56_, v_x_52_, v_x_54_);
lean_dec(v_x_52_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_76_);
lean_ctor_set(v___x_58_, 0, v___x_75_);
v___x_78_ = v___x_58_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_81_, lean_object* v_k_82_, lean_object* v_v_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_81_, v___x_84_, v_k_82_, v_v_83_);
return v___x_85_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_86_ = ((size_t)5ULL);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_shift_left(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; 
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_91_ = lean_usize_sub(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_x_93_, size_t v_x_94_, size_t v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_es_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v_j_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_es_98_ = lean_ctor_get(v_x_93_, 0);
v___x_99_ = ((size_t)5ULL);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_102_ = lean_usize_land(v_x_94_, v___x_101_);
v_j_103_ = lean_usize_to_nat(v___x_102_);
v___x_104_ = lean_array_get_size(v_es_98_);
v___x_105_ = lean_nat_dec_lt(v_j_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec(v_j_103_);
lean_dec(v_x_97_);
lean_dec(v_x_96_);
return v_x_93_;
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_142_; 
lean_inc_ref(v_es_98_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_x_93_, 0);
lean_dec(v_unused_143_);
v___x_107_ = v_x_93_;
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
else
{
lean_dec(v_x_93_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_v_109_; lean_object* v___x_110_; lean_object* v_xs_x27_111_; lean_object* v___y_113_; 
v_v_109_ = lean_array_fget(v_es_98_, v_j_103_);
v___x_110_ = lean_box(0);
v_xs_x27_111_ = lean_array_fset(v_es_98_, v_j_103_, v___x_110_);
switch(lean_obj_tag(v_v_109_))
{
case 0:
{
lean_object* v_key_118_; lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_129_; 
v_key_118_ = lean_ctor_get(v_v_109_, 0);
v_val_119_ = lean_ctor_get(v_v_109_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_129_ == 0)
{
v___x_121_ = v_v_109_;
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_inc(v_key_118_);
lean_dec(v_v_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_instBEqMVarId_beq(v_x_96_, v_key_118_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_del_object(v___x_121_);
v___x_124_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_118_, v_val_119_, v_x_96_, v_x_97_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___y_113_ = v___x_125_;
goto v___jp_112_;
}
else
{
lean_object* v___x_127_; 
lean_dec(v_val_119_);
lean_dec(v_key_118_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_x_97_);
lean_ctor_set(v___x_121_, 0, v_x_96_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_x_96_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_x_97_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v___y_113_ = v___x_127_;
goto v___jp_112_;
}
}
}
}
case 1:
{
lean_object* v_node_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_140_; 
v_node_130_ = lean_ctor_get(v_v_109_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_140_ == 0)
{
v___x_132_ = v_v_109_;
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_node_130_);
lean_dec(v_v_109_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_134_ = lean_usize_shift_right(v_x_94_, v___x_99_);
v___x_135_ = lean_usize_add(v_x_95_, v___x_100_);
v___x_136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_node_130_, v___x_134_, v___x_135_, v_x_96_, v_x_97_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_136_);
v___x_138_ = v___x_132_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v___y_113_ = v___x_138_;
goto v___jp_112_;
}
}
}
default: 
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_x_96_);
lean_ctor_set(v___x_141_, 1, v_x_97_);
v___y_113_ = v___x_141_;
goto v___jp_112_;
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_array_fset(v_xs_x27_111_, v_j_103_, v___y_113_);
lean_dec(v_j_103_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_114_);
v___x_116_ = v___x_107_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
else
{
lean_object* v_ks_144_; lean_object* v_vs_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_165_; 
v_ks_144_ = lean_ctor_get(v_x_93_, 0);
v_vs_145_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_165_ == 0)
{
v___x_147_ = v_x_93_;
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_vs_145_);
lean_inc(v_ks_144_);
lean_dec(v_x_93_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_ks_144_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_vs_145_);
v___x_150_ = v_reuseFailAlloc_164_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v_newNode_151_; uint8_t v___y_153_; size_t v___x_159_; uint8_t v___x_160_; 
v_newNode_151_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v___x_150_, v_x_96_, v_x_97_);
v___x_159_ = ((size_t)7ULL);
v___x_160_ = lean_usize_dec_le(v___x_159_, v_x_95_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_151_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
v___y_153_ = v___x_163_;
goto v___jp_152_;
}
else
{
v___y_153_ = v___x_160_;
goto v___jp_152_;
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
lean_object* v_ks_154_; lean_object* v_vs_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_ks_154_ = lean_ctor_get(v_newNode_151_, 0);
lean_inc_ref(v_ks_154_);
v_vs_155_ = lean_ctor_get(v_newNode_151_, 1);
lean_inc_ref(v_vs_155_);
lean_dec_ref(v_newNode_151_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_95_, v_ks_154_, v_vs_155_, v___x_156_, v___x_157_);
lean_dec_ref(v_vs_155_);
lean_dec_ref(v_ks_154_);
return v___x_158_;
}
else
{
return v_newNode_151_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_166_, lean_object* v_keys_167_, lean_object* v_vals_168_, lean_object* v_i_169_, lean_object* v_entries_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_array_get_size(v_keys_167_);
v___x_172_ = lean_nat_dec_lt(v_i_169_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v_i_169_);
return v_entries_170_;
}
else
{
lean_object* v_k_173_; lean_object* v_v_174_; uint64_t v___x_175_; size_t v_h_176_; size_t v___x_177_; lean_object* v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v_h_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_k_173_ = lean_array_fget_borrowed(v_keys_167_, v_i_169_);
v_v_174_ = lean_array_fget_borrowed(v_vals_168_, v_i_169_);
v___x_175_ = l_Lean_instHashableMVarId_hash(v_k_173_);
v_h_176_ = lean_uint64_to_usize(v___x_175_);
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_sub(v_depth_166_, v___x_179_);
v___x_181_ = lean_usize_mul(v___x_177_, v___x_180_);
v_h_182_ = lean_usize_shift_right(v_h_176_, v___x_181_);
v___x_183_ = lean_nat_add(v_i_169_, v___x_178_);
lean_dec(v_i_169_);
lean_inc(v_v_174_);
lean_inc(v_k_173_);
v___x_184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_entries_170_, v_h_182_, v_depth_166_, v_k_173_, v_v_174_);
v_i_169_ = v___x_183_;
v_entries_170_ = v___x_184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_186_, lean_object* v_keys_187_, lean_object* v_vals_188_, lean_object* v_i_189_, lean_object* v_entries_190_){
_start:
{
size_t v_depth_boxed_191_; lean_object* v_res_192_; 
v_depth_boxed_191_ = lean_unbox_usize(v_depth_186_);
lean_dec(v_depth_186_);
v_res_192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_191_, v_keys_187_, v_vals_188_, v_i_189_, v_entries_190_);
lean_dec_ref(v_vals_188_);
lean_dec_ref(v_keys_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
size_t v_x_4803__boxed_198_; size_t v_x_4804__boxed_199_; lean_object* v_res_200_; 
v_x_4803__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_x_4804__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_res_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_193_, v_x_4803__boxed_198_, v_x_4804__boxed_199_, v_x_196_, v_x_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
uint64_t v___x_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_204_ = l_Lean_instHashableMVarId_hash(v_x_202_);
v___x_205_ = lean_uint64_to_usize(v___x_204_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_201_, v___x_205_, v___x_206_, v_x_202_, v_x_203_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(lean_object* v_mvarId_208_, lean_object* v_val_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_mctx_213_; lean_object* v_cache_214_; lean_object* v_zetaDeltaFVarIds_215_; lean_object* v_postponed_216_; lean_object* v_diag_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_245_; 
v___x_212_ = lean_st_ref_take(v___y_210_);
v_mctx_213_ = lean_ctor_get(v___x_212_, 0);
v_cache_214_ = lean_ctor_get(v___x_212_, 1);
v_zetaDeltaFVarIds_215_ = lean_ctor_get(v___x_212_, 2);
v_postponed_216_ = lean_ctor_get(v___x_212_, 3);
v_diag_217_ = lean_ctor_get(v___x_212_, 4);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_245_ == 0)
{
v___x_219_ = v___x_212_;
v_isShared_220_ = v_isSharedCheck_245_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_diag_217_);
lean_inc(v_postponed_216_);
lean_inc(v_zetaDeltaFVarIds_215_);
lean_inc(v_cache_214_);
lean_inc(v_mctx_213_);
lean_dec(v___x_212_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_245_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_depth_221_; lean_object* v_levelAssignDepth_222_; lean_object* v_lmvarCounter_223_; lean_object* v_mvarCounter_224_; lean_object* v_lDecls_225_; lean_object* v_decls_226_; lean_object* v_userNames_227_; lean_object* v_lAssignment_228_; lean_object* v_eAssignment_229_; lean_object* v_dAssignment_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_244_; 
v_depth_221_ = lean_ctor_get(v_mctx_213_, 0);
v_levelAssignDepth_222_ = lean_ctor_get(v_mctx_213_, 1);
v_lmvarCounter_223_ = lean_ctor_get(v_mctx_213_, 2);
v_mvarCounter_224_ = lean_ctor_get(v_mctx_213_, 3);
v_lDecls_225_ = lean_ctor_get(v_mctx_213_, 4);
v_decls_226_ = lean_ctor_get(v_mctx_213_, 5);
v_userNames_227_ = lean_ctor_get(v_mctx_213_, 6);
v_lAssignment_228_ = lean_ctor_get(v_mctx_213_, 7);
v_eAssignment_229_ = lean_ctor_get(v_mctx_213_, 8);
v_dAssignment_230_ = lean_ctor_get(v_mctx_213_, 9);
v_isSharedCheck_244_ = !lean_is_exclusive(v_mctx_213_);
if (v_isSharedCheck_244_ == 0)
{
v___x_232_ = v_mctx_213_;
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_dAssignment_230_);
lean_inc(v_eAssignment_229_);
lean_inc(v_lAssignment_228_);
lean_inc(v_userNames_227_);
lean_inc(v_decls_226_);
lean_inc(v_lDecls_225_);
lean_inc(v_mvarCounter_224_);
lean_inc(v_lmvarCounter_223_);
lean_inc(v_levelAssignDepth_222_);
lean_inc(v_depth_221_);
lean_dec(v_mctx_213_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(v_eAssignment_229_, v_mvarId_208_, v_val_209_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 8, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_depth_221_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_levelAssignDepth_222_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_lmvarCounter_223_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_mvarCounter_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_lDecls_225_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_decls_226_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_userNames_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v_lAssignment_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 8, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 9, v_dAssignment_230_);
v___x_236_ = v_reuseFailAlloc_243_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_236_);
v___x_238_ = v___x_219_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_cache_214_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_zetaDeltaFVarIds_215_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_postponed_216_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_diag_217_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_st_ref_set(v___y_210_, v___x_238_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_246_, lean_object* v_val_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(v_mvarId_246_, v_val_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0(lean_object* v_fvarId_254_, lean_object* v_mvarId_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; 
lean_inc(v_fvarId_254_);
v___x_261_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_254_, v___y_256_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_427_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_427_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_427_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_427_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_LocalDecl_type(v_a_262_);
lean_dec(v_a_262_);
v___x_272_ = l_Lean_Expr_cleanupAnnotations(v___x_271_);
v___x_273_ = l_Lean_Expr_isApp(v___x_272_);
if (v___x_273_ == 0)
{
lean_dec_ref(v___x_272_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
goto v___jp_266_;
}
else
{
lean_object* v_arg_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_arg_274_ = lean_ctor_get(v___x_272_, 1);
lean_inc_ref(v_arg_274_);
v___x_275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_272_);
v___x_276_ = l_Lean_Expr_isApp(v___x_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v___x_275_);
lean_dec_ref(v_arg_274_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
goto v___jp_266_;
}
else
{
lean_object* v_arg_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_arg_277_ = lean_ctor_get(v___x_275_, 1);
lean_inc_ref(v_arg_277_);
v___x_278_ = l_Lean_Expr_appFnCleanup___redArg(v___x_275_);
v___x_279_ = l_Lean_Expr_isApp(v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v___x_278_);
lean_dec_ref(v_arg_277_);
lean_dec_ref(v_arg_274_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
goto v___jp_266_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_278_);
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1));
v___x_282_ = l_Lean_Expr_isConstOf(v___x_280_, v___x_281_);
lean_dec_ref(v___x_280_);
if (v___x_282_ == 0)
{
lean_dec_ref(v_arg_277_);
lean_dec_ref(v_arg_274_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
goto v___jp_266_;
}
else
{
lean_object* v___x_283_; 
lean_del_object(v___x_264_);
v___x_283_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(v_arg_277_, v___y_259_);
lean_dec_ref(v_arg_277_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_418_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_418_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_418_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_418_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(v_arg_274_, v___y_259_);
lean_dec_ref(v_arg_274_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_409_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_409_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_409_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_409_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
if (lean_obj_tag(v_a_284_) == 1)
{
if (lean_obj_tag(v_a_289_) == 1)
{
lean_object* v_val_398_; lean_object* v_toConstantVal_399_; lean_object* v_val_400_; lean_object* v_toConstantVal_401_; lean_object* v_name_402_; lean_object* v_name_403_; uint8_t v___x_404_; 
lean_del_object(v___x_291_);
v_val_398_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_val_398_);
lean_dec_ref(v_a_284_);
v_toConstantVal_399_ = lean_ctor_get(v_val_398_, 0);
lean_inc_ref(v_toConstantVal_399_);
lean_dec(v_val_398_);
v_val_400_ = lean_ctor_get(v_a_289_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v_a_289_);
v_toConstantVal_401_ = lean_ctor_get(v_val_400_, 0);
lean_inc_ref(v_toConstantVal_401_);
lean_dec(v_val_400_);
v_name_402_ = lean_ctor_get(v_toConstantVal_399_, 0);
lean_inc(v_name_402_);
lean_dec_ref(v_toConstantVal_399_);
v_name_403_ = lean_ctor_get(v_toConstantVal_401_, 0);
lean_inc(v_name_403_);
lean_dec_ref(v_toConstantVal_401_);
v___x_404_ = lean_name_eq(v_name_402_, v_name_403_);
lean_dec(v_name_403_);
lean_dec(v_name_402_);
if (v___x_404_ == 0)
{
if (v___x_282_ == 0)
{
lean_del_object(v___x_286_);
goto v___jp_293_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_407_; 
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v___x_405_ = lean_box(0);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_405_);
v___x_407_ = v___x_286_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_del_object(v___x_286_);
goto v___jp_293_;
}
}
else
{
lean_dec_ref(v_a_284_);
lean_dec(v_a_289_);
lean_del_object(v___x_286_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
goto v___jp_393_;
}
}
else
{
lean_dec(v_a_289_);
lean_del_object(v___x_286_);
lean_dec(v_a_284_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
goto v___jp_393_;
}
v___jp_293_:
{
lean_object* v___x_294_; 
lean_inc(v_mvarId_255_);
v___x_294_ = l_Lean_MVarId_getType(v_mvarId_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
lean_inc(v_fvarId_254_);
v___x_296_ = l_Lean_mkFVar(v_fvarId_254_);
v___x_297_ = l_Lean_Meta_mkNoConfusion(v_a_295_, v___x_296_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_n(v_a_298_, 2);
lean_dec_ref(v___x_297_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
lean_inc(v___y_257_);
lean_inc_ref(v___y_256_);
v___x_299_ = lean_infer_type(v_a_298_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_301_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref(v___x_299_);
v___x_301_ = l_Lean_Meta_whnfD(v_a_300_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_360_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_360_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_360_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_360_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
if (lean_obj_tag(v_a_302_) == 7)
{
lean_object* v_binderType_306_; lean_object* v___x_307_; 
lean_del_object(v___x_304_);
v_binderType_306_ = lean_ctor_get(v_a_302_, 1);
lean_inc_ref(v_binderType_306_);
lean_dec_ref(v_a_302_);
lean_inc(v_mvarId_255_);
v___x_307_ = l_Lean_MVarId_getTag(v_mvarId_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_307_);
v___x_309_ = l_Lean_Expr_headBeta(v_binderType_306_);
v___x_310_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_309_, v_a_308_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_338_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc_n(v_a_311_, 2);
lean_dec_ref(v___x_310_);
v___x_312_ = l_Lean_Expr_app___override(v_a_298_, v_a_311_);
v___x_313_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(v_mvarId_255_, v___x_312_, v___y_257_);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_339_);
v___x_315_ = v___x_313_;
v_isShared_316_ = v_isSharedCheck_338_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___x_313_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_338_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_Lean_Expr_mvarId_x21(v_a_311_);
lean_dec(v_a_311_);
v___x_318_ = l_Lean_MVarId_tryClear(v___x_317_, v_fvarId_254_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_329_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_329_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 0, v_a_319_);
v___x_324_ = v___x_315_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_328_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_324_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_del_object(v___x_315_);
v_a_330_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_318_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_318_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_298_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_340_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_310_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_310_);
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
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_binderType_306_);
lean_dec(v_a_298_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_348_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_307_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_307_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v_a_302_);
lean_dec(v_a_298_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v___x_356_ = lean_box(0);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_356_);
v___x_358_ = v___x_304_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_a_298_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_361_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_301_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_301_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_a_298_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_369_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_299_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_299_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_377_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_297_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_297_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_385_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_294_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_294_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
v___jp_393_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_box(0);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_394_);
v___x_396_ = v___x_291_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_del_object(v___x_286_);
lean_dec(v_a_284_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_410_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_288_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_288_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_arg_274_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_419_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_283_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_283_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
}
v___jp_266_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_mvarId_255_);
lean_dec(v_fvarId_254_);
v_a_428_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_261_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_261_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___boxed(lean_object* v_fvarId_436_, lean_object* v_mvarId_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Grind_injection_x3f___lam__0(v_fvarId_436_, v_mvarId_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object* v_mvarId_444_, lean_object* v_fvarId_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___f_451_; lean_object* v___x_452_; 
lean_inc(v_mvarId_444_);
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_injection_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_451_, 0, v_fvarId_445_);
lean_closure_set(v___f_451_, 1, v_mvarId_444_);
v___x_452_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(v_mvarId_444_, v___f_451_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___boxed(lean_object* v_mvarId_453_, lean_object* v_fvarId_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_453_, v_fvarId_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0(lean_object* v_mvarId_461_, lean_object* v_val_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(v_mvarId_461_, v_val_462_, v___y_464_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___boxed(lean_object* v_mvarId_469_, lean_object* v_val_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0(v_mvarId_469_, v_val_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(v_x_478_, v_x_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, size_t v_x_484_, size_t v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_483_, v_x_484_, v_x_485_, v_x_486_, v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
size_t v_x_5428__boxed_495_; size_t v_x_5429__boxed_496_; lean_object* v_res_497_; 
v_x_5428__boxed_495_ = lean_unbox_usize(v_x_491_);
lean_dec(v_x_491_);
v_x_5429__boxed_496_ = lean_unbox_usize(v_x_492_);
lean_dec(v_x_492_);
v_res_497_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2(v_00_u03b2_489_, v_x_490_, v_x_5428__boxed_495_, v_x_5429__boxed_496_, v_x_493_, v_x_494_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_498_, lean_object* v_n_499_, lean_object* v_k_500_, lean_object* v_v_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_n_499_, v_k_500_, v_v_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_503_, size_t v_depth_504_, lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_heq_507_, lean_object* v_i_508_, lean_object* v_entries_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_504_, v_keys_505_, v_vals_506_, v_i_508_, v_entries_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_511_, lean_object* v_depth_512_, lean_object* v_keys_513_, lean_object* v_vals_514_, lean_object* v_heq_515_, lean_object* v_i_516_, lean_object* v_entries_517_){
_start:
{
size_t v_depth_boxed_518_; lean_object* v_res_519_; 
v_depth_boxed_518_ = lean_unbox_usize(v_depth_512_);
lean_dec(v_depth_512_);
v_res_519_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_511_, v_depth_boxed_518_, v_keys_513_, v_vals_514_, v_heq_515_, v_i_516_, v_entries_517_);
lean_dec_ref(v_vals_514_);
lean_dec_ref(v_keys_513_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_521_, v_x_522_, v_x_523_, v_x_524_);
return v___x_525_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
}
#ifdef __cplusplus
}
#endif
