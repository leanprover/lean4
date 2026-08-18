// Lean compiler output
// Module: Lean.Util.ForEachExprWhere
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
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_ForEachExprWhere_cacheSize;
static const lean_ctor_object l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0 = (const lean_object*)&l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr = (const lean_object*)&l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr___closed__0_value;
static lean_once_cell_t l_Lean_ForEachExprWhere_initCache___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ForEachExprWhere_initCache___closed__0;
static lean_once_cell_t l_Lean_ForEachExprWhere_initCache___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ForEachExprWhere_initCache___closed__1;
static lean_once_cell_t l_Lean_ForEachExprWhere_initCache___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ForEachExprWhere_initCache___closed__2;
static lean_once_cell_t l_Lean_ForEachExprWhere_initCache___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ForEachExprWhere_initCache___closed__3;
static lean_once_cell_t l_Lean_ForEachExprWhere_initCache___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ForEachExprWhere_initCache___closed__4;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_initCache;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0(size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ForEachExprWhere_checked___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExprWhere_checked___redArg___closed__0 = (const lean_object*)&l_Lean_ForEachExprWhere_checked___redArg___closed__0_value;
static const lean_closure_object l_Lean_ForEachExprWhere_checked___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExprWhere_checked___redArg___closed__1 = (const lean_object*)&l_Lean_ForEachExprWhere_checked___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__3(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ForEachExprWhere_visit___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ForEachExprWhere_visit___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t _init_l_Lean_ForEachExprWhere_cacheSize(void){
_start:
{
size_t v___x_1_; 
v___x_1_ = ((size_t)8191ULL);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__0(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = ((lean_object*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr));
v___x_6_ = lean_unsigned_to_nat(8191u);
v___x_7_ = lean_mk_array(v___x_6_, v___x_5_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__1(void){
_start:
{
lean_object* v_cellCount_8_; lean_object* v___x_9_; 
v_cellCount_8_ = lean_unsigned_to_nat(16u);
v___x_9_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__2(void){
_start:
{
lean_object* v_cellCount_10_; lean_object* v___x_11_; 
v_cellCount_10_ = lean_unsigned_to_nat(16u);
v___x_11_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__3(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__2, &l_Lean_ForEachExprWhere_initCache___closed__2_once, _init_l_Lean_ForEachExprWhere_initCache___closed__2);
v___x_13_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__1, &l_Lean_ForEachExprWhere_initCache___closed__1_once, _init_l_Lean_ForEachExprWhere_initCache___closed__1);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_12_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__4(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__3, &l_Lean_ForEachExprWhere_initCache___closed__3_once, _init_l_Lean_ForEachExprWhere_initCache___closed__3);
v___x_17_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__0, &l_Lean_ForEachExprWhere_initCache___closed__0_once, _init_l_Lean_ForEachExprWhere_initCache___closed__0);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__4, &l_Lean_ForEachExprWhere_initCache___closed__4_once, _init_l_Lean_ForEachExprWhere_initCache___closed__4);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0(size_t v___x_20_, lean_object* v_e_21_, lean_object* v_s_22_){
_start:
{
lean_object* v_visited_23_; lean_object* v_checked_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_34_; 
v_visited_23_ = lean_ctor_get(v_s_22_, 0);
v_checked_24_ = lean_ctor_get(v_s_22_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_s_22_);
if (v_isSharedCheck_34_ == 0)
{
v___x_26_ = v_s_22_;
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_checked_24_);
lean_inc(v_visited_23_);
lean_dec(v_s_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_28_ = lean_box(0);
v___x_29_ = lean_array_uset(v_visited_23_, v___x_20_, v_e_21_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_29_);
v___x_31_ = v___x_26_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_checked_24_);
v___x_31_ = v_reuseFailAlloc_33_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; 
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_28_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed(lean_object* v___x_35_, lean_object* v_e_36_, lean_object* v_s_37_){
_start:
{
size_t v___x_322__boxed_38_; lean_object* v_res_39_; 
v___x_322__boxed_38_ = lean_unbox_usize(v___x_35_);
lean_dec(v___x_35_);
v_res_39_ = l_Lean_ForEachExprWhere_visited___redArg___lam__0(v___x_322__boxed_38_, v_e_36_, v_s_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1(lean_object* v_toApplicative_40_, uint8_t v___x_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_toPure_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_toPure_43_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_inc(v_toPure_43_);
lean_dec_ref(v_toApplicative_40_);
v___x_44_ = lean_box(v___x_41_);
v___x_45_ = lean_apply_2(v_toPure_43_, lean_box(0), v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed(lean_object* v_toApplicative_46_, lean_object* v___x_47_, lean_object* v_a_48_){
_start:
{
uint8_t v___x_345__boxed_49_; lean_object* v_res_50_; 
v___x_345__boxed_49_ = lean_unbox(v___x_47_);
v_res_50_ = l_Lean_ForEachExprWhere_visited___redArg___lam__1(v_toApplicative_46_, v___x_345__boxed_49_, v_a_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2(lean_object* v_e_51_, lean_object* v_toApplicative_52_, lean_object* v_a_53_, lean_object* v_inst_54_, lean_object* v_toBind_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_visited_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; size_t v___x_62_; uint8_t v___x_63_; 
v_visited_57_ = lean_ctor_get(v_a_56_, 0);
v___x_58_ = lean_ptr_addr(v_e_51_);
v___x_59_ = ((size_t)8191ULL);
v___x_60_ = lean_usize_mod(v___x_58_, v___x_59_);
v___x_61_ = lean_array_uget_borrowed(v_visited_57_, v___x_60_);
v___x_62_ = lean_ptr_addr(v___x_61_);
v___x_63_ = lean_usize_dec_eq(v___x_62_, v___x_58_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_64_ = lean_box_usize(v___x_60_);
v___f_65_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_65_, 0, v___x_64_);
lean_closure_set(v___f_65_, 1, v_e_51_);
v___x_66_ = lean_box(v___x_63_);
v___f_67_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_67_, 0, v_toApplicative_52_);
lean_closure_set(v___f_67_, 1, v___x_66_);
lean_inc(v_a_53_);
v___x_68_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_68_, 0, lean_box(0));
lean_closure_set(v___x_68_, 1, lean_box(0));
lean_closure_set(v___x_68_, 2, lean_box(0));
lean_closure_set(v___x_68_, 3, v_a_53_);
lean_closure_set(v___x_68_, 4, v___f_65_);
v___x_69_ = lean_apply_2(v_inst_54_, lean_box(0), v___x_68_);
v___x_70_ = lean_apply_4(v_toBind_55_, lean_box(0), lean_box(0), v___x_69_, v___f_67_);
return v___x_70_;
}
else
{
lean_object* v_toPure_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_toBind_55_);
lean_dec(v_inst_54_);
lean_dec_ref(v_e_51_);
v_toPure_71_ = lean_ctor_get(v_toApplicative_52_, 1);
lean_inc(v_toPure_71_);
lean_dec_ref(v_toApplicative_52_);
v___x_72_ = lean_box(v___x_63_);
v___x_73_ = lean_apply_2(v_toPure_71_, lean_box(0), v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed(lean_object* v_e_74_, lean_object* v_toApplicative_75_, lean_object* v_a_76_, lean_object* v_inst_77_, lean_object* v_toBind_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_ForEachExprWhere_visited___redArg___lam__2(v_e_74_, v_toApplicative_75_, v_a_76_, v_inst_77_, v_toBind_78_, v_a_79_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg(lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_e_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_toApplicative_85_; lean_object* v_toBind_86_; lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_toApplicative_85_ = lean_ctor_get(v_inst_82_, 0);
lean_inc_ref(v_toApplicative_85_);
v_toBind_86_ = lean_ctor_get(v_inst_82_, 1);
lean_inc_n(v_toBind_86_, 2);
lean_dec_ref(v_inst_82_);
lean_inc(v_inst_81_);
lean_inc_n(v_a_84_, 2);
v___f_87_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_87_, 0, v_e_83_);
lean_closure_set(v___f_87_, 1, v_toApplicative_85_);
lean_closure_set(v___f_87_, 2, v_a_84_);
lean_closure_set(v___f_87_, 3, v_inst_81_);
lean_closure_set(v___f_87_, 4, v_toBind_86_);
v___x_88_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_88_, 0, lean_box(0));
lean_closure_set(v___x_88_, 1, lean_box(0));
lean_closure_set(v___x_88_, 2, v_a_84_);
v___x_89_ = lean_apply_2(v_inst_81_, lean_box(0), v___x_88_);
v___x_90_ = lean_apply_4(v_toBind_86_, lean_box(0), lean_box(0), v___x_89_, v___f_87_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___boxed(lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_e_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_91_, v_inst_92_, v_e_93_, v_a_94_);
lean_dec(v_a_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited(lean_object* v_00_u03c9_96_, lean_object* v_m_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_e_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_99_, v_inst_100_, v_e_101_, v_a_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___boxed(lean_object* v_00_u03c9_104_, lean_object* v_m_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_e_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_ForEachExprWhere_visited(v_00_u03c9_104_, v_m_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_e_109_, v_a_110_);
lean_dec(v_a_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__0(lean_object* v___x_112_, lean_object* v___x_113_, lean_object* v_e_114_, lean_object* v_s_115_){
_start:
{
lean_object* v_visited_116_; lean_object* v_checked_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_189_; 
v_visited_116_ = lean_ctor_get(v_s_115_, 0);
v_checked_117_ = lean_ctor_get(v_s_115_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_s_115_);
if (v_isSharedCheck_189_ == 0)
{
v___x_119_ = v_s_115_;
v_isShared_120_ = v_isSharedCheck_189_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_checked_117_);
lean_inc(v_visited_116_);
lean_dec(v_s_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_189_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___y_123_; lean_object* v___y_129_; lean_object* v_i_130_; lean_object* v___y_136_; lean_object* v___y_146_; lean_object* v_i_147_; lean_object* v___x_162_; 
v___x_121_ = lean_box(0);
lean_inc_ref(v_e_114_);
lean_inc_ref(v___x_113_);
lean_inc_ref(v___x_112_);
v___x_162_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_112_, v___x_113_, v_checked_117_, v_e_114_);
switch(lean_obj_tag(v___x_162_))
{
case 0:
{
lean_dec_ref_known(v___x_162_, 3);
lean_dec_ref(v_e_114_);
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_112_);
v___y_123_ = v_checked_117_;
goto v___jp_122_;
}
case 1:
{
lean_object* v_index_163_; lean_object* v_size_164_; lean_object* v_keyArray_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_index_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_index_163_);
lean_dec_ref_known(v___x_162_, 1);
v_size_164_ = lean_ctor_get(v_checked_117_, 0);
v_keyArray_165_ = lean_ctor_get(v_checked_117_, 1);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_size_164_, v___x_166_);
v___x_168_ = lean_array_get_size(v_keyArray_165_);
v___x_169_ = lean_nat_dec_lt(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_dec(v___x_167_);
lean_dec(v_index_163_);
goto v___jp_152_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_170_ = lean_unsigned_to_nat(4u);
v___x_171_ = lean_nat_mul(v___x_167_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(3u);
v___x_173_ = lean_nat_mul(v___x_168_, v___x_172_);
v___x_174_ = lean_nat_dec_le(v___x_171_, v___x_173_);
lean_dec(v___x_173_);
lean_dec(v___x_171_);
if (v___x_174_ == 0)
{
lean_dec(v___x_167_);
lean_dec(v_index_163_);
goto v___jp_152_;
}
else
{
lean_object* v___x_175_; 
lean_dec_ref(v___x_113_);
lean_dec_ref(v___x_112_);
v___x_175_ = l_Std_DHashMap_Raw_setEntry___redArg(v_checked_117_, v___x_167_, v_index_163_, v_e_114_, v___x_121_);
lean_dec(v_index_163_);
v___y_123_ = v___x_175_;
goto v___jp_122_;
}
}
}
default: 
{
lean_object* v_size_176_; lean_object* v_keyArray_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_size_176_ = lean_ctor_get(v_checked_117_, 0);
v_keyArray_177_ = lean_ctor_get(v_checked_117_, 1);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_size_176_, v___x_178_);
v___x_180_ = lean_array_get_size(v_keyArray_177_);
v___x_181_ = lean_nat_dec_lt(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v___x_179_);
lean_inc_ref(v___x_113_);
lean_inc_ref(v___x_112_);
v___x_182_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_112_, v___x_113_, v_checked_117_);
v___y_136_ = v___x_182_;
goto v___jp_135_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_183_ = lean_unsigned_to_nat(4u);
v___x_184_ = lean_nat_mul(v___x_179_, v___x_183_);
lean_dec(v___x_179_);
v___x_185_ = lean_unsigned_to_nat(3u);
v___x_186_ = lean_nat_mul(v___x_180_, v___x_185_);
v___x_187_ = lean_nat_dec_le(v___x_184_, v___x_186_);
lean_dec(v___x_186_);
lean_dec(v___x_184_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
lean_inc_ref(v___x_113_);
lean_inc_ref(v___x_112_);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_112_, v___x_113_, v_checked_117_);
v___y_136_ = v___x_188_;
goto v___jp_135_;
}
else
{
v___y_136_ = v_checked_117_;
goto v___jp_135_;
}
}
}
}
v___jp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___y_123_);
v___x_125_ = v___x_119_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_visited_116_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___y_123_);
v___x_125_ = v_reuseFailAlloc_127_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_121_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
return v___x_126_;
}
}
v___jp_128_:
{
lean_object* v_size_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_size_131_ = lean_ctor_get(v___y_129_, 0);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_size_131_, v___x_132_);
v___x_134_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_129_, v___x_133_, v_i_130_, v_e_114_, v___x_121_);
lean_dec(v_i_130_);
v___y_123_ = v___x_134_;
goto v___jp_122_;
}
v___jp_135_:
{
lean_object* v___x_137_; 
lean_inc_ref(v_e_114_);
v___x_137_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_112_, v___x_113_, v___y_136_, v_e_114_);
switch(lean_obj_tag(v___x_137_))
{
case 0:
{
lean_object* v_index_138_; lean_object* v_size_139_; lean_object* v___x_140_; 
v_index_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_index_138_);
lean_dec_ref_known(v___x_137_, 3);
v_size_139_ = lean_ctor_get(v___y_136_, 0);
lean_inc(v_size_139_);
v___x_140_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_136_, v_size_139_, v_index_138_, v_e_114_, v___x_121_);
lean_dec(v_index_138_);
v___y_123_ = v___x_140_;
goto v___jp_122_;
}
case 1:
{
lean_object* v_index_141_; 
v_index_141_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_index_141_);
lean_dec_ref_known(v___x_137_, 1);
v___y_129_ = v___y_136_;
v_i_130_ = v_index_141_;
goto v___jp_128_;
}
default: 
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_136_, v___x_142_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_index_144_; 
v_index_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_index_144_);
lean_dec_ref_known(v___x_143_, 1);
v___y_129_ = v___y_136_;
v_i_130_ = v_index_144_;
goto v___jp_128_;
}
else
{
lean_dec_ref(v_e_114_);
v___y_123_ = v___y_136_;
goto v___jp_122_;
}
}
}
}
v___jp_145_:
{
lean_object* v_size_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_size_148_ = lean_ctor_get(v___y_146_, 0);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_add(v_size_148_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_146_, v___x_150_, v_i_147_, v_e_114_, v___x_121_);
lean_dec(v_i_147_);
v___y_123_ = v___x_151_;
goto v___jp_122_;
}
v___jp_152_:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_inc_ref(v___x_113_);
lean_inc_ref(v___x_112_);
v___x_153_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_112_, v___x_113_, v_checked_117_);
lean_inc_ref(v_e_114_);
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_112_, v___x_113_, v___x_153_, v_e_114_);
switch(lean_obj_tag(v___x_154_))
{
case 0:
{
lean_object* v_index_155_; lean_object* v_size_156_; lean_object* v___x_157_; 
v_index_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_index_155_);
lean_dec_ref_known(v___x_154_, 3);
v_size_156_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_size_156_);
v___x_157_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_153_, v_size_156_, v_index_155_, v_e_114_, v___x_121_);
lean_dec(v_index_155_);
v___y_123_ = v___x_157_;
goto v___jp_122_;
}
case 1:
{
lean_object* v_index_158_; 
v_index_158_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_index_158_);
lean_dec_ref_known(v___x_154_, 1);
v___y_146_ = v___x_153_;
v_i_147_ = v_index_158_;
goto v___jp_145_;
}
default: 
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_153_, v___x_159_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_index_161_; 
v_index_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_index_161_);
lean_dec_ref_known(v___x_160_, 1);
v___y_146_ = v___x_153_;
v_i_147_ = v_index_161_;
goto v___jp_145_;
}
else
{
lean_dec_ref(v_e_114_);
v___y_123_ = v___x_153_;
goto v___jp_122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1(lean_object* v_toApplicative_190_, uint8_t v___x_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_toPure_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_toPure_193_ = lean_ctor_get(v_toApplicative_190_, 1);
lean_inc(v_toPure_193_);
lean_dec_ref(v_toApplicative_190_);
v___x_194_ = lean_box(v___x_191_);
v___x_195_ = lean_apply_2(v_toPure_193_, lean_box(0), v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed(lean_object* v_toApplicative_196_, lean_object* v___x_197_, lean_object* v_a_198_){
_start:
{
uint8_t v___x_1004__boxed_199_; lean_object* v_res_200_; 
v___x_1004__boxed_199_ = lean_unbox(v___x_197_);
v_res_200_ = l_Lean_ForEachExprWhere_checked___redArg___lam__1(v_toApplicative_196_, v___x_1004__boxed_199_, v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2(lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_e_203_, lean_object* v_toApplicative_204_, lean_object* v_a_205_, lean_object* v___f_206_, lean_object* v_inst_207_, lean_object* v_toBind_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_checked_210_; uint8_t v___x_211_; 
v_checked_210_ = lean_ctor_get(v_a_209_, 1);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_201_, v___x_202_, v_checked_210_, v_e_203_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_212_ = lean_box(v___x_211_);
v___f_213_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_213_, 0, v_toApplicative_204_);
lean_closure_set(v___f_213_, 1, v___x_212_);
lean_inc(v_a_205_);
v___x_214_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_214_, 0, lean_box(0));
lean_closure_set(v___x_214_, 1, lean_box(0));
lean_closure_set(v___x_214_, 2, lean_box(0));
lean_closure_set(v___x_214_, 3, v_a_205_);
lean_closure_set(v___x_214_, 4, v___f_206_);
v___x_215_ = lean_apply_2(v_inst_207_, lean_box(0), v___x_214_);
v___x_216_ = lean_apply_4(v_toBind_208_, lean_box(0), lean_box(0), v___x_215_, v___f_213_);
return v___x_216_;
}
else
{
lean_object* v_toPure_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_toBind_208_);
lean_dec(v_inst_207_);
lean_dec_ref(v___f_206_);
v_toPure_217_ = lean_ctor_get(v_toApplicative_204_, 1);
lean_inc(v_toPure_217_);
lean_dec_ref(v_toApplicative_204_);
v___x_218_ = lean_box(v___x_211_);
v___x_219_ = lean_apply_2(v_toPure_217_, lean_box(0), v___x_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed(lean_object* v___x_220_, lean_object* v___x_221_, lean_object* v_e_222_, lean_object* v_toApplicative_223_, lean_object* v_a_224_, lean_object* v___f_225_, lean_object* v_inst_226_, lean_object* v_toBind_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_ForEachExprWhere_checked___redArg___lam__2(v___x_220_, v___x_221_, v_e_222_, v_toApplicative_223_, v_a_224_, v___f_225_, v_inst_226_, v_toBind_227_, v_a_228_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg(lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_e_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_toApplicative_236_; lean_object* v_toBind_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___f_240_; lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_toApplicative_236_ = lean_ctor_get(v_inst_233_, 0);
lean_inc_ref(v_toApplicative_236_);
v_toBind_237_ = lean_ctor_get(v_inst_233_, 1);
lean_inc_n(v_toBind_237_, 2);
lean_dec_ref(v_inst_233_);
v___x_238_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__0));
v___x_239_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__1));
lean_inc_ref(v_e_234_);
v___f_240_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__0), 4, 3);
lean_closure_set(v___f_240_, 0, v___x_238_);
lean_closure_set(v___f_240_, 1, v___x_239_);
lean_closure_set(v___f_240_, 2, v_e_234_);
lean_inc(v_inst_232_);
lean_inc_n(v_a_235_, 2);
v___f_241_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_241_, 0, v___x_238_);
lean_closure_set(v___f_241_, 1, v___x_239_);
lean_closure_set(v___f_241_, 2, v_e_234_);
lean_closure_set(v___f_241_, 3, v_toApplicative_236_);
lean_closure_set(v___f_241_, 4, v_a_235_);
lean_closure_set(v___f_241_, 5, v___f_240_);
lean_closure_set(v___f_241_, 6, v_inst_232_);
lean_closure_set(v___f_241_, 7, v_toBind_237_);
v___x_242_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, lean_box(0));
lean_closure_set(v___x_242_, 2, v_a_235_);
v___x_243_ = lean_apply_2(v_inst_232_, lean_box(0), v___x_242_);
v___x_244_ = lean_apply_4(v_toBind_237_, lean_box(0), lean_box(0), v___x_243_, v___f_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___boxed(lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_e_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_245_, v_inst_246_, v_e_247_, v_a_248_);
lean_dec(v_a_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked(lean_object* v_00_u03c9_250_, lean_object* v_m_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_e_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_253_, v_inst_254_, v_e_255_, v_a_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___boxed(lean_object* v_00_u03c9_258_, lean_object* v_m_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_e_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_ForEachExprWhere_checked(v_00_u03c9_258_, v_m_259_, v_inst_260_, v_inst_261_, v_inst_262_, v_e_263_, v_a_264_);
lean_dec(v_a_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(lean_object* v_p_266_, lean_object* v_e_267_, lean_object* v___f_268_, lean_object* v_a_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_toBind_272_, lean_object* v___f_273_, lean_object* v_toApplicative_274_, uint8_t v_a_275_){
_start:
{
if (v_a_275_ == 0)
{
lean_object* v___x_276_; uint8_t v___x_277_; 
lean_dec_ref(v_toApplicative_274_);
lean_inc_ref(v_e_267_);
v___x_276_ = lean_apply_1(v_p_266_, v_e_267_);
v___x_277_ = lean_unbox(v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v___f_273_);
lean_dec(v_toBind_272_);
lean_dec_ref(v_inst_271_);
lean_dec(v_inst_270_);
lean_dec_ref(v_e_267_);
v___x_278_ = lean_box(0);
lean_inc(v_a_269_);
v___x_279_ = lean_apply_2(v___f_268_, v___x_278_, v_a_269_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v___f_268_);
v___x_280_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_270_, v_inst_271_, v_e_267_, v_a_269_);
v___x_281_ = lean_apply_4(v_toBind_272_, lean_box(0), lean_box(0), v___x_280_, v___f_273_);
return v___x_281_;
}
}
else
{
lean_object* v_toPure_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v___f_273_);
lean_dec(v_toBind_272_);
lean_dec_ref(v_inst_271_);
lean_dec(v_inst_270_);
lean_dec(v___f_268_);
lean_dec_ref(v_e_267_);
lean_dec_ref(v_p_266_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_274_, 1);
lean_inc(v_toPure_282_);
lean_dec_ref(v_toApplicative_274_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_apply_2(v_toPure_282_, lean_box(0), v___x_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed(lean_object* v_p_285_, lean_object* v_e_286_, lean_object* v___f_287_, lean_object* v_a_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_toBind_291_, lean_object* v___f_292_, lean_object* v_toApplicative_293_, lean_object* v_a_294_){
_start:
{
uint8_t v_a_boxed_295_; lean_object* v_res_296_; 
v_a_boxed_295_ = lean_unbox(v_a_294_);
v_res_296_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(v_p_285_, v_e_286_, v___f_287_, v_a_288_, v_inst_289_, v_inst_290_, v_toBind_291_, v___f_292_, v_toApplicative_293_, v_a_boxed_295_);
lean_dec(v_a_288_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(uint8_t v_stopWhenVisited_297_, lean_object* v___f_298_, lean_object* v_a_299_, lean_object* v_toApplicative_300_, lean_object* v_a_301_){
_start:
{
if (v_stopWhenVisited_297_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_toApplicative_300_);
v___x_302_ = lean_box(0);
lean_inc(v_a_299_);
v___x_303_ = lean_apply_2(v___f_298_, v___x_302_, v_a_299_);
return v___x_303_;
}
else
{
lean_object* v_toPure_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v___f_298_);
v_toPure_304_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc(v_toPure_304_);
lean_dec_ref(v_toApplicative_300_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_2(v_toPure_304_, lean_box(0), v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed(lean_object* v_stopWhenVisited_307_, lean_object* v___f_308_, lean_object* v_a_309_, lean_object* v_toApplicative_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_stopWhenVisited_boxed_312_; lean_object* v_res_313_; 
v_stopWhenVisited_boxed_312_ = lean_unbox(v_stopWhenVisited_307_);
v_res_313_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(v_stopWhenVisited_boxed_312_, v___f_308_, v_a_309_, v_toApplicative_310_, v_a_311_);
lean_dec(v_a_309_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(lean_object* v_f_314_, lean_object* v_e_315_, lean_object* v_toBind_316_, lean_object* v___f_317_, lean_object* v___f_318_, lean_object* v_a_319_, uint8_t v_a_320_){
_start:
{
if (v_a_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v___f_318_);
v___x_321_ = lean_apply_1(v_f_314_, v_e_315_);
v___x_322_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_321_, v___f_317_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v___f_317_);
lean_dec(v_toBind_316_);
lean_dec_ref(v_e_315_);
lean_dec(v_f_314_);
v___x_323_ = lean_box(0);
lean_inc(v_a_319_);
v___x_324_ = lean_apply_2(v___f_318_, v___x_323_, v_a_319_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed(lean_object* v_f_325_, lean_object* v_e_326_, lean_object* v_toBind_327_, lean_object* v___f_328_, lean_object* v___f_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
uint8_t v_a_boxed_332_; lean_object* v_res_333_; 
v_a_boxed_332_ = lean_unbox(v_a_331_);
v_res_333_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(v_f_325_, v_e_326_, v_toBind_327_, v___f_328_, v___f_329_, v_a_330_, v_a_boxed_332_);
lean_dec(v_a_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed(lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_p_336_, lean_object* v_f_337_, lean_object* v_stopWhenVisited_338_, lean_object* v_b_339_, lean_object* v___y_340_, lean_object* v_a_341_){
_start:
{
uint8_t v_stopWhenVisited_boxed_342_; lean_object* v_res_343_; 
v_stopWhenVisited_boxed_342_ = lean_unbox(v_stopWhenVisited_338_);
v_res_343_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(v_inst_334_, v_inst_335_, v_p_336_, v_f_337_, v_stopWhenVisited_boxed_342_, v_b_339_, v___y_340_, v_a_341_);
lean_dec(v___y_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_p_346_, lean_object* v_f_347_, uint8_t v_stopWhenVisited_348_, lean_object* v_body_349_, lean_object* v___y_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_344_, v_inst_345_, v_p_346_, v_f_347_, v_stopWhenVisited_348_, v_body_349_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed(lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_p_355_, lean_object* v_f_356_, lean_object* v_stopWhenVisited_357_, lean_object* v_body_358_, lean_object* v___y_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_stopWhenVisited_boxed_361_; lean_object* v_res_362_; 
v_stopWhenVisited_boxed_361_ = lean_unbox(v_stopWhenVisited_357_);
v_res_362_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(v_inst_353_, v_inst_354_, v_p_355_, v_f_356_, v_stopWhenVisited_boxed_361_, v_body_358_, v___y_359_, v_a_360_);
lean_dec(v___y_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_p_365_, lean_object* v_f_366_, uint8_t v_stopWhenVisited_367_, lean_object* v_value_368_, lean_object* v___y_369_, lean_object* v_toBind_370_, lean_object* v___f_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_363_, v_inst_364_, v_p_365_, v_f_366_, v_stopWhenVisited_367_, v_value_368_, v___y_369_);
v___x_374_ = lean_apply_4(v_toBind_370_, lean_box(0), lean_box(0), v___x_373_, v___f_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed(lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_p_377_, lean_object* v_f_378_, lean_object* v_stopWhenVisited_379_, lean_object* v_value_380_, lean_object* v___y_381_, lean_object* v_toBind_382_, lean_object* v___f_383_, lean_object* v_a_384_){
_start:
{
uint8_t v_stopWhenVisited_boxed_385_; lean_object* v_res_386_; 
v_stopWhenVisited_boxed_385_ = lean_unbox(v_stopWhenVisited_379_);
v_res_386_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(v_inst_375_, v_inst_376_, v_p_377_, v_f_378_, v_stopWhenVisited_boxed_385_, v_value_380_, v___y_381_, v_toBind_382_, v___f_383_, v_a_384_);
lean_dec(v___y_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_p_389_, lean_object* v_f_390_, uint8_t v_stopWhenVisited_391_, lean_object* v_arg_392_, lean_object* v___y_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_387_, v_inst_388_, v_p_389_, v_f_390_, v_stopWhenVisited_391_, v_arg_392_, v___y_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_p_398_, lean_object* v_f_399_, lean_object* v_stopWhenVisited_400_, lean_object* v_arg_401_, lean_object* v___y_402_, lean_object* v_a_403_){
_start:
{
uint8_t v_stopWhenVisited_boxed_404_; lean_object* v_res_405_; 
v_stopWhenVisited_boxed_404_ = lean_unbox(v_stopWhenVisited_400_);
v_res_405_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(v_inst_396_, v_inst_397_, v_p_398_, v_f_399_, v_stopWhenVisited_boxed_404_, v_arg_401_, v___y_402_, v_a_403_);
lean_dec(v___y_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_p_408_, lean_object* v_f_409_, uint8_t v_stopWhenVisited_410_, lean_object* v_toBind_411_, lean_object* v_e_412_, lean_object* v_toApplicative_413_, lean_object* v_____r_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_d_417_; lean_object* v_b_418_; 
switch(lean_obj_tag(v_e_412_))
{
case 7:
{
lean_object* v_binderType_423_; lean_object* v_body_424_; 
lean_dec_ref(v_toApplicative_413_);
v_binderType_423_ = lean_ctor_get(v_e_412_, 1);
lean_inc_ref(v_binderType_423_);
v_body_424_ = lean_ctor_get(v_e_412_, 2);
lean_inc_ref(v_body_424_);
lean_dec_ref_known(v_e_412_, 3);
v_d_417_ = v_binderType_423_;
v_b_418_ = v_body_424_;
goto v___jp_416_;
}
case 6:
{
lean_object* v_binderType_425_; lean_object* v_body_426_; 
lean_dec_ref(v_toApplicative_413_);
v_binderType_425_ = lean_ctor_get(v_e_412_, 1);
lean_inc_ref(v_binderType_425_);
v_body_426_ = lean_ctor_get(v_e_412_, 2);
lean_inc_ref(v_body_426_);
lean_dec_ref_known(v_e_412_, 3);
v_d_417_ = v_binderType_425_;
v_b_418_ = v_body_426_;
goto v___jp_416_;
}
case 8:
{
lean_object* v_type_427_; lean_object* v_value_428_; lean_object* v_body_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v_toApplicative_413_);
v_type_427_ = lean_ctor_get(v_e_412_, 1);
lean_inc_ref(v_type_427_);
v_value_428_ = lean_ctor_get(v_e_412_, 2);
lean_inc_ref(v_value_428_);
v_body_429_ = lean_ctor_get(v_e_412_, 3);
lean_inc_ref(v_body_429_);
lean_dec_ref_known(v_e_412_, 4);
v___x_430_ = lean_box(v_stopWhenVisited_410_);
lean_inc_n(v___y_415_, 2);
lean_inc_n(v_f_409_, 2);
lean_inc_ref_n(v_p_408_, 2);
lean_inc_ref_n(v_inst_407_, 2);
lean_inc_n(v_inst_406_, 2);
v___f_431_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_431_, 0, v_inst_406_);
lean_closure_set(v___f_431_, 1, v_inst_407_);
lean_closure_set(v___f_431_, 2, v_p_408_);
lean_closure_set(v___f_431_, 3, v_f_409_);
lean_closure_set(v___f_431_, 4, v___x_430_);
lean_closure_set(v___f_431_, 5, v_body_429_);
lean_closure_set(v___f_431_, 6, v___y_415_);
v___x_432_ = lean_box(v_stopWhenVisited_410_);
lean_inc(v_toBind_411_);
v___f_433_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_433_, 0, v_inst_406_);
lean_closure_set(v___f_433_, 1, v_inst_407_);
lean_closure_set(v___f_433_, 2, v_p_408_);
lean_closure_set(v___f_433_, 3, v_f_409_);
lean_closure_set(v___f_433_, 4, v___x_432_);
lean_closure_set(v___f_433_, 5, v_value_428_);
lean_closure_set(v___f_433_, 6, v___y_415_);
lean_closure_set(v___f_433_, 7, v_toBind_411_);
lean_closure_set(v___f_433_, 8, v___f_431_);
v___x_434_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_406_, v_inst_407_, v_p_408_, v_f_409_, v_stopWhenVisited_410_, v_type_427_, v___y_415_);
v___x_435_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v___x_434_, v___f_433_);
return v___x_435_;
}
case 5:
{
lean_object* v_fn_436_; lean_object* v_arg_437_; lean_object* v___x_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec_ref(v_toApplicative_413_);
v_fn_436_ = lean_ctor_get(v_e_412_, 0);
lean_inc_ref(v_fn_436_);
v_arg_437_ = lean_ctor_get(v_e_412_, 1);
lean_inc_ref(v_arg_437_);
lean_dec_ref_known(v_e_412_, 2);
v___x_438_ = lean_box(v_stopWhenVisited_410_);
lean_inc(v___y_415_);
lean_inc(v_f_409_);
lean_inc_ref(v_p_408_);
lean_inc_ref(v_inst_407_);
lean_inc(v_inst_406_);
v___f_439_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_439_, 0, v_inst_406_);
lean_closure_set(v___f_439_, 1, v_inst_407_);
lean_closure_set(v___f_439_, 2, v_p_408_);
lean_closure_set(v___f_439_, 3, v_f_409_);
lean_closure_set(v___f_439_, 4, v___x_438_);
lean_closure_set(v___f_439_, 5, v_arg_437_);
lean_closure_set(v___f_439_, 6, v___y_415_);
v___x_440_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_406_, v_inst_407_, v_p_408_, v_f_409_, v_stopWhenVisited_410_, v_fn_436_, v___y_415_);
v___x_441_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v___x_440_, v___f_439_);
return v___x_441_;
}
case 10:
{
lean_object* v_expr_442_; lean_object* v___x_443_; 
lean_dec_ref(v_toApplicative_413_);
lean_dec(v_toBind_411_);
v_expr_442_ = lean_ctor_get(v_e_412_, 1);
lean_inc_ref(v_expr_442_);
lean_dec_ref_known(v_e_412_, 2);
v___x_443_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_406_, v_inst_407_, v_p_408_, v_f_409_, v_stopWhenVisited_410_, v_expr_442_, v___y_415_);
return v___x_443_;
}
case 11:
{
lean_object* v_struct_444_; lean_object* v___x_445_; 
lean_dec_ref(v_toApplicative_413_);
lean_dec(v_toBind_411_);
v_struct_444_ = lean_ctor_get(v_e_412_, 2);
lean_inc_ref(v_struct_444_);
lean_dec_ref_known(v_e_412_, 3);
v___x_445_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_406_, v_inst_407_, v_p_408_, v_f_409_, v_stopWhenVisited_410_, v_struct_444_, v___y_415_);
return v___x_445_;
}
default: 
{
lean_object* v_toPure_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v_e_412_);
lean_dec(v_toBind_411_);
lean_dec(v_f_409_);
lean_dec_ref(v_p_408_);
lean_dec_ref(v_inst_407_);
lean_dec(v_inst_406_);
v_toPure_446_ = lean_ctor_get(v_toApplicative_413_, 1);
lean_inc(v_toPure_446_);
lean_dec_ref(v_toApplicative_413_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_apply_2(v_toPure_446_, lean_box(0), v___x_447_);
return v___x_448_;
}
}
v___jp_416_:
{
lean_object* v___x_419_; lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_box(v_stopWhenVisited_410_);
lean_inc(v___y_415_);
lean_inc(v_f_409_);
lean_inc_ref(v_p_408_);
lean_inc_ref(v_inst_407_);
lean_inc(v_inst_406_);
v___f_420_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_420_, 0, v_inst_406_);
lean_closure_set(v___f_420_, 1, v_inst_407_);
lean_closure_set(v___f_420_, 2, v_p_408_);
lean_closure_set(v___f_420_, 3, v_f_409_);
lean_closure_set(v___f_420_, 4, v___x_419_);
lean_closure_set(v___f_420_, 5, v_b_418_);
lean_closure_set(v___f_420_, 6, v___y_415_);
v___x_421_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_406_, v_inst_407_, v_p_408_, v_f_409_, v_stopWhenVisited_410_, v_d_417_, v___y_415_);
v___x_422_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v___x_421_, v___f_420_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed(lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_p_451_, lean_object* v_f_452_, lean_object* v_stopWhenVisited_453_, lean_object* v_toBind_454_, lean_object* v_e_455_, lean_object* v_toApplicative_456_, lean_object* v_____r_457_, lean_object* v___y_458_){
_start:
{
uint8_t v_stopWhenVisited_boxed_459_; lean_object* v_res_460_; 
v_stopWhenVisited_boxed_459_ = lean_unbox(v_stopWhenVisited_453_);
v_res_460_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(v_inst_449_, v_inst_450_, v_p_451_, v_f_452_, v_stopWhenVisited_boxed_459_, v_toBind_454_, v_e_455_, v_toApplicative_456_, v_____r_457_, v___y_458_);
lean_dec(v___y_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_p_463_, lean_object* v_f_464_, uint8_t v_stopWhenVisited_465_, lean_object* v_e_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_toApplicative_468_; lean_object* v_toBind_469_; lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___f_474_; lean_object* v___f_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_toApplicative_468_ = lean_ctor_get(v_inst_462_, 0);
v_toBind_469_ = lean_ctor_get(v_inst_462_, 1);
lean_inc_n(v_toBind_469_, 4);
v___x_470_ = lean_box(v_stopWhenVisited_465_);
lean_inc_ref_n(v_toApplicative_468_, 3);
lean_inc_ref_n(v_e_466_, 3);
lean_inc(v_f_464_);
lean_inc_ref(v_p_463_);
lean_inc_ref_n(v_inst_462_, 2);
lean_inc_n(v_inst_461_, 2);
v___f_471_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_471_, 0, v_inst_461_);
lean_closure_set(v___f_471_, 1, v_inst_462_);
lean_closure_set(v___f_471_, 2, v_p_463_);
lean_closure_set(v___f_471_, 3, v_f_464_);
lean_closure_set(v___f_471_, 4, v___x_470_);
lean_closure_set(v___f_471_, 5, v_toBind_469_);
lean_closure_set(v___f_471_, 6, v_e_466_);
lean_closure_set(v___f_471_, 7, v_toApplicative_468_);
v___x_472_ = lean_box(v_stopWhenVisited_465_);
lean_inc_n(v_a_467_, 3);
lean_inc_ref_n(v___f_471_, 2);
v___f_473_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed), 5, 4);
lean_closure_set(v___f_473_, 0, v___x_472_);
lean_closure_set(v___f_473_, 1, v___f_471_);
lean_closure_set(v___f_473_, 2, v_a_467_);
lean_closure_set(v___f_473_, 3, v_toApplicative_468_);
v___f_474_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_474_, 0, v_f_464_);
lean_closure_set(v___f_474_, 1, v_e_466_);
lean_closure_set(v___f_474_, 2, v_toBind_469_);
lean_closure_set(v___f_474_, 3, v___f_473_);
lean_closure_set(v___f_474_, 4, v___f_471_);
lean_closure_set(v___f_474_, 5, v_a_467_);
v___f_475_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed), 10, 9);
lean_closure_set(v___f_475_, 0, v_p_463_);
lean_closure_set(v___f_475_, 1, v_e_466_);
lean_closure_set(v___f_475_, 2, v___f_471_);
lean_closure_set(v___f_475_, 3, v_a_467_);
lean_closure_set(v___f_475_, 4, v_inst_461_);
lean_closure_set(v___f_475_, 5, v_inst_462_);
lean_closure_set(v___f_475_, 6, v_toBind_469_);
lean_closure_set(v___f_475_, 7, v___f_474_);
lean_closure_set(v___f_475_, 8, v_toApplicative_468_);
v___x_476_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_461_, v_inst_462_, v_e_466_, v_a_467_);
v___x_477_ = lean_apply_4(v_toBind_469_, lean_box(0), lean_box(0), v___x_476_, v___f_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_p_480_, lean_object* v_f_481_, uint8_t v_stopWhenVisited_482_, lean_object* v_b_483_, lean_object* v___y_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_478_, v_inst_479_, v_p_480_, v_f_481_, v_stopWhenVisited_482_, v_b_483_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___boxed(lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_p_489_, lean_object* v_f_490_, lean_object* v_stopWhenVisited_491_, lean_object* v_e_492_, lean_object* v_a_493_){
_start:
{
uint8_t v_stopWhenVisited_boxed_494_; lean_object* v_res_495_; 
v_stopWhenVisited_boxed_494_ = lean_unbox(v_stopWhenVisited_491_);
v_res_495_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_487_, v_inst_488_, v_p_489_, v_f_490_, v_stopWhenVisited_boxed_494_, v_e_492_, v_a_493_);
lean_dec(v_a_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(lean_object* v_00_u03c9_496_, lean_object* v_m_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_p_501_, lean_object* v_f_502_, uint8_t v_stopWhenVisited_503_, lean_object* v_e_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_499_, v_inst_500_, v_p_501_, v_f_502_, v_stopWhenVisited_503_, v_e_504_, v_a_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___boxed(lean_object* v_00_u03c9_507_, lean_object* v_m_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_p_512_, lean_object* v_f_513_, lean_object* v_stopWhenVisited_514_, lean_object* v_e_515_, lean_object* v_a_516_){
_start:
{
uint8_t v_stopWhenVisited_boxed_517_; lean_object* v_res_518_; 
v_stopWhenVisited_boxed_517_ = lean_unbox(v_stopWhenVisited_514_);
v_res_518_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(v_00_u03c9_507_, v_m_508_, v_inst_509_, v_inst_510_, v_inst_511_, v_p_512_, v_f_513_, v_stopWhenVisited_boxed_517_, v_e_515_, v_a_516_);
lean_dec(v_a_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__0(lean_object* v_a_519_, lean_object* v_toPure_520_, lean_object* v_s_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_a_519_);
lean_ctor_set(v___x_522_, 1, v_s_521_);
v___x_523_ = lean_apply_2(v_toPure_520_, lean_box(0), v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__1(lean_object* v_toPure_524_, lean_object* v_ref_525_, lean_object* v_inst_526_, lean_object* v_toBind_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___f_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___f_529_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_529_, 0, v_a_528_);
lean_closure_set(v___f_529_, 1, v_toPure_524_);
v___x_530_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_530_, 0, lean_box(0));
lean_closure_set(v___x_530_, 1, lean_box(0));
lean_closure_set(v___x_530_, 2, v_ref_525_);
v___x_531_ = lean_apply_2(v_inst_526_, lean_box(0), v___x_530_);
v___x_532_ = lean_apply_4(v_toBind_527_, lean_box(0), lean_box(0), v___x_531_, v___f_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2(lean_object* v_toPure_533_, lean_object* v_inst_534_, lean_object* v_toBind_535_, lean_object* v_inst_536_, lean_object* v_p_537_, lean_object* v_f_538_, uint8_t v_stopWhenVisited_539_, lean_object* v_e_540_, lean_object* v_ref_541_){
_start:
{
lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_inc(v_toBind_535_);
lean_inc(v_inst_534_);
lean_inc(v_ref_541_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_542_, 0, v_toPure_533_);
lean_closure_set(v___f_542_, 1, v_ref_541_);
lean_closure_set(v___f_542_, 2, v_inst_534_);
lean_closure_set(v___f_542_, 3, v_toBind_535_);
v___x_543_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_534_, v_inst_536_, v_p_537_, v_f_538_, v_stopWhenVisited_539_, v_e_540_, v_ref_541_);
lean_dec(v_ref_541_);
v___x_544_ = lean_apply_4(v_toBind_535_, lean_box(0), lean_box(0), v___x_543_, v___f_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed(lean_object* v_toPure_545_, lean_object* v_inst_546_, lean_object* v_toBind_547_, lean_object* v_inst_548_, lean_object* v_p_549_, lean_object* v_f_550_, lean_object* v_stopWhenVisited_551_, lean_object* v_e_552_, lean_object* v_ref_553_){
_start:
{
uint8_t v_stopWhenVisited_boxed_554_; lean_object* v_res_555_; 
v_stopWhenVisited_boxed_554_ = lean_unbox(v_stopWhenVisited_551_);
v_res_555_ = l_Lean_ForEachExprWhere_visit___redArg___lam__2(v_toPure_545_, v_inst_546_, v_toBind_547_, v_inst_548_, v_p_549_, v_f_550_, v_stopWhenVisited_boxed_554_, v_e_552_, v_ref_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__3(lean_object* v_toPure_556_, lean_object* v_____x_557_){
_start:
{
lean_object* v_fst_558_; lean_object* v___x_559_; 
v_fst_558_ = lean_ctor_get(v_____x_557_, 0);
lean_inc(v_fst_558_);
lean_dec_ref(v_____x_557_);
v___x_559_ = lean_apply_2(v_toPure_556_, lean_box(0), v_fst_558_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l_Lean_ForEachExprWhere_initCache;
v___x_561_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_561_, 0, lean_box(0));
lean_closure_set(v___x_561_, 1, lean_box(0));
lean_closure_set(v___x_561_, 2, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg(lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_p_564_, lean_object* v_f_565_, lean_object* v_e_566_, uint8_t v_stopWhenVisited_567_){
_start:
{
lean_object* v_toApplicative_568_; lean_object* v_toBind_569_; lean_object* v_toPure_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_toApplicative_568_ = lean_ctor_get(v_inst_563_, 0);
v_toBind_569_ = lean_ctor_get(v_inst_563_, 1);
lean_inc_n(v_toBind_569_, 3);
v_toPure_570_ = lean_ctor_get(v_toApplicative_568_, 1);
lean_inc_n(v_toPure_570_, 2);
v___x_571_ = lean_obj_once(&l_Lean_ForEachExprWhere_visit___redArg___closed__0, &l_Lean_ForEachExprWhere_visit___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0);
lean_inc(v_inst_562_);
v___x_572_ = lean_apply_2(v_inst_562_, lean_box(0), v___x_571_);
v___x_573_ = lean_box(v_stopWhenVisited_567_);
v___f_574_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_574_, 0, v_toPure_570_);
lean_closure_set(v___f_574_, 1, v_inst_562_);
lean_closure_set(v___f_574_, 2, v_toBind_569_);
lean_closure_set(v___f_574_, 3, v_inst_563_);
lean_closure_set(v___f_574_, 4, v_p_564_);
lean_closure_set(v___f_574_, 5, v_f_565_);
lean_closure_set(v___f_574_, 6, v___x_573_);
lean_closure_set(v___f_574_, 7, v_e_566_);
v___f_575_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__3), 2, 1);
lean_closure_set(v___f_575_, 0, v_toPure_570_);
v___x_576_ = lean_apply_4(v_toBind_569_, lean_box(0), lean_box(0), v___x_572_, v___f_574_);
v___x_577_ = lean_apply_4(v_toBind_569_, lean_box(0), lean_box(0), v___x_576_, v___f_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___boxed(lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_p_580_, lean_object* v_f_581_, lean_object* v_e_582_, lean_object* v_stopWhenVisited_583_){
_start:
{
uint8_t v_stopWhenVisited_boxed_584_; lean_object* v_res_585_; 
v_stopWhenVisited_boxed_584_ = lean_unbox(v_stopWhenVisited_583_);
v_res_585_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_578_, v_inst_579_, v_p_580_, v_f_581_, v_e_582_, v_stopWhenVisited_boxed_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit(lean_object* v_00_u03c9_586_, lean_object* v_m_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_p_591_, lean_object* v_f_592_, lean_object* v_e_593_, uint8_t v_stopWhenVisited_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_589_, v_inst_590_, v_p_591_, v_f_592_, v_e_593_, v_stopWhenVisited_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___boxed(lean_object* v_00_u03c9_596_, lean_object* v_m_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_p_601_, lean_object* v_f_602_, lean_object* v_e_603_, lean_object* v_stopWhenVisited_604_){
_start:
{
uint8_t v_stopWhenVisited_boxed_605_; lean_object* v_res_606_; 
v_stopWhenVisited_boxed_605_ = lean_unbox(v_stopWhenVisited_604_);
v_res_606_ = l_Lean_ForEachExprWhere_visit(v_00_u03c9_596_, v_m_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_p_601_, v_f_602_, v_e_603_, v_stopWhenVisited_boxed_605_);
return v_res_606_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin) {
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
l_Lean_ForEachExprWhere_cacheSize = _init_l_Lean_ForEachExprWhere_cacheSize();
l_Lean_ForEachExprWhere_initCache = _init_l_Lean_ForEachExprWhere_initCache();
lean_mark_persistent(l_Lean_ForEachExprWhere_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_ForEachExprWhere(builtin);
}
#ifdef __cplusplus
}
#endif
