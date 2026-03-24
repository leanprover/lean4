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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ForEachExprWhere_cacheSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_ForEachExprWhere_cacheSize___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t _init_l_Lean_ForEachExprWhere_cacheSize___closed__0(void){
_start:
{
size_t v___x_1_; size_t v___x_2_; size_t v___x_3_; 
v___x_1_ = ((size_t)1ULL);
v___x_2_ = ((size_t)8192ULL);
v___x_3_ = lean_usize_sub(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_cacheSize(void){
_start:
{
size_t v___x_4_; 
v___x_4_ = lean_usize_once(&l_Lean_ForEachExprWhere_cacheSize___closed__0, &l_Lean_ForEachExprWhere_cacheSize___closed__0_once, _init_l_Lean_ForEachExprWhere_cacheSize___closed__0);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__0(void){
_start:
{
size_t v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_usize_once(&l_Lean_ForEachExprWhere_cacheSize___closed__0, &l_Lean_ForEachExprWhere_cacheSize___closed__0_once, _init_l_Lean_ForEachExprWhere_cacheSize___closed__0);
v___x_9_ = lean_usize_to_nat(v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__1(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = ((lean_object*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_notAnExpr));
v___x_11_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__0, &l_Lean_ForEachExprWhere_initCache___closed__0_once, _init_l_Lean_ForEachExprWhere_initCache___closed__0);
v___x_12_ = lean_mk_array(v___x_11_, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__2(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_unsigned_to_nat(16u);
v___x_15_ = lean_mk_array(v___x_14_, v___x_13_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__3(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__2, &l_Lean_ForEachExprWhere_initCache___closed__2_once, _init_l_Lean_ForEachExprWhere_initCache___closed__2);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__4(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__3, &l_Lean_ForEachExprWhere_initCache___closed__3_once, _init_l_Lean_ForEachExprWhere_initCache___closed__3);
v___x_20_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__1, &l_Lean_ForEachExprWhere_initCache___closed__1_once, _init_l_Lean_ForEachExprWhere_initCache___closed__1);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___x_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__4, &l_Lean_ForEachExprWhere_initCache___closed__4_once, _init_l_Lean_ForEachExprWhere_initCache___closed__4);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0(size_t v___x_23_, lean_object* v_e_24_, lean_object* v_s_25_){
_start:
{
lean_object* v_visited_26_; lean_object* v_checked_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_37_; 
v_visited_26_ = lean_ctor_get(v_s_25_, 0);
v_checked_27_ = lean_ctor_get(v_s_25_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v_s_25_);
if (v_isSharedCheck_37_ == 0)
{
v___x_29_ = v_s_25_;
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_checked_27_);
lean_inc(v_visited_26_);
lean_dec(v_s_25_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_array_uset(v_visited_26_, v___x_23_, v_e_24_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 0, v___x_32_);
v___x_34_ = v___x_29_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_checked_27_);
v___x_34_ = v_reuseFailAlloc_36_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_31_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed(lean_object* v___x_38_, lean_object* v_e_39_, lean_object* v_s_40_){
_start:
{
size_t v___x_383__boxed_41_; lean_object* v_res_42_; 
v___x_383__boxed_41_ = lean_unbox_usize(v___x_38_);
lean_dec(v___x_38_);
v_res_42_ = l_Lean_ForEachExprWhere_visited___redArg___lam__0(v___x_383__boxed_41_, v_e_39_, v_s_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1(lean_object* v_toApplicative_43_, uint8_t v___x_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_toPure_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_toPure_46_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_46_);
lean_dec_ref(v_toApplicative_43_);
v___x_47_ = lean_box(v___x_44_);
v___x_48_ = lean_apply_2(v_toPure_46_, lean_box(0), v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed(lean_object* v_toApplicative_49_, lean_object* v___x_50_, lean_object* v_a_51_){
_start:
{
uint8_t v___x_406__boxed_52_; lean_object* v_res_53_; 
v___x_406__boxed_52_ = lean_unbox(v___x_50_);
v_res_53_ = l_Lean_ForEachExprWhere_visited___redArg___lam__1(v_toApplicative_49_, v___x_406__boxed_52_, v_a_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2(lean_object* v_e_54_, lean_object* v_toApplicative_55_, lean_object* v_a_56_, lean_object* v_inst_57_, lean_object* v_toBind_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_visited_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; size_t v___x_65_; uint8_t v___x_66_; 
v_visited_60_ = lean_ctor_get(v_a_59_, 0);
v___x_61_ = lean_ptr_addr(v_e_54_);
v___x_62_ = lean_usize_once(&l_Lean_ForEachExprWhere_cacheSize___closed__0, &l_Lean_ForEachExprWhere_cacheSize___closed__0_once, _init_l_Lean_ForEachExprWhere_cacheSize___closed__0);
v___x_63_ = lean_usize_mod(v___x_61_, v___x_62_);
v___x_64_ = lean_array_uget_borrowed(v_visited_60_, v___x_63_);
v___x_65_ = lean_ptr_addr(v___x_64_);
v___x_66_ = lean_usize_dec_eq(v___x_65_, v___x_61_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_67_ = lean_box_usize(v___x_63_);
v___f_68_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_68_, 0, v___x_67_);
lean_closure_set(v___f_68_, 1, v_e_54_);
v___x_69_ = lean_box(v___x_66_);
v___f_70_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_70_, 0, v_toApplicative_55_);
lean_closure_set(v___f_70_, 1, v___x_69_);
v___x_71_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, lean_box(0));
lean_closure_set(v___x_71_, 2, lean_box(0));
lean_closure_set(v___x_71_, 3, v_a_56_);
lean_closure_set(v___x_71_, 4, v___f_68_);
v___x_72_ = lean_apply_2(v_inst_57_, lean_box(0), v___x_71_);
v___x_73_ = lean_apply_4(v_toBind_58_, lean_box(0), lean_box(0), v___x_72_, v___f_70_);
return v___x_73_;
}
else
{
lean_object* v_toPure_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_toBind_58_);
lean_dec(v_inst_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_e_54_);
v_toPure_74_ = lean_ctor_get(v_toApplicative_55_, 1);
lean_inc(v_toPure_74_);
lean_dec_ref(v_toApplicative_55_);
v___x_75_ = lean_box(v___x_66_);
v___x_76_ = lean_apply_2(v_toPure_74_, lean_box(0), v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed(lean_object* v_e_77_, lean_object* v_toApplicative_78_, lean_object* v_a_79_, lean_object* v_inst_80_, lean_object* v_toBind_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_ForEachExprWhere_visited___redArg___lam__2(v_e_77_, v_toApplicative_78_, v_a_79_, v_inst_80_, v_toBind_81_, v_a_82_);
lean_dec_ref(v_a_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg(lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_e_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_toApplicative_88_; lean_object* v_toBind_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_toApplicative_88_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_ref(v_toApplicative_88_);
v_toBind_89_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_toBind_89_);
lean_dec_ref(v_inst_85_);
lean_inc(v_toBind_89_);
lean_inc(v_inst_84_);
lean_inc(v_a_87_);
v___f_90_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_90_, 0, v_e_86_);
lean_closure_set(v___f_90_, 1, v_toApplicative_88_);
lean_closure_set(v___f_90_, 2, v_a_87_);
lean_closure_set(v___f_90_, 3, v_inst_84_);
lean_closure_set(v___f_90_, 4, v_toBind_89_);
v___x_91_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, lean_box(0));
lean_closure_set(v___x_91_, 2, v_a_87_);
v___x_92_ = lean_apply_2(v_inst_84_, lean_box(0), v___x_91_);
v___x_93_ = lean_apply_4(v_toBind_89_, lean_box(0), lean_box(0), v___x_92_, v___f_90_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited(lean_object* v_00_u03c9_94_, lean_object* v_m_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_e_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_97_, v_inst_98_, v_e_99_, v_a_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__0(lean_object* v___x_102_, lean_object* v___x_103_, lean_object* v_e_104_, lean_object* v_s_105_){
_start:
{
lean_object* v_visited_106_; lean_object* v_checked_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_117_; 
v_visited_106_ = lean_ctor_get(v_s_105_, 0);
v_checked_107_ = lean_ctor_get(v_s_105_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v_s_105_);
if (v_isSharedCheck_117_ == 0)
{
v___x_109_ = v_s_105_;
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_checked_107_);
lean_inc(v_visited_106_);
lean_dec(v_s_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_111_ = lean_box(0);
v___x_112_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_102_, v___x_103_, v_checked_107_, v_e_104_, v___x_111_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_112_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_visited_106_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_116_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_111_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1(lean_object* v_toApplicative_118_, uint8_t v___x_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_toPure_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_toPure_121_ = lean_ctor_get(v_toApplicative_118_, 1);
lean_inc(v_toPure_121_);
lean_dec_ref(v_toApplicative_118_);
v___x_122_ = lean_box(v___x_119_);
v___x_123_ = lean_apply_2(v_toPure_121_, lean_box(0), v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed(lean_object* v_toApplicative_124_, lean_object* v___x_125_, lean_object* v_a_126_){
_start:
{
uint8_t v___x_426__boxed_127_; lean_object* v_res_128_; 
v___x_426__boxed_127_ = lean_unbox(v___x_125_);
v_res_128_ = l_Lean_ForEachExprWhere_checked___redArg___lam__1(v_toApplicative_124_, v___x_426__boxed_127_, v_a_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2(lean_object* v___x_129_, lean_object* v___x_130_, lean_object* v_e_131_, lean_object* v_toApplicative_132_, lean_object* v_a_133_, lean_object* v___f_134_, lean_object* v_inst_135_, lean_object* v_toBind_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_checked_138_; uint8_t v___x_139_; 
v_checked_138_ = lean_ctor_get(v_a_137_, 1);
v___x_139_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_129_, v___x_130_, v_checked_138_, v_e_131_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_140_ = lean_box(v___x_139_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_141_, 0, v_toApplicative_132_);
lean_closure_set(v___f_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_142_, 0, lean_box(0));
lean_closure_set(v___x_142_, 1, lean_box(0));
lean_closure_set(v___x_142_, 2, lean_box(0));
lean_closure_set(v___x_142_, 3, v_a_133_);
lean_closure_set(v___x_142_, 4, v___f_134_);
v___x_143_ = lean_apply_2(v_inst_135_, lean_box(0), v___x_142_);
v___x_144_ = lean_apply_4(v_toBind_136_, lean_box(0), lean_box(0), v___x_143_, v___f_141_);
return v___x_144_;
}
else
{
lean_object* v_toPure_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_toBind_136_);
lean_dec(v_inst_135_);
lean_dec_ref(v___f_134_);
lean_dec(v_a_133_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_inc(v_toPure_145_);
lean_dec_ref(v_toApplicative_132_);
v___x_146_ = lean_box(v___x_139_);
v___x_147_ = lean_apply_2(v_toPure_145_, lean_box(0), v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed(lean_object* v___x_148_, lean_object* v___x_149_, lean_object* v_e_150_, lean_object* v_toApplicative_151_, lean_object* v_a_152_, lean_object* v___f_153_, lean_object* v_inst_154_, lean_object* v_toBind_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_ForEachExprWhere_checked___redArg___lam__2(v___x_148_, v___x_149_, v_e_150_, v_toApplicative_151_, v_a_152_, v___f_153_, v_inst_154_, v_toBind_155_, v_a_156_);
lean_dec_ref(v_a_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg(lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_e_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_toApplicative_164_; lean_object* v_toBind_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_toApplicative_164_ = lean_ctor_get(v_inst_161_, 0);
lean_inc_ref(v_toApplicative_164_);
v_toBind_165_ = lean_ctor_get(v_inst_161_, 1);
lean_inc(v_toBind_165_);
lean_dec_ref(v_inst_161_);
v___x_166_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__0));
v___x_167_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__1));
lean_inc_ref(v_e_162_);
v___f_168_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__0), 4, 3);
lean_closure_set(v___f_168_, 0, v___x_166_);
lean_closure_set(v___f_168_, 1, v___x_167_);
lean_closure_set(v___f_168_, 2, v_e_162_);
lean_inc(v_toBind_165_);
lean_inc(v_inst_160_);
lean_inc(v_a_163_);
v___f_169_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_169_, 0, v___x_166_);
lean_closure_set(v___f_169_, 1, v___x_167_);
lean_closure_set(v___f_169_, 2, v_e_162_);
lean_closure_set(v___f_169_, 3, v_toApplicative_164_);
lean_closure_set(v___f_169_, 4, v_a_163_);
lean_closure_set(v___f_169_, 5, v___f_168_);
lean_closure_set(v___f_169_, 6, v_inst_160_);
lean_closure_set(v___f_169_, 7, v_toBind_165_);
v___x_170_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, lean_box(0));
lean_closure_set(v___x_170_, 2, v_a_163_);
v___x_171_ = lean_apply_2(v_inst_160_, lean_box(0), v___x_170_);
v___x_172_ = lean_apply_4(v_toBind_165_, lean_box(0), lean_box(0), v___x_171_, v___f_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked(lean_object* v_00_u03c9_173_, lean_object* v_m_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_e_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_176_, v_inst_177_, v_e_178_, v_a_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(lean_object* v_p_181_, lean_object* v_e_182_, lean_object* v___f_183_, lean_object* v_a_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_toBind_187_, lean_object* v___f_188_, lean_object* v_toApplicative_189_, uint8_t v_a_190_){
_start:
{
if (v_a_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
lean_dec_ref(v_toApplicative_189_);
lean_inc_ref(v_e_182_);
v___x_191_ = lean_apply_1(v_p_181_, v_e_182_);
v___x_192_ = lean_unbox(v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v___f_188_);
lean_dec(v_toBind_187_);
lean_dec_ref(v_inst_186_);
lean_dec(v_inst_185_);
lean_dec_ref(v_e_182_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_apply_2(v___f_183_, v___x_193_, v_a_184_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___f_183_);
v___x_195_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_185_, v_inst_186_, v_e_182_, v_a_184_);
v___x_196_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_195_, v___f_188_);
return v___x_196_;
}
}
else
{
lean_object* v_toPure_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v___f_188_);
lean_dec(v_toBind_187_);
lean_dec_ref(v_inst_186_);
lean_dec(v_inst_185_);
lean_dec(v_a_184_);
lean_dec(v___f_183_);
lean_dec_ref(v_e_182_);
lean_dec_ref(v_p_181_);
v_toPure_197_ = lean_ctor_get(v_toApplicative_189_, 1);
lean_inc(v_toPure_197_);
lean_dec_ref(v_toApplicative_189_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_2(v_toPure_197_, lean_box(0), v___x_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed(lean_object* v_p_200_, lean_object* v_e_201_, lean_object* v___f_202_, lean_object* v_a_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_toBind_206_, lean_object* v___f_207_, lean_object* v_toApplicative_208_, lean_object* v_a_209_){
_start:
{
uint8_t v_a_boxed_210_; lean_object* v_res_211_; 
v_a_boxed_210_ = lean_unbox(v_a_209_);
v_res_211_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(v_p_200_, v_e_201_, v___f_202_, v_a_203_, v_inst_204_, v_inst_205_, v_toBind_206_, v___f_207_, v_toApplicative_208_, v_a_boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(uint8_t v_stopWhenVisited_212_, lean_object* v___f_213_, lean_object* v_a_214_, lean_object* v_toApplicative_215_, lean_object* v_a_216_){
_start:
{
if (v_stopWhenVisited_212_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_toApplicative_215_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_apply_2(v___f_213_, v___x_217_, v_a_214_);
return v___x_218_;
}
else
{
lean_object* v_toPure_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_a_214_);
lean_dec(v___f_213_);
v_toPure_219_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_219_);
lean_dec_ref(v_toApplicative_215_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_apply_2(v_toPure_219_, lean_box(0), v___x_220_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed(lean_object* v_stopWhenVisited_222_, lean_object* v___f_223_, lean_object* v_a_224_, lean_object* v_toApplicative_225_, lean_object* v_a_226_){
_start:
{
uint8_t v_stopWhenVisited_boxed_227_; lean_object* v_res_228_; 
v_stopWhenVisited_boxed_227_ = lean_unbox(v_stopWhenVisited_222_);
v_res_228_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(v_stopWhenVisited_boxed_227_, v___f_223_, v_a_224_, v_toApplicative_225_, v_a_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(lean_object* v_f_229_, lean_object* v_e_230_, lean_object* v_toBind_231_, lean_object* v___f_232_, lean_object* v___f_233_, lean_object* v_a_234_, uint8_t v_a_235_){
_start:
{
if (v_a_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_a_234_);
lean_dec(v___f_233_);
v___x_236_ = lean_apply_1(v_f_229_, v_e_230_);
v___x_237_ = lean_apply_4(v_toBind_231_, lean_box(0), lean_box(0), v___x_236_, v___f_232_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v___f_232_);
lean_dec(v_toBind_231_);
lean_dec_ref(v_e_230_);
lean_dec(v_f_229_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_apply_2(v___f_233_, v___x_238_, v_a_234_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed(lean_object* v_f_240_, lean_object* v_e_241_, lean_object* v_toBind_242_, lean_object* v___f_243_, lean_object* v___f_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
uint8_t v_a_boxed_247_; lean_object* v_res_248_; 
v_a_boxed_247_ = lean_unbox(v_a_246_);
v_res_248_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(v_f_240_, v_e_241_, v_toBind_242_, v___f_243_, v___f_244_, v_a_245_, v_a_boxed_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_p_251_, lean_object* v_f_252_, lean_object* v_stopWhenVisited_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v_a_256_){
_start:
{
uint8_t v_stopWhenVisited_boxed_257_; lean_object* v_res_258_; 
v_stopWhenVisited_boxed_257_ = lean_unbox(v_stopWhenVisited_253_);
v_res_258_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(v_inst_249_, v_inst_250_, v_p_251_, v_f_252_, v_stopWhenVisited_boxed_257_, v_b_254_, v___y_255_, v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_p_261_, lean_object* v_f_262_, uint8_t v_stopWhenVisited_263_, lean_object* v_body_264_, lean_object* v___y_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_259_, v_inst_260_, v_p_261_, v_f_262_, v_stopWhenVisited_263_, v_body_264_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_p_270_, lean_object* v_f_271_, lean_object* v_stopWhenVisited_272_, lean_object* v_body_273_, lean_object* v___y_274_, lean_object* v_a_275_){
_start:
{
uint8_t v_stopWhenVisited_boxed_276_; lean_object* v_res_277_; 
v_stopWhenVisited_boxed_276_ = lean_unbox(v_stopWhenVisited_272_);
v_res_277_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(v_inst_268_, v_inst_269_, v_p_270_, v_f_271_, v_stopWhenVisited_boxed_276_, v_body_273_, v___y_274_, v_a_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_p_280_, lean_object* v_f_281_, uint8_t v_stopWhenVisited_282_, lean_object* v_value_283_, lean_object* v___y_284_, lean_object* v_toBind_285_, lean_object* v___f_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_278_, v_inst_279_, v_p_280_, v_f_281_, v_stopWhenVisited_282_, v_value_283_, v___y_284_);
v___x_289_ = lean_apply_4(v_toBind_285_, lean_box(0), lean_box(0), v___x_288_, v___f_286_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_p_292_, lean_object* v_f_293_, lean_object* v_stopWhenVisited_294_, lean_object* v_value_295_, lean_object* v___y_296_, lean_object* v_toBind_297_, lean_object* v___f_298_, lean_object* v_a_299_){
_start:
{
uint8_t v_stopWhenVisited_boxed_300_; lean_object* v_res_301_; 
v_stopWhenVisited_boxed_300_ = lean_unbox(v_stopWhenVisited_294_);
v_res_301_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(v_inst_290_, v_inst_291_, v_p_292_, v_f_293_, v_stopWhenVisited_boxed_300_, v_value_295_, v___y_296_, v_toBind_297_, v___f_298_, v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_p_304_, lean_object* v_f_305_, uint8_t v_stopWhenVisited_306_, lean_object* v_arg_307_, lean_object* v___y_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_302_, v_inst_303_, v_p_304_, v_f_305_, v_stopWhenVisited_306_, v_arg_307_, v___y_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed(lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_p_313_, lean_object* v_f_314_, lean_object* v_stopWhenVisited_315_, lean_object* v_arg_316_, lean_object* v___y_317_, lean_object* v_a_318_){
_start:
{
uint8_t v_stopWhenVisited_boxed_319_; lean_object* v_res_320_; 
v_stopWhenVisited_boxed_319_ = lean_unbox(v_stopWhenVisited_315_);
v_res_320_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(v_inst_311_, v_inst_312_, v_p_313_, v_f_314_, v_stopWhenVisited_boxed_319_, v_arg_316_, v___y_317_, v_a_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_p_323_, lean_object* v_f_324_, uint8_t v_stopWhenVisited_325_, lean_object* v_toBind_326_, lean_object* v_e_327_, lean_object* v_toApplicative_328_, lean_object* v_____r_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_d_332_; lean_object* v_b_333_; 
switch(lean_obj_tag(v_e_327_))
{
case 7:
{
lean_object* v_binderType_338_; lean_object* v_body_339_; 
lean_dec_ref(v_toApplicative_328_);
v_binderType_338_ = lean_ctor_get(v_e_327_, 1);
lean_inc_ref(v_binderType_338_);
v_body_339_ = lean_ctor_get(v_e_327_, 2);
lean_inc_ref(v_body_339_);
lean_dec_ref(v_e_327_);
v_d_332_ = v_binderType_338_;
v_b_333_ = v_body_339_;
goto v___jp_331_;
}
case 6:
{
lean_object* v_binderType_340_; lean_object* v_body_341_; 
lean_dec_ref(v_toApplicative_328_);
v_binderType_340_ = lean_ctor_get(v_e_327_, 1);
lean_inc_ref(v_binderType_340_);
v_body_341_ = lean_ctor_get(v_e_327_, 2);
lean_inc_ref(v_body_341_);
lean_dec_ref(v_e_327_);
v_d_332_ = v_binderType_340_;
v_b_333_ = v_body_341_;
goto v___jp_331_;
}
case 8:
{
lean_object* v_type_342_; lean_object* v_value_343_; lean_object* v_body_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v_toApplicative_328_);
v_type_342_ = lean_ctor_get(v_e_327_, 1);
lean_inc_ref(v_type_342_);
v_value_343_ = lean_ctor_get(v_e_327_, 2);
lean_inc_ref(v_value_343_);
v_body_344_ = lean_ctor_get(v_e_327_, 3);
lean_inc_ref(v_body_344_);
lean_dec_ref(v_e_327_);
v___x_345_ = lean_box(v_stopWhenVisited_325_);
lean_inc(v___y_330_);
lean_inc(v_f_324_);
lean_inc_ref(v_p_323_);
lean_inc_ref(v_inst_322_);
lean_inc(v_inst_321_);
v___f_346_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_346_, 0, v_inst_321_);
lean_closure_set(v___f_346_, 1, v_inst_322_);
lean_closure_set(v___f_346_, 2, v_p_323_);
lean_closure_set(v___f_346_, 3, v_f_324_);
lean_closure_set(v___f_346_, 4, v___x_345_);
lean_closure_set(v___f_346_, 5, v_body_344_);
lean_closure_set(v___f_346_, 6, v___y_330_);
v___x_347_ = lean_box(v_stopWhenVisited_325_);
lean_inc(v_toBind_326_);
lean_inc(v___y_330_);
lean_inc(v_f_324_);
lean_inc_ref(v_p_323_);
lean_inc_ref(v_inst_322_);
lean_inc(v_inst_321_);
v___f_348_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_348_, 0, v_inst_321_);
lean_closure_set(v___f_348_, 1, v_inst_322_);
lean_closure_set(v___f_348_, 2, v_p_323_);
lean_closure_set(v___f_348_, 3, v_f_324_);
lean_closure_set(v___f_348_, 4, v___x_347_);
lean_closure_set(v___f_348_, 5, v_value_343_);
lean_closure_set(v___f_348_, 6, v___y_330_);
lean_closure_set(v___f_348_, 7, v_toBind_326_);
lean_closure_set(v___f_348_, 8, v___f_346_);
v___x_349_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_321_, v_inst_322_, v_p_323_, v_f_324_, v_stopWhenVisited_325_, v_type_342_, v___y_330_);
v___x_350_ = lean_apply_4(v_toBind_326_, lean_box(0), lean_box(0), v___x_349_, v___f_348_);
return v___x_350_;
}
case 5:
{
lean_object* v_fn_351_; lean_object* v_arg_352_; lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec_ref(v_toApplicative_328_);
v_fn_351_ = lean_ctor_get(v_e_327_, 0);
lean_inc_ref(v_fn_351_);
v_arg_352_ = lean_ctor_get(v_e_327_, 1);
lean_inc_ref(v_arg_352_);
lean_dec_ref(v_e_327_);
v___x_353_ = lean_box(v_stopWhenVisited_325_);
lean_inc(v___y_330_);
lean_inc(v_f_324_);
lean_inc_ref(v_p_323_);
lean_inc_ref(v_inst_322_);
lean_inc(v_inst_321_);
v___f_354_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_354_, 0, v_inst_321_);
lean_closure_set(v___f_354_, 1, v_inst_322_);
lean_closure_set(v___f_354_, 2, v_p_323_);
lean_closure_set(v___f_354_, 3, v_f_324_);
lean_closure_set(v___f_354_, 4, v___x_353_);
lean_closure_set(v___f_354_, 5, v_arg_352_);
lean_closure_set(v___f_354_, 6, v___y_330_);
v___x_355_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_321_, v_inst_322_, v_p_323_, v_f_324_, v_stopWhenVisited_325_, v_fn_351_, v___y_330_);
v___x_356_ = lean_apply_4(v_toBind_326_, lean_box(0), lean_box(0), v___x_355_, v___f_354_);
return v___x_356_;
}
case 10:
{
lean_object* v_expr_357_; lean_object* v___x_358_; 
lean_dec_ref(v_toApplicative_328_);
lean_dec(v_toBind_326_);
v_expr_357_ = lean_ctor_get(v_e_327_, 1);
lean_inc_ref(v_expr_357_);
lean_dec_ref(v_e_327_);
v___x_358_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_321_, v_inst_322_, v_p_323_, v_f_324_, v_stopWhenVisited_325_, v_expr_357_, v___y_330_);
return v___x_358_;
}
case 11:
{
lean_object* v_struct_359_; lean_object* v___x_360_; 
lean_dec_ref(v_toApplicative_328_);
lean_dec(v_toBind_326_);
v_struct_359_ = lean_ctor_get(v_e_327_, 2);
lean_inc_ref(v_struct_359_);
lean_dec_ref(v_e_327_);
v___x_360_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_321_, v_inst_322_, v_p_323_, v_f_324_, v_stopWhenVisited_325_, v_struct_359_, v___y_330_);
return v___x_360_;
}
default: 
{
lean_object* v_toPure_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v___y_330_);
lean_dec_ref(v_e_327_);
lean_dec(v_toBind_326_);
lean_dec(v_f_324_);
lean_dec_ref(v_p_323_);
lean_dec_ref(v_inst_322_);
lean_dec(v_inst_321_);
v_toPure_361_ = lean_ctor_get(v_toApplicative_328_, 1);
lean_inc(v_toPure_361_);
lean_dec_ref(v_toApplicative_328_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_apply_2(v_toPure_361_, lean_box(0), v___x_362_);
return v___x_363_;
}
}
v___jp_331_:
{
lean_object* v___x_334_; lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = lean_box(v_stopWhenVisited_325_);
lean_inc(v___y_330_);
lean_inc(v_f_324_);
lean_inc_ref(v_p_323_);
lean_inc_ref(v_inst_322_);
lean_inc(v_inst_321_);
v___f_335_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_335_, 0, v_inst_321_);
lean_closure_set(v___f_335_, 1, v_inst_322_);
lean_closure_set(v___f_335_, 2, v_p_323_);
lean_closure_set(v___f_335_, 3, v_f_324_);
lean_closure_set(v___f_335_, 4, v___x_334_);
lean_closure_set(v___f_335_, 5, v_b_333_);
lean_closure_set(v___f_335_, 6, v___y_330_);
v___x_336_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_321_, v_inst_322_, v_p_323_, v_f_324_, v_stopWhenVisited_325_, v_d_332_, v___y_330_);
v___x_337_ = lean_apply_4(v_toBind_326_, lean_box(0), lean_box(0), v___x_336_, v___f_335_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_p_366_, lean_object* v_f_367_, lean_object* v_stopWhenVisited_368_, lean_object* v_toBind_369_, lean_object* v_e_370_, lean_object* v_toApplicative_371_, lean_object* v_____r_372_, lean_object* v___y_373_){
_start:
{
uint8_t v_stopWhenVisited_boxed_374_; lean_object* v_res_375_; 
v_stopWhenVisited_boxed_374_ = lean_unbox(v_stopWhenVisited_368_);
v_res_375_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(v_inst_364_, v_inst_365_, v_p_366_, v_f_367_, v_stopWhenVisited_boxed_374_, v_toBind_369_, v_e_370_, v_toApplicative_371_, v_____r_372_, v___y_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_p_378_, lean_object* v_f_379_, uint8_t v_stopWhenVisited_380_, lean_object* v_e_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_toApplicative_383_; lean_object* v_toBind_384_; lean_object* v___x_385_; lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_toApplicative_383_ = lean_ctor_get(v_inst_377_, 0);
v_toBind_384_ = lean_ctor_get(v_inst_377_, 1);
lean_inc(v_toBind_384_);
v___x_385_ = lean_box(v_stopWhenVisited_380_);
lean_inc_ref(v_toApplicative_383_);
lean_inc_ref(v_e_381_);
lean_inc(v_toBind_384_);
lean_inc(v_f_379_);
lean_inc_ref(v_p_378_);
lean_inc_ref(v_inst_377_);
lean_inc(v_inst_376_);
v___f_386_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_386_, 0, v_inst_376_);
lean_closure_set(v___f_386_, 1, v_inst_377_);
lean_closure_set(v___f_386_, 2, v_p_378_);
lean_closure_set(v___f_386_, 3, v_f_379_);
lean_closure_set(v___f_386_, 4, v___x_385_);
lean_closure_set(v___f_386_, 5, v_toBind_384_);
lean_closure_set(v___f_386_, 6, v_e_381_);
lean_closure_set(v___f_386_, 7, v_toApplicative_383_);
v___x_387_ = lean_box(v_stopWhenVisited_380_);
lean_inc_ref(v_toApplicative_383_);
lean_inc(v_a_382_);
lean_inc_ref(v___f_386_);
v___f_388_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed), 5, 4);
lean_closure_set(v___f_388_, 0, v___x_387_);
lean_closure_set(v___f_388_, 1, v___f_386_);
lean_closure_set(v___f_388_, 2, v_a_382_);
lean_closure_set(v___f_388_, 3, v_toApplicative_383_);
lean_inc(v_a_382_);
lean_inc_ref(v___f_386_);
lean_inc(v_toBind_384_);
lean_inc_ref(v_e_381_);
v___f_389_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_389_, 0, v_f_379_);
lean_closure_set(v___f_389_, 1, v_e_381_);
lean_closure_set(v___f_389_, 2, v_toBind_384_);
lean_closure_set(v___f_389_, 3, v___f_388_);
lean_closure_set(v___f_389_, 4, v___f_386_);
lean_closure_set(v___f_389_, 5, v_a_382_);
lean_inc_ref(v_toApplicative_383_);
lean_inc(v_toBind_384_);
lean_inc_ref(v_inst_377_);
lean_inc(v_inst_376_);
lean_inc(v_a_382_);
lean_inc_ref(v_e_381_);
v___f_390_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed), 10, 9);
lean_closure_set(v___f_390_, 0, v_p_378_);
lean_closure_set(v___f_390_, 1, v_e_381_);
lean_closure_set(v___f_390_, 2, v___f_386_);
lean_closure_set(v___f_390_, 3, v_a_382_);
lean_closure_set(v___f_390_, 4, v_inst_376_);
lean_closure_set(v___f_390_, 5, v_inst_377_);
lean_closure_set(v___f_390_, 6, v_toBind_384_);
lean_closure_set(v___f_390_, 7, v___f_389_);
lean_closure_set(v___f_390_, 8, v_toApplicative_383_);
v___x_391_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_376_, v_inst_377_, v_e_381_, v_a_382_);
v___x_392_ = lean_apply_4(v_toBind_384_, lean_box(0), lean_box(0), v___x_391_, v___f_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_p_395_, lean_object* v_f_396_, uint8_t v_stopWhenVisited_397_, lean_object* v_b_398_, lean_object* v___y_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_393_, v_inst_394_, v_p_395_, v_f_396_, v_stopWhenVisited_397_, v_b_398_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___boxed(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_p_404_, lean_object* v_f_405_, lean_object* v_stopWhenVisited_406_, lean_object* v_e_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_stopWhenVisited_boxed_409_; lean_object* v_res_410_; 
v_stopWhenVisited_boxed_409_ = lean_unbox(v_stopWhenVisited_406_);
v_res_410_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_402_, v_inst_403_, v_p_404_, v_f_405_, v_stopWhenVisited_boxed_409_, v_e_407_, v_a_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(lean_object* v_00_u03c9_411_, lean_object* v_m_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_p_416_, lean_object* v_f_417_, uint8_t v_stopWhenVisited_418_, lean_object* v_e_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_414_, v_inst_415_, v_p_416_, v_f_417_, v_stopWhenVisited_418_, v_e_419_, v_a_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___boxed(lean_object* v_00_u03c9_422_, lean_object* v_m_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_p_427_, lean_object* v_f_428_, lean_object* v_stopWhenVisited_429_, lean_object* v_e_430_, lean_object* v_a_431_){
_start:
{
uint8_t v_stopWhenVisited_boxed_432_; lean_object* v_res_433_; 
v_stopWhenVisited_boxed_432_ = lean_unbox(v_stopWhenVisited_429_);
v_res_433_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(v_00_u03c9_422_, v_m_423_, v_inst_424_, v_inst_425_, v_inst_426_, v_p_427_, v_f_428_, v_stopWhenVisited_boxed_432_, v_e_430_, v_a_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__0(lean_object* v_a_434_, lean_object* v_toPure_435_, lean_object* v_s_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_a_434_);
lean_ctor_set(v___x_437_, 1, v_s_436_);
v___x_438_ = lean_apply_2(v_toPure_435_, lean_box(0), v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__1(lean_object* v_toPure_439_, lean_object* v_ref_440_, lean_object* v_inst_441_, lean_object* v_toBind_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___f_444_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_444_, 0, v_a_443_);
lean_closure_set(v___f_444_, 1, v_toPure_439_);
v___x_445_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_445_, 0, lean_box(0));
lean_closure_set(v___x_445_, 1, lean_box(0));
lean_closure_set(v___x_445_, 2, v_ref_440_);
v___x_446_ = lean_apply_2(v_inst_441_, lean_box(0), v___x_445_);
v___x_447_ = lean_apply_4(v_toBind_442_, lean_box(0), lean_box(0), v___x_446_, v___f_444_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2(lean_object* v_toPure_448_, lean_object* v_inst_449_, lean_object* v_toBind_450_, lean_object* v_inst_451_, lean_object* v_p_452_, lean_object* v_f_453_, uint8_t v_stopWhenVisited_454_, lean_object* v_e_455_, lean_object* v_ref_456_){
_start:
{
lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_inc(v_toBind_450_);
lean_inc(v_inst_449_);
lean_inc(v_ref_456_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_457_, 0, v_toPure_448_);
lean_closure_set(v___f_457_, 1, v_ref_456_);
lean_closure_set(v___f_457_, 2, v_inst_449_);
lean_closure_set(v___f_457_, 3, v_toBind_450_);
v___x_458_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_449_, v_inst_451_, v_p_452_, v_f_453_, v_stopWhenVisited_454_, v_e_455_, v_ref_456_);
v___x_459_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v___x_458_, v___f_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed(lean_object* v_toPure_460_, lean_object* v_inst_461_, lean_object* v_toBind_462_, lean_object* v_inst_463_, lean_object* v_p_464_, lean_object* v_f_465_, lean_object* v_stopWhenVisited_466_, lean_object* v_e_467_, lean_object* v_ref_468_){
_start:
{
uint8_t v_stopWhenVisited_boxed_469_; lean_object* v_res_470_; 
v_stopWhenVisited_boxed_469_ = lean_unbox(v_stopWhenVisited_466_);
v_res_470_ = l_Lean_ForEachExprWhere_visit___redArg___lam__2(v_toPure_460_, v_inst_461_, v_toBind_462_, v_inst_463_, v_p_464_, v_f_465_, v_stopWhenVisited_boxed_469_, v_e_467_, v_ref_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__3(lean_object* v_toPure_471_, lean_object* v_____x_472_){
_start:
{
lean_object* v_fst_473_; lean_object* v___x_474_; 
v_fst_473_ = lean_ctor_get(v_____x_472_, 0);
lean_inc(v_fst_473_);
lean_dec_ref(v_____x_472_);
v___x_474_ = lean_apply_2(v_toPure_471_, lean_box(0), v_fst_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = l_Lean_ForEachExprWhere_initCache;
v___x_476_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_476_, 0, lean_box(0));
lean_closure_set(v___x_476_, 1, lean_box(0));
lean_closure_set(v___x_476_, 2, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg(lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_p_479_, lean_object* v_f_480_, lean_object* v_e_481_, uint8_t v_stopWhenVisited_482_){
_start:
{
lean_object* v_toApplicative_483_; lean_object* v_toBind_484_; lean_object* v_toPure_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_toApplicative_483_ = lean_ctor_get(v_inst_478_, 0);
v_toBind_484_ = lean_ctor_get(v_inst_478_, 1);
lean_inc(v_toBind_484_);
v_toPure_485_ = lean_ctor_get(v_toApplicative_483_, 1);
lean_inc(v_toPure_485_);
v___x_486_ = lean_obj_once(&l_Lean_ForEachExprWhere_visit___redArg___closed__0, &l_Lean_ForEachExprWhere_visit___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0);
lean_inc(v_inst_477_);
v___x_487_ = lean_apply_2(v_inst_477_, lean_box(0), v___x_486_);
v___x_488_ = lean_box(v_stopWhenVisited_482_);
lean_inc(v_toBind_484_);
lean_inc(v_toPure_485_);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_489_, 0, v_toPure_485_);
lean_closure_set(v___f_489_, 1, v_inst_477_);
lean_closure_set(v___f_489_, 2, v_toBind_484_);
lean_closure_set(v___f_489_, 3, v_inst_478_);
lean_closure_set(v___f_489_, 4, v_p_479_);
lean_closure_set(v___f_489_, 5, v_f_480_);
lean_closure_set(v___f_489_, 6, v___x_488_);
lean_closure_set(v___f_489_, 7, v_e_481_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__3), 2, 1);
lean_closure_set(v___f_490_, 0, v_toPure_485_);
lean_inc(v_toBind_484_);
v___x_491_ = lean_apply_4(v_toBind_484_, lean_box(0), lean_box(0), v___x_487_, v___f_489_);
v___x_492_ = lean_apply_4(v_toBind_484_, lean_box(0), lean_box(0), v___x_491_, v___f_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___boxed(lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_p_495_, lean_object* v_f_496_, lean_object* v_e_497_, lean_object* v_stopWhenVisited_498_){
_start:
{
uint8_t v_stopWhenVisited_boxed_499_; lean_object* v_res_500_; 
v_stopWhenVisited_boxed_499_ = lean_unbox(v_stopWhenVisited_498_);
v_res_500_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_493_, v_inst_494_, v_p_495_, v_f_496_, v_e_497_, v_stopWhenVisited_boxed_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit(lean_object* v_00_u03c9_501_, lean_object* v_m_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_p_506_, lean_object* v_f_507_, lean_object* v_e_508_, uint8_t v_stopWhenVisited_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_504_, v_inst_505_, v_p_506_, v_f_507_, v_e_508_, v_stopWhenVisited_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___boxed(lean_object* v_00_u03c9_511_, lean_object* v_m_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_p_516_, lean_object* v_f_517_, lean_object* v_e_518_, lean_object* v_stopWhenVisited_519_){
_start:
{
uint8_t v_stopWhenVisited_boxed_520_; lean_object* v_res_521_; 
v_stopWhenVisited_boxed_520_ = lean_unbox(v_stopWhenVisited_519_);
v_res_521_ = l_Lean_ForEachExprWhere_visit(v_00_u03c9_511_, v_m_512_, v_inst_513_, v_inst_514_, v_inst_515_, v_p_516_, v_f_517_, v_e_518_, v_stopWhenVisited_boxed_520_);
return v_res_521_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
