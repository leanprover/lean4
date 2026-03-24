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
size_t v___x_328__boxed_41_; lean_object* v_res_42_; 
v___x_328__boxed_41_ = lean_unbox_usize(v___x_38_);
lean_dec(v___x_38_);
v_res_42_ = l_Lean_ForEachExprWhere_visited___redArg___lam__0(v___x_328__boxed_41_, v_e_39_, v_s_40_);
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
uint8_t v___x_351__boxed_52_; lean_object* v_res_53_; 
v___x_351__boxed_52_ = lean_unbox(v___x_50_);
v_res_53_ = l_Lean_ForEachExprWhere_visited___redArg___lam__1(v_toApplicative_49_, v___x_351__boxed_52_, v_a_51_);
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
lean_inc(v_a_56_);
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
lean_dec(v_a_79_);
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
lean_inc(v_a_87_);
v___x_91_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, lean_box(0));
lean_closure_set(v___x_91_, 2, v_a_87_);
v___x_92_ = lean_apply_2(v_inst_84_, lean_box(0), v___x_91_);
v___x_93_ = lean_apply_4(v_toBind_89_, lean_box(0), lean_box(0), v___x_92_, v___f_90_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___boxed(lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_e_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_94_, v_inst_95_, v_e_96_, v_a_97_);
lean_dec(v_a_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited(lean_object* v_00_u03c9_99_, lean_object* v_m_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_e_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_102_, v_inst_103_, v_e_104_, v_a_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___boxed(lean_object* v_00_u03c9_107_, lean_object* v_m_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_e_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_ForEachExprWhere_visited(v_00_u03c9_107_, v_m_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_e_112_, v_a_113_);
lean_dec(v_a_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__0(lean_object* v___x_115_, lean_object* v___x_116_, lean_object* v_e_117_, lean_object* v_s_118_){
_start:
{
lean_object* v_visited_119_; lean_object* v_checked_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_visited_119_ = lean_ctor_get(v_s_118_, 0);
v_checked_120_ = lean_ctor_get(v_s_118_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_s_118_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v_s_118_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_checked_120_);
lean_inc(v_visited_119_);
lean_dec(v_s_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_124_ = lean_box(0);
v___x_125_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_115_, v___x_116_, v_checked_120_, v_e_117_, v___x_124_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_125_);
v___x_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_visited_119_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_129_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_124_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1(lean_object* v_toApplicative_131_, uint8_t v___x_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_toPure_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_toPure_134_ = lean_ctor_get(v_toApplicative_131_, 1);
lean_inc(v_toPure_134_);
lean_dec_ref(v_toApplicative_131_);
v___x_135_ = lean_box(v___x_132_);
v___x_136_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed(lean_object* v_toApplicative_137_, lean_object* v___x_138_, lean_object* v_a_139_){
_start:
{
uint8_t v___x_371__boxed_140_; lean_object* v_res_141_; 
v___x_371__boxed_140_ = lean_unbox(v___x_138_);
v_res_141_ = l_Lean_ForEachExprWhere_checked___redArg___lam__1(v_toApplicative_137_, v___x_371__boxed_140_, v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2(lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v_e_144_, lean_object* v_toApplicative_145_, lean_object* v_a_146_, lean_object* v___f_147_, lean_object* v_inst_148_, lean_object* v_toBind_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_checked_151_; uint8_t v___x_152_; 
v_checked_151_ = lean_ctor_get(v_a_150_, 1);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_142_, v___x_143_, v_checked_151_, v_e_144_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_box(v___x_152_);
v___f_154_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_154_, 0, v_toApplicative_145_);
lean_closure_set(v___f_154_, 1, v___x_153_);
lean_inc(v_a_146_);
v___x_155_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_155_, 0, lean_box(0));
lean_closure_set(v___x_155_, 1, lean_box(0));
lean_closure_set(v___x_155_, 2, lean_box(0));
lean_closure_set(v___x_155_, 3, v_a_146_);
lean_closure_set(v___x_155_, 4, v___f_147_);
v___x_156_ = lean_apply_2(v_inst_148_, lean_box(0), v___x_155_);
v___x_157_ = lean_apply_4(v_toBind_149_, lean_box(0), lean_box(0), v___x_156_, v___f_154_);
return v___x_157_;
}
else
{
lean_object* v_toPure_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_toBind_149_);
lean_dec(v_inst_148_);
lean_dec_ref(v___f_147_);
v_toPure_158_ = lean_ctor_get(v_toApplicative_145_, 1);
lean_inc(v_toPure_158_);
lean_dec_ref(v_toApplicative_145_);
v___x_159_ = lean_box(v___x_152_);
v___x_160_ = lean_apply_2(v_toPure_158_, lean_box(0), v___x_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed(lean_object* v___x_161_, lean_object* v___x_162_, lean_object* v_e_163_, lean_object* v_toApplicative_164_, lean_object* v_a_165_, lean_object* v___f_166_, lean_object* v_inst_167_, lean_object* v_toBind_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_ForEachExprWhere_checked___redArg___lam__2(v___x_161_, v___x_162_, v_e_163_, v_toApplicative_164_, v_a_165_, v___f_166_, v_inst_167_, v_toBind_168_, v_a_169_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_e_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_toApplicative_177_; lean_object* v_toBind_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_toApplicative_177_ = lean_ctor_get(v_inst_174_, 0);
lean_inc_ref(v_toApplicative_177_);
v_toBind_178_ = lean_ctor_get(v_inst_174_, 1);
lean_inc(v_toBind_178_);
lean_dec_ref(v_inst_174_);
v___x_179_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__0));
v___x_180_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__1));
lean_inc_ref(v_e_175_);
v___f_181_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__0), 4, 3);
lean_closure_set(v___f_181_, 0, v___x_179_);
lean_closure_set(v___f_181_, 1, v___x_180_);
lean_closure_set(v___f_181_, 2, v_e_175_);
lean_inc(v_toBind_178_);
lean_inc(v_inst_173_);
lean_inc(v_a_176_);
v___f_182_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_182_, 0, v___x_179_);
lean_closure_set(v___f_182_, 1, v___x_180_);
lean_closure_set(v___f_182_, 2, v_e_175_);
lean_closure_set(v___f_182_, 3, v_toApplicative_177_);
lean_closure_set(v___f_182_, 4, v_a_176_);
lean_closure_set(v___f_182_, 5, v___f_181_);
lean_closure_set(v___f_182_, 6, v_inst_173_);
lean_closure_set(v___f_182_, 7, v_toBind_178_);
lean_inc(v_a_176_);
v___x_183_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_183_, 0, lean_box(0));
lean_closure_set(v___x_183_, 1, lean_box(0));
lean_closure_set(v___x_183_, 2, v_a_176_);
v___x_184_ = lean_apply_2(v_inst_173_, lean_box(0), v___x_183_);
v___x_185_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v___x_184_, v___f_182_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___boxed(lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_e_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_186_, v_inst_187_, v_e_188_, v_a_189_);
lean_dec(v_a_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked(lean_object* v_00_u03c9_191_, lean_object* v_m_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_e_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_194_, v_inst_195_, v_e_196_, v_a_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___boxed(lean_object* v_00_u03c9_199_, lean_object* v_m_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_e_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_ForEachExprWhere_checked(v_00_u03c9_199_, v_m_200_, v_inst_201_, v_inst_202_, v_inst_203_, v_e_204_, v_a_205_);
lean_dec(v_a_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(lean_object* v_p_207_, lean_object* v_e_208_, lean_object* v___f_209_, lean_object* v_a_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_toBind_213_, lean_object* v___f_214_, lean_object* v_toApplicative_215_, uint8_t v_a_216_){
_start:
{
if (v_a_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
lean_dec_ref(v_toApplicative_215_);
lean_inc_ref(v_e_208_);
v___x_217_ = lean_apply_1(v_p_207_, v_e_208_);
v___x_218_ = lean_unbox(v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___f_214_);
lean_dec(v_toBind_213_);
lean_dec_ref(v_inst_212_);
lean_dec(v_inst_211_);
lean_dec_ref(v_e_208_);
v___x_219_ = lean_box(0);
lean_inc(v_a_210_);
v___x_220_ = lean_apply_2(v___f_209_, v___x_219_, v_a_210_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v___f_209_);
v___x_221_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_211_, v_inst_212_, v_e_208_, v_a_210_);
v___x_222_ = lean_apply_4(v_toBind_213_, lean_box(0), lean_box(0), v___x_221_, v___f_214_);
return v___x_222_;
}
}
else
{
lean_object* v_toPure_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v___f_214_);
lean_dec(v_toBind_213_);
lean_dec_ref(v_inst_212_);
lean_dec(v_inst_211_);
lean_dec(v___f_209_);
lean_dec_ref(v_e_208_);
lean_dec_ref(v_p_207_);
v_toPure_223_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_223_);
lean_dec_ref(v_toApplicative_215_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_apply_2(v_toPure_223_, lean_box(0), v___x_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed(lean_object* v_p_226_, lean_object* v_e_227_, lean_object* v___f_228_, lean_object* v_a_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_toBind_232_, lean_object* v___f_233_, lean_object* v_toApplicative_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_a_boxed_236_; lean_object* v_res_237_; 
v_a_boxed_236_ = lean_unbox(v_a_235_);
v_res_237_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(v_p_226_, v_e_227_, v___f_228_, v_a_229_, v_inst_230_, v_inst_231_, v_toBind_232_, v___f_233_, v_toApplicative_234_, v_a_boxed_236_);
lean_dec(v_a_229_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(uint8_t v_stopWhenVisited_238_, lean_object* v___f_239_, lean_object* v_a_240_, lean_object* v_toApplicative_241_, lean_object* v_a_242_){
_start:
{
if (v_stopWhenVisited_238_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v_toApplicative_241_);
v___x_243_ = lean_box(0);
lean_inc(v_a_240_);
v___x_244_ = lean_apply_2(v___f_239_, v___x_243_, v_a_240_);
return v___x_244_;
}
else
{
lean_object* v_toPure_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v___f_239_);
v_toPure_245_ = lean_ctor_get(v_toApplicative_241_, 1);
lean_inc(v_toPure_245_);
lean_dec_ref(v_toApplicative_241_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_2(v_toPure_245_, lean_box(0), v___x_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed(lean_object* v_stopWhenVisited_248_, lean_object* v___f_249_, lean_object* v_a_250_, lean_object* v_toApplicative_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_stopWhenVisited_boxed_253_; lean_object* v_res_254_; 
v_stopWhenVisited_boxed_253_ = lean_unbox(v_stopWhenVisited_248_);
v_res_254_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(v_stopWhenVisited_boxed_253_, v___f_249_, v_a_250_, v_toApplicative_251_, v_a_252_);
lean_dec(v_a_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(lean_object* v_f_255_, lean_object* v_e_256_, lean_object* v_toBind_257_, lean_object* v___f_258_, lean_object* v___f_259_, lean_object* v_a_260_, uint8_t v_a_261_){
_start:
{
if (v_a_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v___f_259_);
v___x_262_ = lean_apply_1(v_f_255_, v_e_256_);
v___x_263_ = lean_apply_4(v_toBind_257_, lean_box(0), lean_box(0), v___x_262_, v___f_258_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v___f_258_);
lean_dec(v_toBind_257_);
lean_dec_ref(v_e_256_);
lean_dec(v_f_255_);
v___x_264_ = lean_box(0);
lean_inc(v_a_260_);
v___x_265_ = lean_apply_2(v___f_259_, v___x_264_, v_a_260_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed(lean_object* v_f_266_, lean_object* v_e_267_, lean_object* v_toBind_268_, lean_object* v___f_269_, lean_object* v___f_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
uint8_t v_a_boxed_273_; lean_object* v_res_274_; 
v_a_boxed_273_ = lean_unbox(v_a_272_);
v_res_274_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(v_f_266_, v_e_267_, v_toBind_268_, v___f_269_, v___f_270_, v_a_271_, v_a_boxed_273_);
lean_dec(v_a_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed(lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_p_277_, lean_object* v_f_278_, lean_object* v_stopWhenVisited_279_, lean_object* v_b_280_, lean_object* v___y_281_, lean_object* v_a_282_){
_start:
{
uint8_t v_stopWhenVisited_boxed_283_; lean_object* v_res_284_; 
v_stopWhenVisited_boxed_283_ = lean_unbox(v_stopWhenVisited_279_);
v_res_284_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(v_inst_275_, v_inst_276_, v_p_277_, v_f_278_, v_stopWhenVisited_boxed_283_, v_b_280_, v___y_281_, v_a_282_);
lean_dec(v___y_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_p_287_, lean_object* v_f_288_, uint8_t v_stopWhenVisited_289_, lean_object* v_body_290_, lean_object* v___y_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_285_, v_inst_286_, v_p_287_, v_f_288_, v_stopWhenVisited_289_, v_body_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed(lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_p_296_, lean_object* v_f_297_, lean_object* v_stopWhenVisited_298_, lean_object* v_body_299_, lean_object* v___y_300_, lean_object* v_a_301_){
_start:
{
uint8_t v_stopWhenVisited_boxed_302_; lean_object* v_res_303_; 
v_stopWhenVisited_boxed_302_ = lean_unbox(v_stopWhenVisited_298_);
v_res_303_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(v_inst_294_, v_inst_295_, v_p_296_, v_f_297_, v_stopWhenVisited_boxed_302_, v_body_299_, v___y_300_, v_a_301_);
lean_dec(v___y_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_p_306_, lean_object* v_f_307_, uint8_t v_stopWhenVisited_308_, lean_object* v_value_309_, lean_object* v___y_310_, lean_object* v_toBind_311_, lean_object* v___f_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_304_, v_inst_305_, v_p_306_, v_f_307_, v_stopWhenVisited_308_, v_value_309_, v___y_310_);
v___x_315_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_314_, v___f_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed(lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_p_318_, lean_object* v_f_319_, lean_object* v_stopWhenVisited_320_, lean_object* v_value_321_, lean_object* v___y_322_, lean_object* v_toBind_323_, lean_object* v___f_324_, lean_object* v_a_325_){
_start:
{
uint8_t v_stopWhenVisited_boxed_326_; lean_object* v_res_327_; 
v_stopWhenVisited_boxed_326_ = lean_unbox(v_stopWhenVisited_320_);
v_res_327_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(v_inst_316_, v_inst_317_, v_p_318_, v_f_319_, v_stopWhenVisited_boxed_326_, v_value_321_, v___y_322_, v_toBind_323_, v___f_324_, v_a_325_);
lean_dec(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_p_330_, lean_object* v_f_331_, uint8_t v_stopWhenVisited_332_, lean_object* v_arg_333_, lean_object* v___y_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_328_, v_inst_329_, v_p_330_, v_f_331_, v_stopWhenVisited_332_, v_arg_333_, v___y_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed(lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_p_339_, lean_object* v_f_340_, lean_object* v_stopWhenVisited_341_, lean_object* v_arg_342_, lean_object* v___y_343_, lean_object* v_a_344_){
_start:
{
uint8_t v_stopWhenVisited_boxed_345_; lean_object* v_res_346_; 
v_stopWhenVisited_boxed_345_ = lean_unbox(v_stopWhenVisited_341_);
v_res_346_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(v_inst_337_, v_inst_338_, v_p_339_, v_f_340_, v_stopWhenVisited_boxed_345_, v_arg_342_, v___y_343_, v_a_344_);
lean_dec(v___y_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_p_349_, lean_object* v_f_350_, uint8_t v_stopWhenVisited_351_, lean_object* v_toBind_352_, lean_object* v_e_353_, lean_object* v_toApplicative_354_, lean_object* v_____r_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_d_358_; lean_object* v_b_359_; 
switch(lean_obj_tag(v_e_353_))
{
case 7:
{
lean_object* v_binderType_364_; lean_object* v_body_365_; 
lean_dec_ref(v_toApplicative_354_);
v_binderType_364_ = lean_ctor_get(v_e_353_, 1);
lean_inc_ref(v_binderType_364_);
v_body_365_ = lean_ctor_get(v_e_353_, 2);
lean_inc_ref(v_body_365_);
lean_dec_ref(v_e_353_);
v_d_358_ = v_binderType_364_;
v_b_359_ = v_body_365_;
goto v___jp_357_;
}
case 6:
{
lean_object* v_binderType_366_; lean_object* v_body_367_; 
lean_dec_ref(v_toApplicative_354_);
v_binderType_366_ = lean_ctor_get(v_e_353_, 1);
lean_inc_ref(v_binderType_366_);
v_body_367_ = lean_ctor_get(v_e_353_, 2);
lean_inc_ref(v_body_367_);
lean_dec_ref(v_e_353_);
v_d_358_ = v_binderType_366_;
v_b_359_ = v_body_367_;
goto v___jp_357_;
}
case 8:
{
lean_object* v_type_368_; lean_object* v_value_369_; lean_object* v_body_370_; lean_object* v___x_371_; lean_object* v___f_372_; lean_object* v___x_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref(v_toApplicative_354_);
v_type_368_ = lean_ctor_get(v_e_353_, 1);
lean_inc_ref(v_type_368_);
v_value_369_ = lean_ctor_get(v_e_353_, 2);
lean_inc_ref(v_value_369_);
v_body_370_ = lean_ctor_get(v_e_353_, 3);
lean_inc_ref(v_body_370_);
lean_dec_ref(v_e_353_);
v___x_371_ = lean_box(v_stopWhenVisited_351_);
lean_inc(v___y_356_);
lean_inc(v_f_350_);
lean_inc_ref(v_p_349_);
lean_inc_ref(v_inst_348_);
lean_inc(v_inst_347_);
v___f_372_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_372_, 0, v_inst_347_);
lean_closure_set(v___f_372_, 1, v_inst_348_);
lean_closure_set(v___f_372_, 2, v_p_349_);
lean_closure_set(v___f_372_, 3, v_f_350_);
lean_closure_set(v___f_372_, 4, v___x_371_);
lean_closure_set(v___f_372_, 5, v_body_370_);
lean_closure_set(v___f_372_, 6, v___y_356_);
v___x_373_ = lean_box(v_stopWhenVisited_351_);
lean_inc(v_toBind_352_);
lean_inc(v___y_356_);
lean_inc(v_f_350_);
lean_inc_ref(v_p_349_);
lean_inc_ref(v_inst_348_);
lean_inc(v_inst_347_);
v___f_374_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_374_, 0, v_inst_347_);
lean_closure_set(v___f_374_, 1, v_inst_348_);
lean_closure_set(v___f_374_, 2, v_p_349_);
lean_closure_set(v___f_374_, 3, v_f_350_);
lean_closure_set(v___f_374_, 4, v___x_373_);
lean_closure_set(v___f_374_, 5, v_value_369_);
lean_closure_set(v___f_374_, 6, v___y_356_);
lean_closure_set(v___f_374_, 7, v_toBind_352_);
lean_closure_set(v___f_374_, 8, v___f_372_);
v___x_375_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_347_, v_inst_348_, v_p_349_, v_f_350_, v_stopWhenVisited_351_, v_type_368_, v___y_356_);
v___x_376_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v___x_375_, v___f_374_);
return v___x_376_;
}
case 5:
{
lean_object* v_fn_377_; lean_object* v_arg_378_; lean_object* v___x_379_; lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec_ref(v_toApplicative_354_);
v_fn_377_ = lean_ctor_get(v_e_353_, 0);
lean_inc_ref(v_fn_377_);
v_arg_378_ = lean_ctor_get(v_e_353_, 1);
lean_inc_ref(v_arg_378_);
lean_dec_ref(v_e_353_);
v___x_379_ = lean_box(v_stopWhenVisited_351_);
lean_inc(v___y_356_);
lean_inc(v_f_350_);
lean_inc_ref(v_p_349_);
lean_inc_ref(v_inst_348_);
lean_inc(v_inst_347_);
v___f_380_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_380_, 0, v_inst_347_);
lean_closure_set(v___f_380_, 1, v_inst_348_);
lean_closure_set(v___f_380_, 2, v_p_349_);
lean_closure_set(v___f_380_, 3, v_f_350_);
lean_closure_set(v___f_380_, 4, v___x_379_);
lean_closure_set(v___f_380_, 5, v_arg_378_);
lean_closure_set(v___f_380_, 6, v___y_356_);
v___x_381_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_347_, v_inst_348_, v_p_349_, v_f_350_, v_stopWhenVisited_351_, v_fn_377_, v___y_356_);
v___x_382_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v___x_381_, v___f_380_);
return v___x_382_;
}
case 10:
{
lean_object* v_expr_383_; lean_object* v___x_384_; 
lean_dec_ref(v_toApplicative_354_);
lean_dec(v_toBind_352_);
v_expr_383_ = lean_ctor_get(v_e_353_, 1);
lean_inc_ref(v_expr_383_);
lean_dec_ref(v_e_353_);
v___x_384_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_347_, v_inst_348_, v_p_349_, v_f_350_, v_stopWhenVisited_351_, v_expr_383_, v___y_356_);
return v___x_384_;
}
case 11:
{
lean_object* v_struct_385_; lean_object* v___x_386_; 
lean_dec_ref(v_toApplicative_354_);
lean_dec(v_toBind_352_);
v_struct_385_ = lean_ctor_get(v_e_353_, 2);
lean_inc_ref(v_struct_385_);
lean_dec_ref(v_e_353_);
v___x_386_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_347_, v_inst_348_, v_p_349_, v_f_350_, v_stopWhenVisited_351_, v_struct_385_, v___y_356_);
return v___x_386_;
}
default: 
{
lean_object* v_toPure_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref(v_e_353_);
lean_dec(v_toBind_352_);
lean_dec(v_f_350_);
lean_dec_ref(v_p_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_inst_347_);
v_toPure_387_ = lean_ctor_get(v_toApplicative_354_, 1);
lean_inc(v_toPure_387_);
lean_dec_ref(v_toApplicative_354_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_apply_2(v_toPure_387_, lean_box(0), v___x_388_);
return v___x_389_;
}
}
v___jp_357_:
{
lean_object* v___x_360_; lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = lean_box(v_stopWhenVisited_351_);
lean_inc(v___y_356_);
lean_inc(v_f_350_);
lean_inc_ref(v_p_349_);
lean_inc_ref(v_inst_348_);
lean_inc(v_inst_347_);
v___f_361_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_361_, 0, v_inst_347_);
lean_closure_set(v___f_361_, 1, v_inst_348_);
lean_closure_set(v___f_361_, 2, v_p_349_);
lean_closure_set(v___f_361_, 3, v_f_350_);
lean_closure_set(v___f_361_, 4, v___x_360_);
lean_closure_set(v___f_361_, 5, v_b_359_);
lean_closure_set(v___f_361_, 6, v___y_356_);
v___x_362_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_347_, v_inst_348_, v_p_349_, v_f_350_, v_stopWhenVisited_351_, v_d_358_, v___y_356_);
v___x_363_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v___x_362_, v___f_361_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed(lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_p_392_, lean_object* v_f_393_, lean_object* v_stopWhenVisited_394_, lean_object* v_toBind_395_, lean_object* v_e_396_, lean_object* v_toApplicative_397_, lean_object* v_____r_398_, lean_object* v___y_399_){
_start:
{
uint8_t v_stopWhenVisited_boxed_400_; lean_object* v_res_401_; 
v_stopWhenVisited_boxed_400_ = lean_unbox(v_stopWhenVisited_394_);
v_res_401_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(v_inst_390_, v_inst_391_, v_p_392_, v_f_393_, v_stopWhenVisited_boxed_400_, v_toBind_395_, v_e_396_, v_toApplicative_397_, v_____r_398_, v___y_399_);
lean_dec(v___y_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_p_404_, lean_object* v_f_405_, uint8_t v_stopWhenVisited_406_, lean_object* v_e_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_toApplicative_409_; lean_object* v_toBind_410_; lean_object* v___x_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_toApplicative_409_ = lean_ctor_get(v_inst_403_, 0);
v_toBind_410_ = lean_ctor_get(v_inst_403_, 1);
lean_inc(v_toBind_410_);
v___x_411_ = lean_box(v_stopWhenVisited_406_);
lean_inc_ref(v_toApplicative_409_);
lean_inc_ref(v_e_407_);
lean_inc(v_toBind_410_);
lean_inc(v_f_405_);
lean_inc_ref(v_p_404_);
lean_inc_ref(v_inst_403_);
lean_inc(v_inst_402_);
v___f_412_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_412_, 0, v_inst_402_);
lean_closure_set(v___f_412_, 1, v_inst_403_);
lean_closure_set(v___f_412_, 2, v_p_404_);
lean_closure_set(v___f_412_, 3, v_f_405_);
lean_closure_set(v___f_412_, 4, v___x_411_);
lean_closure_set(v___f_412_, 5, v_toBind_410_);
lean_closure_set(v___f_412_, 6, v_e_407_);
lean_closure_set(v___f_412_, 7, v_toApplicative_409_);
v___x_413_ = lean_box(v_stopWhenVisited_406_);
lean_inc_ref(v_toApplicative_409_);
lean_inc(v_a_408_);
lean_inc_ref(v___f_412_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed), 5, 4);
lean_closure_set(v___f_414_, 0, v___x_413_);
lean_closure_set(v___f_414_, 1, v___f_412_);
lean_closure_set(v___f_414_, 2, v_a_408_);
lean_closure_set(v___f_414_, 3, v_toApplicative_409_);
lean_inc(v_a_408_);
lean_inc_ref(v___f_412_);
lean_inc(v_toBind_410_);
lean_inc_ref(v_e_407_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_415_, 0, v_f_405_);
lean_closure_set(v___f_415_, 1, v_e_407_);
lean_closure_set(v___f_415_, 2, v_toBind_410_);
lean_closure_set(v___f_415_, 3, v___f_414_);
lean_closure_set(v___f_415_, 4, v___f_412_);
lean_closure_set(v___f_415_, 5, v_a_408_);
lean_inc_ref(v_toApplicative_409_);
lean_inc(v_toBind_410_);
lean_inc_ref(v_inst_403_);
lean_inc(v_inst_402_);
lean_inc(v_a_408_);
lean_inc_ref(v_e_407_);
v___f_416_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed), 10, 9);
lean_closure_set(v___f_416_, 0, v_p_404_);
lean_closure_set(v___f_416_, 1, v_e_407_);
lean_closure_set(v___f_416_, 2, v___f_412_);
lean_closure_set(v___f_416_, 3, v_a_408_);
lean_closure_set(v___f_416_, 4, v_inst_402_);
lean_closure_set(v___f_416_, 5, v_inst_403_);
lean_closure_set(v___f_416_, 6, v_toBind_410_);
lean_closure_set(v___f_416_, 7, v___f_415_);
lean_closure_set(v___f_416_, 8, v_toApplicative_409_);
v___x_417_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_402_, v_inst_403_, v_e_407_, v_a_408_);
v___x_418_ = lean_apply_4(v_toBind_410_, lean_box(0), lean_box(0), v___x_417_, v___f_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_p_421_, lean_object* v_f_422_, uint8_t v_stopWhenVisited_423_, lean_object* v_b_424_, lean_object* v___y_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_419_, v_inst_420_, v_p_421_, v_f_422_, v_stopWhenVisited_423_, v_b_424_, v___y_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___boxed(lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_p_430_, lean_object* v_f_431_, lean_object* v_stopWhenVisited_432_, lean_object* v_e_433_, lean_object* v_a_434_){
_start:
{
uint8_t v_stopWhenVisited_boxed_435_; lean_object* v_res_436_; 
v_stopWhenVisited_boxed_435_ = lean_unbox(v_stopWhenVisited_432_);
v_res_436_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_428_, v_inst_429_, v_p_430_, v_f_431_, v_stopWhenVisited_boxed_435_, v_e_433_, v_a_434_);
lean_dec(v_a_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(lean_object* v_00_u03c9_437_, lean_object* v_m_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_p_442_, lean_object* v_f_443_, uint8_t v_stopWhenVisited_444_, lean_object* v_e_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_440_, v_inst_441_, v_p_442_, v_f_443_, v_stopWhenVisited_444_, v_e_445_, v_a_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___boxed(lean_object* v_00_u03c9_448_, lean_object* v_m_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_p_453_, lean_object* v_f_454_, lean_object* v_stopWhenVisited_455_, lean_object* v_e_456_, lean_object* v_a_457_){
_start:
{
uint8_t v_stopWhenVisited_boxed_458_; lean_object* v_res_459_; 
v_stopWhenVisited_boxed_458_ = lean_unbox(v_stopWhenVisited_455_);
v_res_459_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(v_00_u03c9_448_, v_m_449_, v_inst_450_, v_inst_451_, v_inst_452_, v_p_453_, v_f_454_, v_stopWhenVisited_boxed_458_, v_e_456_, v_a_457_);
lean_dec(v_a_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__0(lean_object* v_a_460_, lean_object* v_toPure_461_, lean_object* v_s_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_a_460_);
lean_ctor_set(v___x_463_, 1, v_s_462_);
v___x_464_ = lean_apply_2(v_toPure_461_, lean_box(0), v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__1(lean_object* v_toPure_465_, lean_object* v_ref_466_, lean_object* v_inst_467_, lean_object* v_toBind_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___f_470_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_470_, 0, v_a_469_);
lean_closure_set(v___f_470_, 1, v_toPure_465_);
v___x_471_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_471_, 0, lean_box(0));
lean_closure_set(v___x_471_, 1, lean_box(0));
lean_closure_set(v___x_471_, 2, v_ref_466_);
v___x_472_ = lean_apply_2(v_inst_467_, lean_box(0), v___x_471_);
v___x_473_ = lean_apply_4(v_toBind_468_, lean_box(0), lean_box(0), v___x_472_, v___f_470_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2(lean_object* v_toPure_474_, lean_object* v_inst_475_, lean_object* v_toBind_476_, lean_object* v_inst_477_, lean_object* v_p_478_, lean_object* v_f_479_, uint8_t v_stopWhenVisited_480_, lean_object* v_e_481_, lean_object* v_ref_482_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v_toBind_476_);
lean_inc(v_inst_475_);
lean_inc(v_ref_482_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_483_, 0, v_toPure_474_);
lean_closure_set(v___f_483_, 1, v_ref_482_);
lean_closure_set(v___f_483_, 2, v_inst_475_);
lean_closure_set(v___f_483_, 3, v_toBind_476_);
v___x_484_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_475_, v_inst_477_, v_p_478_, v_f_479_, v_stopWhenVisited_480_, v_e_481_, v_ref_482_);
lean_dec(v_ref_482_);
v___x_485_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v___x_484_, v___f_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed(lean_object* v_toPure_486_, lean_object* v_inst_487_, lean_object* v_toBind_488_, lean_object* v_inst_489_, lean_object* v_p_490_, lean_object* v_f_491_, lean_object* v_stopWhenVisited_492_, lean_object* v_e_493_, lean_object* v_ref_494_){
_start:
{
uint8_t v_stopWhenVisited_boxed_495_; lean_object* v_res_496_; 
v_stopWhenVisited_boxed_495_ = lean_unbox(v_stopWhenVisited_492_);
v_res_496_ = l_Lean_ForEachExprWhere_visit___redArg___lam__2(v_toPure_486_, v_inst_487_, v_toBind_488_, v_inst_489_, v_p_490_, v_f_491_, v_stopWhenVisited_boxed_495_, v_e_493_, v_ref_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__3(lean_object* v_toPure_497_, lean_object* v_____x_498_){
_start:
{
lean_object* v_fst_499_; lean_object* v___x_500_; 
v_fst_499_ = lean_ctor_get(v_____x_498_, 0);
lean_inc(v_fst_499_);
lean_dec_ref(v_____x_498_);
v___x_500_ = lean_apply_2(v_toPure_497_, lean_box(0), v_fst_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = l_Lean_ForEachExprWhere_initCache;
v___x_502_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_502_, 0, lean_box(0));
lean_closure_set(v___x_502_, 1, lean_box(0));
lean_closure_set(v___x_502_, 2, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg(lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_p_505_, lean_object* v_f_506_, lean_object* v_e_507_, uint8_t v_stopWhenVisited_508_){
_start:
{
lean_object* v_toApplicative_509_; lean_object* v_toBind_510_; lean_object* v_toPure_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_toApplicative_509_ = lean_ctor_get(v_inst_504_, 0);
v_toBind_510_ = lean_ctor_get(v_inst_504_, 1);
lean_inc(v_toBind_510_);
v_toPure_511_ = lean_ctor_get(v_toApplicative_509_, 1);
lean_inc(v_toPure_511_);
v___x_512_ = lean_obj_once(&l_Lean_ForEachExprWhere_visit___redArg___closed__0, &l_Lean_ForEachExprWhere_visit___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0);
lean_inc(v_inst_503_);
v___x_513_ = lean_apply_2(v_inst_503_, lean_box(0), v___x_512_);
v___x_514_ = lean_box(v_stopWhenVisited_508_);
lean_inc(v_toBind_510_);
lean_inc(v_toPure_511_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_515_, 0, v_toPure_511_);
lean_closure_set(v___f_515_, 1, v_inst_503_);
lean_closure_set(v___f_515_, 2, v_toBind_510_);
lean_closure_set(v___f_515_, 3, v_inst_504_);
lean_closure_set(v___f_515_, 4, v_p_505_);
lean_closure_set(v___f_515_, 5, v_f_506_);
lean_closure_set(v___f_515_, 6, v___x_514_);
lean_closure_set(v___f_515_, 7, v_e_507_);
v___f_516_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__3), 2, 1);
lean_closure_set(v___f_516_, 0, v_toPure_511_);
lean_inc(v_toBind_510_);
v___x_517_ = lean_apply_4(v_toBind_510_, lean_box(0), lean_box(0), v___x_513_, v___f_515_);
v___x_518_ = lean_apply_4(v_toBind_510_, lean_box(0), lean_box(0), v___x_517_, v___f_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___boxed(lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_p_521_, lean_object* v_f_522_, lean_object* v_e_523_, lean_object* v_stopWhenVisited_524_){
_start:
{
uint8_t v_stopWhenVisited_boxed_525_; lean_object* v_res_526_; 
v_stopWhenVisited_boxed_525_ = lean_unbox(v_stopWhenVisited_524_);
v_res_526_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_519_, v_inst_520_, v_p_521_, v_f_522_, v_e_523_, v_stopWhenVisited_boxed_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit(lean_object* v_00_u03c9_527_, lean_object* v_m_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_p_532_, lean_object* v_f_533_, lean_object* v_e_534_, uint8_t v_stopWhenVisited_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_530_, v_inst_531_, v_p_532_, v_f_533_, v_e_534_, v_stopWhenVisited_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___boxed(lean_object* v_00_u03c9_537_, lean_object* v_m_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_p_542_, lean_object* v_f_543_, lean_object* v_e_544_, lean_object* v_stopWhenVisited_545_){
_start:
{
uint8_t v_stopWhenVisited_boxed_546_; lean_object* v_res_547_; 
v_stopWhenVisited_boxed_546_ = lean_unbox(v_stopWhenVisited_545_);
v_res_547_ = l_Lean_ForEachExprWhere_visit(v_00_u03c9_537_, v_m_538_, v_inst_539_, v_inst_540_, v_inst_541_, v_p_542_, v_f_543_, v_e_544_, v_stopWhenVisited_boxed_546_);
return v_res_547_;
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
