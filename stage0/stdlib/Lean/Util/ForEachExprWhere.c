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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_unsigned_to_nat(16u);
v___x_10_ = lean_mk_array(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__2(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__1, &l_Lean_ForEachExprWhere_initCache___closed__1_once, _init_l_Lean_ForEachExprWhere_initCache___closed__1);
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache___closed__3(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__2, &l_Lean_ForEachExprWhere_initCache___closed__2_once, _init_l_Lean_ForEachExprWhere_initCache___closed__2);
v___x_15_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__0, &l_Lean_ForEachExprWhere_initCache___closed__0_once, _init_l_Lean_ForEachExprWhere_initCache___closed__0);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_initCache(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Lean_ForEachExprWhere_initCache___closed__3, &l_Lean_ForEachExprWhere_initCache___closed__3_once, _init_l_Lean_ForEachExprWhere_initCache___closed__3);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0(size_t v___x_18_, lean_object* v_e_19_, lean_object* v_s_20_){
_start:
{
lean_object* v_visited_21_; lean_object* v_checked_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_32_; 
v_visited_21_ = lean_ctor_get(v_s_20_, 0);
v_checked_22_ = lean_ctor_get(v_s_20_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_s_20_);
if (v_isSharedCheck_32_ == 0)
{
v___x_24_ = v_s_20_;
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_checked_22_);
lean_inc(v_visited_21_);
lean_dec(v_s_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_26_ = lean_box(0);
v___x_27_ = lean_array_uset(v_visited_21_, v___x_18_, v_e_19_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_27_);
v___x_29_ = v___x_24_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_checked_22_);
v___x_29_ = v_reuseFailAlloc_31_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_26_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed(lean_object* v___x_33_, lean_object* v_e_34_, lean_object* v_s_35_){
_start:
{
size_t v___x_322__boxed_36_; lean_object* v_res_37_; 
v___x_322__boxed_36_ = lean_unbox_usize(v___x_33_);
lean_dec(v___x_33_);
v_res_37_ = l_Lean_ForEachExprWhere_visited___redArg___lam__0(v___x_322__boxed_36_, v_e_34_, v_s_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1(lean_object* v_toApplicative_38_, uint8_t v___x_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_toPure_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_toPure_41_ = lean_ctor_get(v_toApplicative_38_, 1);
lean_inc(v_toPure_41_);
lean_dec_ref(v_toApplicative_38_);
v___x_42_ = lean_box(v___x_39_);
v___x_43_ = lean_apply_2(v_toPure_41_, lean_box(0), v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed(lean_object* v_toApplicative_44_, lean_object* v___x_45_, lean_object* v_a_46_){
_start:
{
uint8_t v___x_345__boxed_47_; lean_object* v_res_48_; 
v___x_345__boxed_47_ = lean_unbox(v___x_45_);
v_res_48_ = l_Lean_ForEachExprWhere_visited___redArg___lam__1(v_toApplicative_44_, v___x_345__boxed_47_, v_a_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2(lean_object* v_e_49_, lean_object* v_toApplicative_50_, lean_object* v_a_51_, lean_object* v_inst_52_, lean_object* v_toBind_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_visited_55_; size_t v___x_56_; size_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; size_t v___x_60_; uint8_t v___x_61_; 
v_visited_55_ = lean_ctor_get(v_a_54_, 0);
v___x_56_ = lean_ptr_addr(v_e_49_);
v___x_57_ = ((size_t)8191ULL);
v___x_58_ = lean_usize_mod(v___x_56_, v___x_57_);
v___x_59_ = lean_array_uget_borrowed(v_visited_55_, v___x_58_);
v___x_60_ = lean_ptr_addr(v___x_59_);
v___x_61_ = lean_usize_dec_eq(v___x_60_, v___x_56_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_62_ = lean_box_usize(v___x_58_);
v___f_63_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_63_, 0, v___x_62_);
lean_closure_set(v___f_63_, 1, v_e_49_);
v___x_64_ = lean_box(v___x_61_);
v___f_65_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_65_, 0, v_toApplicative_50_);
lean_closure_set(v___f_65_, 1, v___x_64_);
lean_inc(v_a_51_);
v___x_66_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_66_, 0, lean_box(0));
lean_closure_set(v___x_66_, 1, lean_box(0));
lean_closure_set(v___x_66_, 2, lean_box(0));
lean_closure_set(v___x_66_, 3, v_a_51_);
lean_closure_set(v___x_66_, 4, v___f_63_);
v___x_67_ = lean_apply_2(v_inst_52_, lean_box(0), v___x_66_);
v___x_68_ = lean_apply_4(v_toBind_53_, lean_box(0), lean_box(0), v___x_67_, v___f_65_);
return v___x_68_;
}
else
{
lean_object* v_toPure_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_toBind_53_);
lean_dec(v_inst_52_);
lean_dec_ref(v_e_49_);
v_toPure_69_ = lean_ctor_get(v_toApplicative_50_, 1);
lean_inc(v_toPure_69_);
lean_dec_ref(v_toApplicative_50_);
v___x_70_ = lean_box(v___x_61_);
v___x_71_ = lean_apply_2(v_toPure_69_, lean_box(0), v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed(lean_object* v_e_72_, lean_object* v_toApplicative_73_, lean_object* v_a_74_, lean_object* v_inst_75_, lean_object* v_toBind_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_ForEachExprWhere_visited___redArg___lam__2(v_e_72_, v_toApplicative_73_, v_a_74_, v_inst_75_, v_toBind_76_, v_a_77_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_74_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg(lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_e_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_toApplicative_83_; lean_object* v_toBind_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_toApplicative_83_ = lean_ctor_get(v_inst_80_, 0);
lean_inc_ref(v_toApplicative_83_);
v_toBind_84_ = lean_ctor_get(v_inst_80_, 1);
lean_inc_n(v_toBind_84_, 2);
lean_dec_ref(v_inst_80_);
lean_inc(v_inst_79_);
lean_inc_n(v_a_82_, 2);
v___f_85_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visited___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_85_, 0, v_e_81_);
lean_closure_set(v___f_85_, 1, v_toApplicative_83_);
lean_closure_set(v___f_85_, 2, v_a_82_);
lean_closure_set(v___f_85_, 3, v_inst_79_);
lean_closure_set(v___f_85_, 4, v_toBind_84_);
v___x_86_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_86_, 0, lean_box(0));
lean_closure_set(v___x_86_, 1, lean_box(0));
lean_closure_set(v___x_86_, 2, v_a_82_);
v___x_87_ = lean_apply_2(v_inst_79_, lean_box(0), v___x_86_);
v___x_88_ = lean_apply_4(v_toBind_84_, lean_box(0), lean_box(0), v___x_87_, v___f_85_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___boxed(lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_e_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_89_, v_inst_90_, v_e_91_, v_a_92_);
lean_dec(v_a_92_);
return v_res_93_;
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
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___boxed(lean_object* v_00_u03c9_102_, lean_object* v_m_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_e_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_ForEachExprWhere_visited(v_00_u03c9_102_, v_m_103_, v_inst_104_, v_inst_105_, v_inst_106_, v_e_107_, v_a_108_);
lean_dec(v_a_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__0(lean_object* v___x_110_, lean_object* v___x_111_, lean_object* v_e_112_, lean_object* v_s_113_){
_start:
{
lean_object* v_visited_114_; lean_object* v_checked_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_125_; 
v_visited_114_ = lean_ctor_get(v_s_113_, 0);
v_checked_115_ = lean_ctor_get(v_s_113_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_s_113_);
if (v_isSharedCheck_125_ == 0)
{
v___x_117_ = v_s_113_;
v_isShared_118_ = v_isSharedCheck_125_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_checked_115_);
lean_inc(v_visited_114_);
lean_dec(v_s_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_125_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_119_ = lean_box(0);
v___x_120_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_110_, v___x_111_, v_checked_115_, v_e_112_, v___x_119_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_120_);
v___x_122_ = v___x_117_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_visited_114_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_124_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_119_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1(lean_object* v_toApplicative_126_, uint8_t v___x_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_toPure_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_toPure_129_ = lean_ctor_get(v_toApplicative_126_, 1);
lean_inc(v_toPure_129_);
lean_dec_ref(v_toApplicative_126_);
v___x_130_ = lean_box(v___x_127_);
v___x_131_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed(lean_object* v_toApplicative_132_, lean_object* v___x_133_, lean_object* v_a_134_){
_start:
{
uint8_t v___x_371__boxed_135_; lean_object* v_res_136_; 
v___x_371__boxed_135_ = lean_unbox(v___x_133_);
v_res_136_ = l_Lean_ForEachExprWhere_checked___redArg___lam__1(v_toApplicative_132_, v___x_371__boxed_135_, v_a_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2(lean_object* v___x_137_, lean_object* v___x_138_, lean_object* v_e_139_, lean_object* v_toApplicative_140_, lean_object* v_a_141_, lean_object* v___f_142_, lean_object* v_inst_143_, lean_object* v_toBind_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_checked_146_; uint8_t v___x_147_; 
v_checked_146_ = lean_ctor_get(v_a_145_, 1);
v___x_147_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_137_, v___x_138_, v_checked_146_, v_e_139_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_148_ = lean_box(v___x_147_);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_149_, 0, v_toApplicative_140_);
lean_closure_set(v___f_149_, 1, v___x_148_);
lean_inc(v_a_141_);
v___x_150_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_150_, 0, lean_box(0));
lean_closure_set(v___x_150_, 1, lean_box(0));
lean_closure_set(v___x_150_, 2, lean_box(0));
lean_closure_set(v___x_150_, 3, v_a_141_);
lean_closure_set(v___x_150_, 4, v___f_142_);
v___x_151_ = lean_apply_2(v_inst_143_, lean_box(0), v___x_150_);
v___x_152_ = lean_apply_4(v_toBind_144_, lean_box(0), lean_box(0), v___x_151_, v___f_149_);
return v___x_152_;
}
else
{
lean_object* v_toPure_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_toBind_144_);
lean_dec(v_inst_143_);
lean_dec_ref(v___f_142_);
v_toPure_153_ = lean_ctor_get(v_toApplicative_140_, 1);
lean_inc(v_toPure_153_);
lean_dec_ref(v_toApplicative_140_);
v___x_154_ = lean_box(v___x_147_);
v___x_155_ = lean_apply_2(v_toPure_153_, lean_box(0), v___x_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed(lean_object* v___x_156_, lean_object* v___x_157_, lean_object* v_e_158_, lean_object* v_toApplicative_159_, lean_object* v_a_160_, lean_object* v___f_161_, lean_object* v_inst_162_, lean_object* v_toBind_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_ForEachExprWhere_checked___redArg___lam__2(v___x_156_, v___x_157_, v_e_158_, v_toApplicative_159_, v_a_160_, v___f_161_, v_inst_162_, v_toBind_163_, v_a_164_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg(lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_e_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_toApplicative_172_; lean_object* v_toBind_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_toApplicative_172_ = lean_ctor_get(v_inst_169_, 0);
lean_inc_ref(v_toApplicative_172_);
v_toBind_173_ = lean_ctor_get(v_inst_169_, 1);
lean_inc_n(v_toBind_173_, 2);
lean_dec_ref(v_inst_169_);
v___x_174_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__0));
v___x_175_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__1));
lean_inc_ref(v_e_170_);
v___f_176_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__0), 4, 3);
lean_closure_set(v___f_176_, 0, v___x_174_);
lean_closure_set(v___f_176_, 1, v___x_175_);
lean_closure_set(v___f_176_, 2, v_e_170_);
lean_inc(v_inst_168_);
lean_inc_n(v_a_171_, 2);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_177_, 0, v___x_174_);
lean_closure_set(v___f_177_, 1, v___x_175_);
lean_closure_set(v___f_177_, 2, v_e_170_);
lean_closure_set(v___f_177_, 3, v_toApplicative_172_);
lean_closure_set(v___f_177_, 4, v_a_171_);
lean_closure_set(v___f_177_, 5, v___f_176_);
lean_closure_set(v___f_177_, 6, v_inst_168_);
lean_closure_set(v___f_177_, 7, v_toBind_173_);
v___x_178_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_178_, 0, lean_box(0));
lean_closure_set(v___x_178_, 1, lean_box(0));
lean_closure_set(v___x_178_, 2, v_a_171_);
v___x_179_ = lean_apply_2(v_inst_168_, lean_box(0), v___x_178_);
v___x_180_ = lean_apply_4(v_toBind_173_, lean_box(0), lean_box(0), v___x_179_, v___f_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___boxed(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_e_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_181_, v_inst_182_, v_e_183_, v_a_184_);
lean_dec(v_a_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked(lean_object* v_00_u03c9_186_, lean_object* v_m_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_e_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_189_, v_inst_190_, v_e_191_, v_a_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___boxed(lean_object* v_00_u03c9_194_, lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_e_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_ForEachExprWhere_checked(v_00_u03c9_194_, v_m_195_, v_inst_196_, v_inst_197_, v_inst_198_, v_e_199_, v_a_200_);
lean_dec(v_a_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(lean_object* v_p_202_, lean_object* v_e_203_, lean_object* v___f_204_, lean_object* v_a_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_toBind_208_, lean_object* v___f_209_, lean_object* v_toApplicative_210_, uint8_t v_a_211_){
_start:
{
if (v_a_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
lean_dec_ref(v_toApplicative_210_);
lean_inc_ref(v_e_203_);
v___x_212_ = lean_apply_1(v_p_202_, v_e_203_);
v___x_213_ = lean_unbox(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v___f_209_);
lean_dec(v_toBind_208_);
lean_dec_ref(v_inst_207_);
lean_dec(v_inst_206_);
lean_dec_ref(v_e_203_);
v___x_214_ = lean_box(0);
lean_inc(v_a_205_);
v___x_215_ = lean_apply_2(v___f_204_, v___x_214_, v_a_205_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v___f_204_);
v___x_216_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_206_, v_inst_207_, v_e_203_, v_a_205_);
v___x_217_ = lean_apply_4(v_toBind_208_, lean_box(0), lean_box(0), v___x_216_, v___f_209_);
return v___x_217_;
}
}
else
{
lean_object* v_toPure_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___f_209_);
lean_dec(v_toBind_208_);
lean_dec_ref(v_inst_207_);
lean_dec(v_inst_206_);
lean_dec(v___f_204_);
lean_dec_ref(v_e_203_);
lean_dec_ref(v_p_202_);
v_toPure_218_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_inc(v_toPure_218_);
lean_dec_ref(v_toApplicative_210_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_apply_2(v_toPure_218_, lean_box(0), v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed(lean_object* v_p_221_, lean_object* v_e_222_, lean_object* v___f_223_, lean_object* v_a_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_toBind_227_, lean_object* v___f_228_, lean_object* v_toApplicative_229_, lean_object* v_a_230_){
_start:
{
uint8_t v_a_boxed_231_; lean_object* v_res_232_; 
v_a_boxed_231_ = lean_unbox(v_a_230_);
v_res_232_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(v_p_221_, v_e_222_, v___f_223_, v_a_224_, v_inst_225_, v_inst_226_, v_toBind_227_, v___f_228_, v_toApplicative_229_, v_a_boxed_231_);
lean_dec(v_a_224_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(uint8_t v_stopWhenVisited_233_, lean_object* v___f_234_, lean_object* v_a_235_, lean_object* v_toApplicative_236_, lean_object* v_a_237_){
_start:
{
if (v_stopWhenVisited_233_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_toApplicative_236_);
v___x_238_ = lean_box(0);
lean_inc(v_a_235_);
v___x_239_ = lean_apply_2(v___f_234_, v___x_238_, v_a_235_);
return v___x_239_;
}
else
{
lean_object* v_toPure_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v___f_234_);
v_toPure_240_ = lean_ctor_get(v_toApplicative_236_, 1);
lean_inc(v_toPure_240_);
lean_dec_ref(v_toApplicative_236_);
v___x_241_ = lean_box(0);
v___x_242_ = lean_apply_2(v_toPure_240_, lean_box(0), v___x_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed(lean_object* v_stopWhenVisited_243_, lean_object* v___f_244_, lean_object* v_a_245_, lean_object* v_toApplicative_246_, lean_object* v_a_247_){
_start:
{
uint8_t v_stopWhenVisited_boxed_248_; lean_object* v_res_249_; 
v_stopWhenVisited_boxed_248_ = lean_unbox(v_stopWhenVisited_243_);
v_res_249_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(v_stopWhenVisited_boxed_248_, v___f_244_, v_a_245_, v_toApplicative_246_, v_a_247_);
lean_dec(v_a_245_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(lean_object* v_f_250_, lean_object* v_e_251_, lean_object* v_toBind_252_, lean_object* v___f_253_, lean_object* v___f_254_, lean_object* v_a_255_, uint8_t v_a_256_){
_start:
{
if (v_a_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___f_254_);
v___x_257_ = lean_apply_1(v_f_250_, v_e_251_);
v___x_258_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v___x_257_, v___f_253_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v___f_253_);
lean_dec(v_toBind_252_);
lean_dec_ref(v_e_251_);
lean_dec(v_f_250_);
v___x_259_ = lean_box(0);
lean_inc(v_a_255_);
v___x_260_ = lean_apply_2(v___f_254_, v___x_259_, v_a_255_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed(lean_object* v_f_261_, lean_object* v_e_262_, lean_object* v_toBind_263_, lean_object* v___f_264_, lean_object* v___f_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
uint8_t v_a_boxed_268_; lean_object* v_res_269_; 
v_a_boxed_268_ = lean_unbox(v_a_267_);
v_res_269_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(v_f_261_, v_e_262_, v_toBind_263_, v___f_264_, v___f_265_, v_a_266_, v_a_boxed_268_);
lean_dec(v_a_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_p_272_, lean_object* v_f_273_, lean_object* v_stopWhenVisited_274_, lean_object* v_b_275_, lean_object* v___y_276_, lean_object* v_a_277_){
_start:
{
uint8_t v_stopWhenVisited_boxed_278_; lean_object* v_res_279_; 
v_stopWhenVisited_boxed_278_ = lean_unbox(v_stopWhenVisited_274_);
v_res_279_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(v_inst_270_, v_inst_271_, v_p_272_, v_f_273_, v_stopWhenVisited_boxed_278_, v_b_275_, v___y_276_, v_a_277_);
lean_dec(v___y_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_p_282_, lean_object* v_f_283_, uint8_t v_stopWhenVisited_284_, lean_object* v_body_285_, lean_object* v___y_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_280_, v_inst_281_, v_p_282_, v_f_283_, v_stopWhenVisited_284_, v_body_285_, v___y_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed(lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_p_291_, lean_object* v_f_292_, lean_object* v_stopWhenVisited_293_, lean_object* v_body_294_, lean_object* v___y_295_, lean_object* v_a_296_){
_start:
{
uint8_t v_stopWhenVisited_boxed_297_; lean_object* v_res_298_; 
v_stopWhenVisited_boxed_297_ = lean_unbox(v_stopWhenVisited_293_);
v_res_298_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(v_inst_289_, v_inst_290_, v_p_291_, v_f_292_, v_stopWhenVisited_boxed_297_, v_body_294_, v___y_295_, v_a_296_);
lean_dec(v___y_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_p_301_, lean_object* v_f_302_, uint8_t v_stopWhenVisited_303_, lean_object* v_value_304_, lean_object* v___y_305_, lean_object* v_toBind_306_, lean_object* v___f_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_299_, v_inst_300_, v_p_301_, v_f_302_, v_stopWhenVisited_303_, v_value_304_, v___y_305_);
v___x_310_ = lean_apply_4(v_toBind_306_, lean_box(0), lean_box(0), v___x_309_, v___f_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed(lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_p_313_, lean_object* v_f_314_, lean_object* v_stopWhenVisited_315_, lean_object* v_value_316_, lean_object* v___y_317_, lean_object* v_toBind_318_, lean_object* v___f_319_, lean_object* v_a_320_){
_start:
{
uint8_t v_stopWhenVisited_boxed_321_; lean_object* v_res_322_; 
v_stopWhenVisited_boxed_321_ = lean_unbox(v_stopWhenVisited_315_);
v_res_322_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(v_inst_311_, v_inst_312_, v_p_313_, v_f_314_, v_stopWhenVisited_boxed_321_, v_value_316_, v___y_317_, v_toBind_318_, v___f_319_, v_a_320_);
lean_dec(v___y_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_p_325_, lean_object* v_f_326_, uint8_t v_stopWhenVisited_327_, lean_object* v_arg_328_, lean_object* v___y_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_323_, v_inst_324_, v_p_325_, v_f_326_, v_stopWhenVisited_327_, v_arg_328_, v___y_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed(lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_p_334_, lean_object* v_f_335_, lean_object* v_stopWhenVisited_336_, lean_object* v_arg_337_, lean_object* v___y_338_, lean_object* v_a_339_){
_start:
{
uint8_t v_stopWhenVisited_boxed_340_; lean_object* v_res_341_; 
v_stopWhenVisited_boxed_340_ = lean_unbox(v_stopWhenVisited_336_);
v_res_341_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(v_inst_332_, v_inst_333_, v_p_334_, v_f_335_, v_stopWhenVisited_boxed_340_, v_arg_337_, v___y_338_, v_a_339_);
lean_dec(v___y_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_p_344_, lean_object* v_f_345_, uint8_t v_stopWhenVisited_346_, lean_object* v_toBind_347_, lean_object* v_e_348_, lean_object* v_toApplicative_349_, lean_object* v_____r_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_d_353_; lean_object* v_b_354_; 
switch(lean_obj_tag(v_e_348_))
{
case 7:
{
lean_object* v_binderType_359_; lean_object* v_body_360_; 
lean_dec_ref(v_toApplicative_349_);
v_binderType_359_ = lean_ctor_get(v_e_348_, 1);
lean_inc_ref(v_binderType_359_);
v_body_360_ = lean_ctor_get(v_e_348_, 2);
lean_inc_ref(v_body_360_);
lean_dec_ref_known(v_e_348_, 3);
v_d_353_ = v_binderType_359_;
v_b_354_ = v_body_360_;
goto v___jp_352_;
}
case 6:
{
lean_object* v_binderType_361_; lean_object* v_body_362_; 
lean_dec_ref(v_toApplicative_349_);
v_binderType_361_ = lean_ctor_get(v_e_348_, 1);
lean_inc_ref(v_binderType_361_);
v_body_362_ = lean_ctor_get(v_e_348_, 2);
lean_inc_ref(v_body_362_);
lean_dec_ref_known(v_e_348_, 3);
v_d_353_ = v_binderType_361_;
v_b_354_ = v_body_362_;
goto v___jp_352_;
}
case 8:
{
lean_object* v_type_363_; lean_object* v_value_364_; lean_object* v_body_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v_toApplicative_349_);
v_type_363_ = lean_ctor_get(v_e_348_, 1);
lean_inc_ref(v_type_363_);
v_value_364_ = lean_ctor_get(v_e_348_, 2);
lean_inc_ref(v_value_364_);
v_body_365_ = lean_ctor_get(v_e_348_, 3);
lean_inc_ref(v_body_365_);
lean_dec_ref_known(v_e_348_, 4);
v___x_366_ = lean_box(v_stopWhenVisited_346_);
lean_inc_n(v___y_351_, 2);
lean_inc_n(v_f_345_, 2);
lean_inc_ref_n(v_p_344_, 2);
lean_inc_ref_n(v_inst_343_, 2);
lean_inc_n(v_inst_342_, 2);
v___f_367_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_367_, 0, v_inst_342_);
lean_closure_set(v___f_367_, 1, v_inst_343_);
lean_closure_set(v___f_367_, 2, v_p_344_);
lean_closure_set(v___f_367_, 3, v_f_345_);
lean_closure_set(v___f_367_, 4, v___x_366_);
lean_closure_set(v___f_367_, 5, v_body_365_);
lean_closure_set(v___f_367_, 6, v___y_351_);
v___x_368_ = lean_box(v_stopWhenVisited_346_);
lean_inc(v_toBind_347_);
v___f_369_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_369_, 0, v_inst_342_);
lean_closure_set(v___f_369_, 1, v_inst_343_);
lean_closure_set(v___f_369_, 2, v_p_344_);
lean_closure_set(v___f_369_, 3, v_f_345_);
lean_closure_set(v___f_369_, 4, v___x_368_);
lean_closure_set(v___f_369_, 5, v_value_364_);
lean_closure_set(v___f_369_, 6, v___y_351_);
lean_closure_set(v___f_369_, 7, v_toBind_347_);
lean_closure_set(v___f_369_, 8, v___f_367_);
v___x_370_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_342_, v_inst_343_, v_p_344_, v_f_345_, v_stopWhenVisited_346_, v_type_363_, v___y_351_);
v___x_371_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_370_, v___f_369_);
return v___x_371_;
}
case 5:
{
lean_object* v_fn_372_; lean_object* v_arg_373_; lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec_ref(v_toApplicative_349_);
v_fn_372_ = lean_ctor_get(v_e_348_, 0);
lean_inc_ref(v_fn_372_);
v_arg_373_ = lean_ctor_get(v_e_348_, 1);
lean_inc_ref(v_arg_373_);
lean_dec_ref_known(v_e_348_, 2);
v___x_374_ = lean_box(v_stopWhenVisited_346_);
lean_inc(v___y_351_);
lean_inc(v_f_345_);
lean_inc_ref(v_p_344_);
lean_inc_ref(v_inst_343_);
lean_inc(v_inst_342_);
v___f_375_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_375_, 0, v_inst_342_);
lean_closure_set(v___f_375_, 1, v_inst_343_);
lean_closure_set(v___f_375_, 2, v_p_344_);
lean_closure_set(v___f_375_, 3, v_f_345_);
lean_closure_set(v___f_375_, 4, v___x_374_);
lean_closure_set(v___f_375_, 5, v_arg_373_);
lean_closure_set(v___f_375_, 6, v___y_351_);
v___x_376_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_342_, v_inst_343_, v_p_344_, v_f_345_, v_stopWhenVisited_346_, v_fn_372_, v___y_351_);
v___x_377_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_376_, v___f_375_);
return v___x_377_;
}
case 10:
{
lean_object* v_expr_378_; lean_object* v___x_379_; 
lean_dec_ref(v_toApplicative_349_);
lean_dec(v_toBind_347_);
v_expr_378_ = lean_ctor_get(v_e_348_, 1);
lean_inc_ref(v_expr_378_);
lean_dec_ref_known(v_e_348_, 2);
v___x_379_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_342_, v_inst_343_, v_p_344_, v_f_345_, v_stopWhenVisited_346_, v_expr_378_, v___y_351_);
return v___x_379_;
}
case 11:
{
lean_object* v_struct_380_; lean_object* v___x_381_; 
lean_dec_ref(v_toApplicative_349_);
lean_dec(v_toBind_347_);
v_struct_380_ = lean_ctor_get(v_e_348_, 2);
lean_inc_ref(v_struct_380_);
lean_dec_ref_known(v_e_348_, 3);
v___x_381_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_342_, v_inst_343_, v_p_344_, v_f_345_, v_stopWhenVisited_346_, v_struct_380_, v___y_351_);
return v___x_381_;
}
default: 
{
lean_object* v_toPure_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec_ref(v_e_348_);
lean_dec(v_toBind_347_);
lean_dec(v_f_345_);
lean_dec_ref(v_p_344_);
lean_dec_ref(v_inst_343_);
lean_dec(v_inst_342_);
v_toPure_382_ = lean_ctor_get(v_toApplicative_349_, 1);
lean_inc(v_toPure_382_);
lean_dec_ref(v_toApplicative_349_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_apply_2(v_toPure_382_, lean_box(0), v___x_383_);
return v___x_384_;
}
}
v___jp_352_:
{
lean_object* v___x_355_; lean_object* v___f_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_box(v_stopWhenVisited_346_);
lean_inc(v___y_351_);
lean_inc(v_f_345_);
lean_inc_ref(v_p_344_);
lean_inc_ref(v_inst_343_);
lean_inc(v_inst_342_);
v___f_356_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_356_, 0, v_inst_342_);
lean_closure_set(v___f_356_, 1, v_inst_343_);
lean_closure_set(v___f_356_, 2, v_p_344_);
lean_closure_set(v___f_356_, 3, v_f_345_);
lean_closure_set(v___f_356_, 4, v___x_355_);
lean_closure_set(v___f_356_, 5, v_b_354_);
lean_closure_set(v___f_356_, 6, v___y_351_);
v___x_357_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_342_, v_inst_343_, v_p_344_, v_f_345_, v_stopWhenVisited_346_, v_d_353_, v___y_351_);
v___x_358_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_357_, v___f_356_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed(lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_p_387_, lean_object* v_f_388_, lean_object* v_stopWhenVisited_389_, lean_object* v_toBind_390_, lean_object* v_e_391_, lean_object* v_toApplicative_392_, lean_object* v_____r_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_stopWhenVisited_boxed_395_; lean_object* v_res_396_; 
v_stopWhenVisited_boxed_395_ = lean_unbox(v_stopWhenVisited_389_);
v_res_396_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(v_inst_385_, v_inst_386_, v_p_387_, v_f_388_, v_stopWhenVisited_boxed_395_, v_toBind_390_, v_e_391_, v_toApplicative_392_, v_____r_393_, v___y_394_);
lean_dec(v___y_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_p_399_, lean_object* v_f_400_, uint8_t v_stopWhenVisited_401_, lean_object* v_e_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_toApplicative_404_; lean_object* v_toBind_405_; lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_toApplicative_404_ = lean_ctor_get(v_inst_398_, 0);
v_toBind_405_ = lean_ctor_get(v_inst_398_, 1);
lean_inc_n(v_toBind_405_, 4);
v___x_406_ = lean_box(v_stopWhenVisited_401_);
lean_inc_ref_n(v_toApplicative_404_, 3);
lean_inc_ref_n(v_e_402_, 3);
lean_inc(v_f_400_);
lean_inc_ref(v_p_399_);
lean_inc_ref_n(v_inst_398_, 2);
lean_inc_n(v_inst_397_, 2);
v___f_407_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_407_, 0, v_inst_397_);
lean_closure_set(v___f_407_, 1, v_inst_398_);
lean_closure_set(v___f_407_, 2, v_p_399_);
lean_closure_set(v___f_407_, 3, v_f_400_);
lean_closure_set(v___f_407_, 4, v___x_406_);
lean_closure_set(v___f_407_, 5, v_toBind_405_);
lean_closure_set(v___f_407_, 6, v_e_402_);
lean_closure_set(v___f_407_, 7, v_toApplicative_404_);
v___x_408_ = lean_box(v_stopWhenVisited_401_);
lean_inc_n(v_a_403_, 3);
lean_inc_ref_n(v___f_407_, 2);
v___f_409_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed), 5, 4);
lean_closure_set(v___f_409_, 0, v___x_408_);
lean_closure_set(v___f_409_, 1, v___f_407_);
lean_closure_set(v___f_409_, 2, v_a_403_);
lean_closure_set(v___f_409_, 3, v_toApplicative_404_);
v___f_410_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_410_, 0, v_f_400_);
lean_closure_set(v___f_410_, 1, v_e_402_);
lean_closure_set(v___f_410_, 2, v_toBind_405_);
lean_closure_set(v___f_410_, 3, v___f_409_);
lean_closure_set(v___f_410_, 4, v___f_407_);
lean_closure_set(v___f_410_, 5, v_a_403_);
v___f_411_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed), 10, 9);
lean_closure_set(v___f_411_, 0, v_p_399_);
lean_closure_set(v___f_411_, 1, v_e_402_);
lean_closure_set(v___f_411_, 2, v___f_407_);
lean_closure_set(v___f_411_, 3, v_a_403_);
lean_closure_set(v___f_411_, 4, v_inst_397_);
lean_closure_set(v___f_411_, 5, v_inst_398_);
lean_closure_set(v___f_411_, 6, v_toBind_405_);
lean_closure_set(v___f_411_, 7, v___f_410_);
lean_closure_set(v___f_411_, 8, v_toApplicative_404_);
v___x_412_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_397_, v_inst_398_, v_e_402_, v_a_403_);
v___x_413_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v___x_412_, v___f_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_p_416_, lean_object* v_f_417_, uint8_t v_stopWhenVisited_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_414_, v_inst_415_, v_p_416_, v_f_417_, v_stopWhenVisited_418_, v_b_419_, v___y_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___boxed(lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_p_425_, lean_object* v_f_426_, lean_object* v_stopWhenVisited_427_, lean_object* v_e_428_, lean_object* v_a_429_){
_start:
{
uint8_t v_stopWhenVisited_boxed_430_; lean_object* v_res_431_; 
v_stopWhenVisited_boxed_430_ = lean_unbox(v_stopWhenVisited_427_);
v_res_431_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_423_, v_inst_424_, v_p_425_, v_f_426_, v_stopWhenVisited_boxed_430_, v_e_428_, v_a_429_);
lean_dec(v_a_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(lean_object* v_00_u03c9_432_, lean_object* v_m_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_p_437_, lean_object* v_f_438_, uint8_t v_stopWhenVisited_439_, lean_object* v_e_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_435_, v_inst_436_, v_p_437_, v_f_438_, v_stopWhenVisited_439_, v_e_440_, v_a_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___boxed(lean_object* v_00_u03c9_443_, lean_object* v_m_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_p_448_, lean_object* v_f_449_, lean_object* v_stopWhenVisited_450_, lean_object* v_e_451_, lean_object* v_a_452_){
_start:
{
uint8_t v_stopWhenVisited_boxed_453_; lean_object* v_res_454_; 
v_stopWhenVisited_boxed_453_ = lean_unbox(v_stopWhenVisited_450_);
v_res_454_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(v_00_u03c9_443_, v_m_444_, v_inst_445_, v_inst_446_, v_inst_447_, v_p_448_, v_f_449_, v_stopWhenVisited_boxed_453_, v_e_451_, v_a_452_);
lean_dec(v_a_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__0(lean_object* v_a_455_, lean_object* v_toPure_456_, lean_object* v_s_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_a_455_);
lean_ctor_set(v___x_458_, 1, v_s_457_);
v___x_459_ = lean_apply_2(v_toPure_456_, lean_box(0), v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__1(lean_object* v_toPure_460_, lean_object* v_ref_461_, lean_object* v_inst_462_, lean_object* v_toBind_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___f_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___f_465_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_465_, 0, v_a_464_);
lean_closure_set(v___f_465_, 1, v_toPure_460_);
v___x_466_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_466_, 0, lean_box(0));
lean_closure_set(v___x_466_, 1, lean_box(0));
lean_closure_set(v___x_466_, 2, v_ref_461_);
v___x_467_ = lean_apply_2(v_inst_462_, lean_box(0), v___x_466_);
v___x_468_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v___x_467_, v___f_465_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2(lean_object* v_toPure_469_, lean_object* v_inst_470_, lean_object* v_toBind_471_, lean_object* v_inst_472_, lean_object* v_p_473_, lean_object* v_f_474_, uint8_t v_stopWhenVisited_475_, lean_object* v_e_476_, lean_object* v_ref_477_){
_start:
{
lean_object* v___f_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_inc(v_toBind_471_);
lean_inc(v_inst_470_);
lean_inc(v_ref_477_);
v___f_478_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_478_, 0, v_toPure_469_);
lean_closure_set(v___f_478_, 1, v_ref_477_);
lean_closure_set(v___f_478_, 2, v_inst_470_);
lean_closure_set(v___f_478_, 3, v_toBind_471_);
v___x_479_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_470_, v_inst_472_, v_p_473_, v_f_474_, v_stopWhenVisited_475_, v_e_476_, v_ref_477_);
lean_dec(v_ref_477_);
v___x_480_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v___x_479_, v___f_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed(lean_object* v_toPure_481_, lean_object* v_inst_482_, lean_object* v_toBind_483_, lean_object* v_inst_484_, lean_object* v_p_485_, lean_object* v_f_486_, lean_object* v_stopWhenVisited_487_, lean_object* v_e_488_, lean_object* v_ref_489_){
_start:
{
uint8_t v_stopWhenVisited_boxed_490_; lean_object* v_res_491_; 
v_stopWhenVisited_boxed_490_ = lean_unbox(v_stopWhenVisited_487_);
v_res_491_ = l_Lean_ForEachExprWhere_visit___redArg___lam__2(v_toPure_481_, v_inst_482_, v_toBind_483_, v_inst_484_, v_p_485_, v_f_486_, v_stopWhenVisited_boxed_490_, v_e_488_, v_ref_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__3(lean_object* v_toPure_492_, lean_object* v_____x_493_){
_start:
{
lean_object* v_fst_494_; lean_object* v___x_495_; 
v_fst_494_ = lean_ctor_get(v_____x_493_, 0);
lean_inc(v_fst_494_);
lean_dec_ref(v_____x_493_);
v___x_495_ = lean_apply_2(v_toPure_492_, lean_box(0), v_fst_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l_Lean_ForEachExprWhere_initCache;
v___x_497_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_497_, 0, lean_box(0));
lean_closure_set(v___x_497_, 1, lean_box(0));
lean_closure_set(v___x_497_, 2, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg(lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_p_500_, lean_object* v_f_501_, lean_object* v_e_502_, uint8_t v_stopWhenVisited_503_){
_start:
{
lean_object* v_toApplicative_504_; lean_object* v_toBind_505_; lean_object* v_toPure_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___f_510_; lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_toApplicative_504_ = lean_ctor_get(v_inst_499_, 0);
v_toBind_505_ = lean_ctor_get(v_inst_499_, 1);
lean_inc_n(v_toBind_505_, 3);
v_toPure_506_ = lean_ctor_get(v_toApplicative_504_, 1);
lean_inc_n(v_toPure_506_, 2);
v___x_507_ = lean_obj_once(&l_Lean_ForEachExprWhere_visit___redArg___closed__0, &l_Lean_ForEachExprWhere_visit___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0);
lean_inc(v_inst_498_);
v___x_508_ = lean_apply_2(v_inst_498_, lean_box(0), v___x_507_);
v___x_509_ = lean_box(v_stopWhenVisited_503_);
v___f_510_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_510_, 0, v_toPure_506_);
lean_closure_set(v___f_510_, 1, v_inst_498_);
lean_closure_set(v___f_510_, 2, v_toBind_505_);
lean_closure_set(v___f_510_, 3, v_inst_499_);
lean_closure_set(v___f_510_, 4, v_p_500_);
lean_closure_set(v___f_510_, 5, v_f_501_);
lean_closure_set(v___f_510_, 6, v___x_509_);
lean_closure_set(v___f_510_, 7, v_e_502_);
v___f_511_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__3), 2, 1);
lean_closure_set(v___f_511_, 0, v_toPure_506_);
v___x_512_ = lean_apply_4(v_toBind_505_, lean_box(0), lean_box(0), v___x_508_, v___f_510_);
v___x_513_ = lean_apply_4(v_toBind_505_, lean_box(0), lean_box(0), v___x_512_, v___f_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___boxed(lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_p_516_, lean_object* v_f_517_, lean_object* v_e_518_, lean_object* v_stopWhenVisited_519_){
_start:
{
uint8_t v_stopWhenVisited_boxed_520_; lean_object* v_res_521_; 
v_stopWhenVisited_boxed_520_ = lean_unbox(v_stopWhenVisited_519_);
v_res_521_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_514_, v_inst_515_, v_p_516_, v_f_517_, v_e_518_, v_stopWhenVisited_boxed_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit(lean_object* v_00_u03c9_522_, lean_object* v_m_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_p_527_, lean_object* v_f_528_, lean_object* v_e_529_, uint8_t v_stopWhenVisited_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_525_, v_inst_526_, v_p_527_, v_f_528_, v_e_529_, v_stopWhenVisited_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___boxed(lean_object* v_00_u03c9_532_, lean_object* v_m_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_p_537_, lean_object* v_f_538_, lean_object* v_e_539_, lean_object* v_stopWhenVisited_540_){
_start:
{
uint8_t v_stopWhenVisited_boxed_541_; lean_object* v_res_542_; 
v_stopWhenVisited_boxed_541_ = lean_unbox(v_stopWhenVisited_540_);
v_res_542_ = l_Lean_ForEachExprWhere_visit(v_00_u03c9_532_, v_m_533_, v_inst_534_, v_inst_535_, v_inst_536_, v_p_537_, v_f_538_, v_e_539_, v_stopWhenVisited_boxed_541_);
return v_res_542_;
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
