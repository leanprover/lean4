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
lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0(size_t v___x_18_, lean_object* v_e_19_, lean_object* v_s_20_){
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
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v___x_18_ = stack[0].m_num;
lean_object* v_e_19_ = stack[1].m_obj;
lean_object* v_s_20_ = stack[2].m_obj;
lean_object* v_res_33_;
v_res_33_ = l_Lean_ForEachExprWhere_visited___redArg___lam__0(v___x_18_, v_e_19_, v_s_20_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__0___boxed(lean_object* v___x_34_, lean_object* v_e_35_, lean_object* v_s_36_){
_start:
{
size_t v___x_269__boxed_37_; lean_object* v_res_38_; 
v___x_269__boxed_37_ = lean_unbox_usize(v___x_34_);
lean_dec(v___x_34_);
v_res_38_ = l_Lean_ForEachExprWhere_visited___redArg___lam__0(v___x_269__boxed_37_, v_e_35_, v_s_36_);
return v_res_38_;
}
}
lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1(lean_object* v_toApplicative_39_, uint8_t v___x_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_toPure_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_toPure_42_ = lean_ctor_get(v_toApplicative_39_, 1);
lean_inc(v_toPure_42_);
lean_dec_ref(v_toApplicative_39_);
v___x_43_ = lean_box(v___x_40_);
v___x_44_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_39_ = stack[0].m_obj;
uint8_t v___x_40_ = stack[1].m_num;
lean_object* v_a_41_ = stack[2].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_ForEachExprWhere_visited___redArg___lam__1(v_toApplicative_39_, v___x_40_, v_a_41_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___redArg___lam__1___boxed(lean_object* v_toApplicative_46_, lean_object* v___x_47_, lean_object* v_a_48_){
_start:
{
uint8_t v___x_304__boxed_49_; lean_object* v_res_50_; 
v___x_304__boxed_49_ = lean_unbox(v___x_47_);
v_res_50_ = l_Lean_ForEachExprWhere_visited___redArg___lam__1(v_toApplicative_46_, v___x_304__boxed_49_, v_a_48_);
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
lean_object* v_visited_116_; lean_object* v_checked_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_127_; 
v_visited_116_ = lean_ctor_get(v_s_115_, 0);
v_checked_117_ = lean_ctor_get(v_s_115_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_s_115_);
if (v_isSharedCheck_127_ == 0)
{
v___x_119_ = v_s_115_;
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_checked_117_);
lean_inc(v_visited_116_);
lean_dec(v_s_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_121_ = lean_box(0);
v___x_122_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_112_, v___x_113_, v_checked_117_, v_e_114_, v___x_121_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_122_);
v___x_124_ = v___x_119_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_visited_116_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_126_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; 
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_121_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
return v___x_125_;
}
}
}
}
lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1(lean_object* v_toApplicative_128_, uint8_t v___x_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_toPure_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_toPure_131_ = lean_ctor_get(v_toApplicative_128_, 1);
lean_inc(v_toPure_131_);
lean_dec_ref(v_toApplicative_128_);
v___x_132_ = lean_box(v___x_129_);
v___x_133_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_checked___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_128_ = stack[0].m_obj;
uint8_t v___x_129_ = stack[1].m_num;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Lean_ForEachExprWhere_checked___redArg___lam__1(v_toApplicative_128_, v___x_129_, v_a_130_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed(lean_object* v_toApplicative_135_, lean_object* v___x_136_, lean_object* v_a_137_){
_start:
{
uint8_t v___x_307__boxed_138_; lean_object* v_res_139_; 
v___x_307__boxed_138_ = lean_unbox(v___x_136_);
v_res_139_ = l_Lean_ForEachExprWhere_checked___redArg___lam__1(v_toApplicative_135_, v___x_307__boxed_138_, v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2(lean_object* v___x_140_, lean_object* v___x_141_, lean_object* v_e_142_, lean_object* v_toApplicative_143_, lean_object* v_a_144_, lean_object* v___f_145_, lean_object* v_inst_146_, lean_object* v_toBind_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_checked_149_; uint8_t v___x_150_; 
v_checked_149_ = lean_ctor_get(v_a_148_, 1);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_140_, v___x_141_, v_checked_149_, v_e_142_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = lean_box(v___x_150_);
v___f_152_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_152_, 0, v_toApplicative_143_);
lean_closure_set(v___f_152_, 1, v___x_151_);
lean_inc(v_a_144_);
v___x_153_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, lean_box(0));
lean_closure_set(v___x_153_, 3, v_a_144_);
lean_closure_set(v___x_153_, 4, v___f_145_);
v___x_154_ = lean_apply_2(v_inst_146_, lean_box(0), v___x_153_);
v___x_155_ = lean_apply_4(v_toBind_147_, lean_box(0), lean_box(0), v___x_154_, v___f_152_);
return v___x_155_;
}
else
{
lean_object* v_toPure_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_toBind_147_);
lean_dec(v_inst_146_);
lean_dec_ref(v___f_145_);
v_toPure_156_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_156_);
lean_dec_ref(v_toApplicative_143_);
v___x_157_ = lean_box(v___x_150_);
v___x_158_ = lean_apply_2(v_toPure_156_, lean_box(0), v___x_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed(lean_object* v___x_159_, lean_object* v___x_160_, lean_object* v_e_161_, lean_object* v_toApplicative_162_, lean_object* v_a_163_, lean_object* v___f_164_, lean_object* v_inst_165_, lean_object* v_toBind_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_ForEachExprWhere_checked___redArg___lam__2(v___x_159_, v___x_160_, v_e_161_, v_toApplicative_162_, v_a_163_, v___f_164_, v_inst_165_, v_toBind_166_, v_a_167_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_e_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_toApplicative_175_; lean_object* v_toBind_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_toApplicative_175_ = lean_ctor_get(v_inst_172_, 0);
lean_inc_ref(v_toApplicative_175_);
v_toBind_176_ = lean_ctor_get(v_inst_172_, 1);
lean_inc_n(v_toBind_176_, 2);
lean_dec_ref(v_inst_172_);
v___x_177_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__0));
v___x_178_ = ((lean_object*)(l_Lean_ForEachExprWhere_checked___redArg___closed__1));
lean_inc_ref(v_e_173_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__0), 4, 3);
lean_closure_set(v___f_179_, 0, v___x_177_);
lean_closure_set(v___f_179_, 1, v___x_178_);
lean_closure_set(v___f_179_, 2, v_e_173_);
lean_inc(v_inst_171_);
lean_inc_n(v_a_174_, 2);
v___f_180_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_checked___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_180_, 0, v___x_177_);
lean_closure_set(v___f_180_, 1, v___x_178_);
lean_closure_set(v___f_180_, 2, v_e_173_);
lean_closure_set(v___f_180_, 3, v_toApplicative_175_);
lean_closure_set(v___f_180_, 4, v_a_174_);
lean_closure_set(v___f_180_, 5, v___f_179_);
lean_closure_set(v___f_180_, 6, v_inst_171_);
lean_closure_set(v___f_180_, 7, v_toBind_176_);
v___x_181_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_181_, 0, lean_box(0));
lean_closure_set(v___x_181_, 1, lean_box(0));
lean_closure_set(v___x_181_, 2, v_a_174_);
v___x_182_ = lean_apply_2(v_inst_171_, lean_box(0), v___x_181_);
v___x_183_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v___x_182_, v___f_180_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___redArg___boxed(lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_e_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_184_, v_inst_185_, v_e_186_, v_a_187_);
lean_dec(v_a_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked(lean_object* v_00_u03c9_189_, lean_object* v_m_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_e_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_192_, v_inst_193_, v_e_194_, v_a_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___boxed(lean_object* v_00_u03c9_197_, lean_object* v_m_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_e_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_ForEachExprWhere_checked(v_00_u03c9_197_, v_m_198_, v_inst_199_, v_inst_200_, v_inst_201_, v_e_202_, v_a_203_);
lean_dec(v_a_203_);
return v_res_204_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(lean_object* v_p_205_, lean_object* v_e_206_, lean_object* v___f_207_, lean_object* v_a_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_toBind_211_, lean_object* v___f_212_, lean_object* v_toApplicative_213_, uint8_t v_a_214_){
_start:
{
if (v_a_214_ == 0)
{
lean_object* v___x_215_; uint8_t v___x_216_; 
lean_dec_ref(v_toApplicative_213_);
lean_inc_ref(v_e_206_);
v___x_215_ = lean_apply_1(v_p_205_, v_e_206_);
v___x_216_ = lean_unbox(v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v___f_212_);
lean_dec(v_toBind_211_);
lean_dec_ref(v_inst_210_);
lean_dec(v_inst_209_);
lean_dec_ref(v_e_206_);
v___x_217_ = lean_box(0);
lean_inc(v_a_208_);
v___x_218_ = lean_apply_2(v___f_207_, v___x_217_, v_a_208_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___f_207_);
v___x_219_ = l_Lean_ForEachExprWhere_checked___redArg(v_inst_209_, v_inst_210_, v_e_206_, v_a_208_);
v___x_220_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_219_, v___f_212_);
return v___x_220_;
}
}
else
{
lean_object* v_toPure_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v___f_212_);
lean_dec(v_toBind_211_);
lean_dec_ref(v_inst_210_);
lean_dec(v_inst_209_);
lean_dec(v___f_207_);
lean_dec_ref(v_e_206_);
lean_dec_ref(v_p_205_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_213_, 1);
lean_inc(v_toPure_221_);
lean_dec_ref(v_toApplicative_213_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_apply_2(v_toPure_221_, lean_box(0), v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_205_ = stack[0].m_obj;
lean_object* v_e_206_ = stack[1].m_obj;
lean_object* v___f_207_ = stack[2].m_obj;
lean_object* v_a_208_ = stack[3].m_obj;
lean_object* v_inst_209_ = stack[4].m_obj;
lean_object* v_inst_210_ = stack[5].m_obj;
lean_object* v_toBind_211_ = stack[6].m_obj;
lean_object* v___f_212_ = stack[7].m_obj;
lean_object* v_toApplicative_213_ = stack[8].m_obj;
uint8_t v_a_214_ = stack[9].m_num;
lean_object* v_res_224_;
v_res_224_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(v_p_205_, v_e_206_, v___f_207_, v_a_208_, v_inst_209_, v_inst_210_, v_toBind_211_, v___f_212_, v_toApplicative_213_, v_a_214_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed(lean_object* v_p_225_, lean_object* v_e_226_, lean_object* v___f_227_, lean_object* v_a_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_toBind_231_, lean_object* v___f_232_, lean_object* v_toApplicative_233_, lean_object* v_a_234_){
_start:
{
uint8_t v_a_boxed_235_; lean_object* v_res_236_; 
v_a_boxed_235_ = lean_unbox(v_a_234_);
v_res_236_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7(v_p_225_, v_e_226_, v___f_227_, v_a_228_, v_inst_229_, v_inst_230_, v_toBind_231_, v___f_232_, v_toApplicative_233_, v_a_boxed_235_);
lean_dec(v_a_228_);
return v_res_236_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(uint8_t v_stopWhenVisited_237_, lean_object* v___f_238_, lean_object* v_a_239_, lean_object* v_toApplicative_240_, lean_object* v_a_241_){
_start:
{
if (v_stopWhenVisited_237_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v_toApplicative_240_);
v___x_242_ = lean_box(0);
lean_inc(v_a_239_);
v___x_243_ = lean_apply_2(v___f_238_, v___x_242_, v_a_239_);
return v___x_243_;
}
else
{
lean_object* v_toPure_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v___f_238_);
v_toPure_244_ = lean_ctor_get(v_toApplicative_240_, 1);
lean_inc(v_toPure_244_);
lean_dec_ref(v_toApplicative_240_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_apply_2(v_toPure_244_, lean_box(0), v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_stopWhenVisited_237_ = stack[0].m_num;
lean_object* v___f_238_ = stack[1].m_obj;
lean_object* v_a_239_ = stack[2].m_obj;
lean_object* v_toApplicative_240_ = stack[3].m_obj;
lean_object* v_a_241_ = stack[4].m_obj;
lean_object* v_res_247_;
v_res_247_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5(v_stopWhenVisited_237_, v___f_238_, v_a_239_, v_toApplicative_240_, v_a_241_);
stack->m_obj
 = v_res_247_;
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
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(lean_object* v_f_255_, lean_object* v_e_256_, lean_object* v_toBind_257_, lean_object* v___f_258_, lean_object* v___f_259_, lean_object* v_a_260_, uint8_t v_a_261_){
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
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_255_ = stack[0].m_obj;
lean_object* v_e_256_ = stack[1].m_obj;
lean_object* v_toBind_257_ = stack[2].m_obj;
lean_object* v___f_258_ = stack[3].m_obj;
lean_object* v___f_259_ = stack[4].m_obj;
lean_object* v_a_260_ = stack[5].m_obj;
uint8_t v_a_261_ = stack[6].m_num;
lean_object* v_res_266_;
v_res_266_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(v_f_255_, v_e_256_, v_toBind_257_, v___f_258_, v___f_259_, v_a_260_, v_a_261_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed(lean_object* v_f_267_, lean_object* v_e_268_, lean_object* v_toBind_269_, lean_object* v___f_270_, lean_object* v___f_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
uint8_t v_a_boxed_274_; lean_object* v_res_275_; 
v_a_boxed_274_ = lean_unbox(v_a_273_);
v_res_275_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6(v_f_267_, v_e_268_, v_toBind_269_, v___f_270_, v___f_271_, v_a_272_, v_a_boxed_274_);
lean_dec(v_a_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed(lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_p_278_, lean_object* v_f_279_, lean_object* v_stopWhenVisited_280_, lean_object* v_b_281_, lean_object* v___y_282_, lean_object* v_a_283_){
_start:
{
uint8_t v_stopWhenVisited_boxed_284_; lean_object* v_res_285_; 
v_stopWhenVisited_boxed_284_ = lean_unbox(v_stopWhenVisited_280_);
v_res_285_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(v_inst_276_, v_inst_277_, v_p_278_, v_f_279_, v_stopWhenVisited_boxed_284_, v_b_281_, v___y_282_, v_a_283_);
lean_dec(v___y_282_);
return v_res_285_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_p_288_, lean_object* v_f_289_, uint8_t v_stopWhenVisited_290_, lean_object* v_body_291_, lean_object* v___y_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_286_, v_inst_287_, v_p_288_, v_f_289_, v_stopWhenVisited_290_, v_body_291_, v___y_292_);
return v___x_294_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_286_ = stack[0].m_obj;
lean_object* v_inst_287_ = stack[1].m_obj;
lean_object* v_p_288_ = stack[2].m_obj;
lean_object* v_f_289_ = stack[3].m_obj;
uint8_t v_stopWhenVisited_290_ = stack[4].m_num;
lean_object* v_body_291_ = stack[5].m_obj;
lean_object* v___y_292_ = stack[6].m_obj;
lean_object* v_a_293_ = stack[7].m_obj;
lean_object* v_res_295_;
v_res_295_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(v_inst_286_, v_inst_287_, v_p_288_, v_f_289_, v_stopWhenVisited_290_, v_body_291_, v___y_292_, v_a_293_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed(lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_p_298_, lean_object* v_f_299_, lean_object* v_stopWhenVisited_300_, lean_object* v_body_301_, lean_object* v___y_302_, lean_object* v_a_303_){
_start:
{
uint8_t v_stopWhenVisited_boxed_304_; lean_object* v_res_305_; 
v_stopWhenVisited_boxed_304_ = lean_unbox(v_stopWhenVisited_300_);
v_res_305_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1(v_inst_296_, v_inst_297_, v_p_298_, v_f_299_, v_stopWhenVisited_boxed_304_, v_body_301_, v___y_302_, v_a_303_);
lean_dec(v___y_302_);
return v_res_305_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_p_308_, lean_object* v_f_309_, uint8_t v_stopWhenVisited_310_, lean_object* v_value_311_, lean_object* v___y_312_, lean_object* v_toBind_313_, lean_object* v___f_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_306_, v_inst_307_, v_p_308_, v_f_309_, v_stopWhenVisited_310_, v_value_311_, v___y_312_);
v___x_317_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_316_, v___f_314_);
return v___x_317_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_306_ = stack[0].m_obj;
lean_object* v_inst_307_ = stack[1].m_obj;
lean_object* v_p_308_ = stack[2].m_obj;
lean_object* v_f_309_ = stack[3].m_obj;
uint8_t v_stopWhenVisited_310_ = stack[4].m_num;
lean_object* v_value_311_ = stack[5].m_obj;
lean_object* v___y_312_ = stack[6].m_obj;
lean_object* v_toBind_313_ = stack[7].m_obj;
lean_object* v___f_314_ = stack[8].m_obj;
lean_object* v_a_315_ = stack[9].m_obj;
lean_object* v_res_318_;
v_res_318_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(v_inst_306_, v_inst_307_, v_p_308_, v_f_309_, v_stopWhenVisited_310_, v_value_311_, v___y_312_, v_toBind_313_, v___f_314_, v_a_315_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_p_321_, lean_object* v_f_322_, lean_object* v_stopWhenVisited_323_, lean_object* v_value_324_, lean_object* v___y_325_, lean_object* v_toBind_326_, lean_object* v___f_327_, lean_object* v_a_328_){
_start:
{
uint8_t v_stopWhenVisited_boxed_329_; lean_object* v_res_330_; 
v_stopWhenVisited_boxed_329_ = lean_unbox(v_stopWhenVisited_323_);
v_res_330_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2(v_inst_319_, v_inst_320_, v_p_321_, v_f_322_, v_stopWhenVisited_boxed_329_, v_value_324_, v___y_325_, v_toBind_326_, v___f_327_, v_a_328_);
lean_dec(v___y_325_);
return v_res_330_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_p_333_, lean_object* v_f_334_, uint8_t v_stopWhenVisited_335_, lean_object* v_arg_336_, lean_object* v___y_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_331_, v_inst_332_, v_p_333_, v_f_334_, v_stopWhenVisited_335_, v_arg_336_, v___y_337_);
return v___x_339_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_331_ = stack[0].m_obj;
lean_object* v_inst_332_ = stack[1].m_obj;
lean_object* v_p_333_ = stack[2].m_obj;
lean_object* v_f_334_ = stack[3].m_obj;
uint8_t v_stopWhenVisited_335_ = stack[4].m_num;
lean_object* v_arg_336_ = stack[5].m_obj;
lean_object* v___y_337_ = stack[6].m_obj;
lean_object* v_a_338_ = stack[7].m_obj;
lean_object* v_res_340_;
v_res_340_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(v_inst_331_, v_inst_332_, v_p_333_, v_f_334_, v_stopWhenVisited_335_, v_arg_336_, v___y_337_, v_a_338_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed(lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_p_343_, lean_object* v_f_344_, lean_object* v_stopWhenVisited_345_, lean_object* v_arg_346_, lean_object* v___y_347_, lean_object* v_a_348_){
_start:
{
uint8_t v_stopWhenVisited_boxed_349_; lean_object* v_res_350_; 
v_stopWhenVisited_boxed_349_ = lean_unbox(v_stopWhenVisited_345_);
v_res_350_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3(v_inst_341_, v_inst_342_, v_p_343_, v_f_344_, v_stopWhenVisited_boxed_349_, v_arg_346_, v___y_347_, v_a_348_);
lean_dec(v___y_347_);
return v_res_350_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_p_353_, lean_object* v_f_354_, uint8_t v_stopWhenVisited_355_, lean_object* v_toBind_356_, lean_object* v_e_357_, lean_object* v_toApplicative_358_, lean_object* v_____r_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_d_362_; lean_object* v_b_363_; 
switch(lean_obj_tag(v_e_357_))
{
case 7:
{
lean_object* v_binderType_368_; lean_object* v_body_369_; 
lean_dec_ref(v_toApplicative_358_);
v_binderType_368_ = lean_ctor_get(v_e_357_, 1);
lean_inc_ref(v_binderType_368_);
v_body_369_ = lean_ctor_get(v_e_357_, 2);
lean_inc_ref(v_body_369_);
lean_dec_ref_known(v_e_357_, 3);
v_d_362_ = v_binderType_368_;
v_b_363_ = v_body_369_;
goto v___jp_361_;
}
case 6:
{
lean_object* v_binderType_370_; lean_object* v_body_371_; 
lean_dec_ref(v_toApplicative_358_);
v_binderType_370_ = lean_ctor_get(v_e_357_, 1);
lean_inc_ref(v_binderType_370_);
v_body_371_ = lean_ctor_get(v_e_357_, 2);
lean_inc_ref(v_body_371_);
lean_dec_ref_known(v_e_357_, 3);
v_d_362_ = v_binderType_370_;
v_b_363_ = v_body_371_;
goto v___jp_361_;
}
case 8:
{
lean_object* v_type_372_; lean_object* v_value_373_; lean_object* v_body_374_; lean_object* v___x_375_; lean_object* v___f_376_; lean_object* v___x_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec_ref(v_toApplicative_358_);
v_type_372_ = lean_ctor_get(v_e_357_, 1);
lean_inc_ref(v_type_372_);
v_value_373_ = lean_ctor_get(v_e_357_, 2);
lean_inc_ref(v_value_373_);
v_body_374_ = lean_ctor_get(v_e_357_, 3);
lean_inc_ref(v_body_374_);
lean_dec_ref_known(v_e_357_, 4);
v___x_375_ = lean_box(v_stopWhenVisited_355_);
lean_inc_n(v___y_360_, 2);
lean_inc_n(v_f_354_, 2);
lean_inc_ref_n(v_p_353_, 2);
lean_inc_ref_n(v_inst_352_, 2);
lean_inc_n(v_inst_351_, 2);
v___f_376_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_376_, 0, v_inst_351_);
lean_closure_set(v___f_376_, 1, v_inst_352_);
lean_closure_set(v___f_376_, 2, v_p_353_);
lean_closure_set(v___f_376_, 3, v_f_354_);
lean_closure_set(v___f_376_, 4, v___x_375_);
lean_closure_set(v___f_376_, 5, v_body_374_);
lean_closure_set(v___f_376_, 6, v___y_360_);
v___x_377_ = lean_box(v_stopWhenVisited_355_);
lean_inc(v_toBind_356_);
v___f_378_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_378_, 0, v_inst_351_);
lean_closure_set(v___f_378_, 1, v_inst_352_);
lean_closure_set(v___f_378_, 2, v_p_353_);
lean_closure_set(v___f_378_, 3, v_f_354_);
lean_closure_set(v___f_378_, 4, v___x_377_);
lean_closure_set(v___f_378_, 5, v_value_373_);
lean_closure_set(v___f_378_, 6, v___y_360_);
lean_closure_set(v___f_378_, 7, v_toBind_356_);
lean_closure_set(v___f_378_, 8, v___f_376_);
v___x_379_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_351_, v_inst_352_, v_p_353_, v_f_354_, v_stopWhenVisited_355_, v_type_372_, v___y_360_);
v___x_380_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v___x_379_, v___f_378_);
return v___x_380_;
}
case 5:
{
lean_object* v_fn_381_; lean_object* v_arg_382_; lean_object* v___x_383_; lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec_ref(v_toApplicative_358_);
v_fn_381_ = lean_ctor_get(v_e_357_, 0);
lean_inc_ref(v_fn_381_);
v_arg_382_ = lean_ctor_get(v_e_357_, 1);
lean_inc_ref(v_arg_382_);
lean_dec_ref_known(v_e_357_, 2);
v___x_383_ = lean_box(v_stopWhenVisited_355_);
lean_inc(v___y_360_);
lean_inc(v_f_354_);
lean_inc_ref(v_p_353_);
lean_inc_ref(v_inst_352_);
lean_inc(v_inst_351_);
v___f_384_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_384_, 0, v_inst_351_);
lean_closure_set(v___f_384_, 1, v_inst_352_);
lean_closure_set(v___f_384_, 2, v_p_353_);
lean_closure_set(v___f_384_, 3, v_f_354_);
lean_closure_set(v___f_384_, 4, v___x_383_);
lean_closure_set(v___f_384_, 5, v_arg_382_);
lean_closure_set(v___f_384_, 6, v___y_360_);
v___x_385_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_351_, v_inst_352_, v_p_353_, v_f_354_, v_stopWhenVisited_355_, v_fn_381_, v___y_360_);
v___x_386_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v___x_385_, v___f_384_);
return v___x_386_;
}
case 10:
{
lean_object* v_expr_387_; lean_object* v___x_388_; 
lean_dec_ref(v_toApplicative_358_);
lean_dec(v_toBind_356_);
v_expr_387_ = lean_ctor_get(v_e_357_, 1);
lean_inc_ref(v_expr_387_);
lean_dec_ref_known(v_e_357_, 2);
v___x_388_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_351_, v_inst_352_, v_p_353_, v_f_354_, v_stopWhenVisited_355_, v_expr_387_, v___y_360_);
return v___x_388_;
}
case 11:
{
lean_object* v_struct_389_; lean_object* v___x_390_; 
lean_dec_ref(v_toApplicative_358_);
lean_dec(v_toBind_356_);
v_struct_389_ = lean_ctor_get(v_e_357_, 2);
lean_inc_ref(v_struct_389_);
lean_dec_ref_known(v_e_357_, 3);
v___x_390_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_351_, v_inst_352_, v_p_353_, v_f_354_, v_stopWhenVisited_355_, v_struct_389_, v___y_360_);
return v___x_390_;
}
default: 
{
lean_object* v_toPure_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref(v_e_357_);
lean_dec(v_toBind_356_);
lean_dec(v_f_354_);
lean_dec_ref(v_p_353_);
lean_dec_ref(v_inst_352_);
lean_dec(v_inst_351_);
v_toPure_391_ = lean_ctor_get(v_toApplicative_358_, 1);
lean_inc(v_toPure_391_);
lean_dec_ref(v_toApplicative_358_);
v___x_392_ = lean_box(0);
v___x_393_ = lean_apply_2(v_toPure_391_, lean_box(0), v___x_392_);
return v___x_393_;
}
}
v___jp_361_:
{
lean_object* v___x_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_364_ = lean_box(v_stopWhenVisited_355_);
lean_inc(v___y_360_);
lean_inc(v_f_354_);
lean_inc_ref(v_p_353_);
lean_inc_ref(v_inst_352_);
lean_inc(v_inst_351_);
v___f_365_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_365_, 0, v_inst_351_);
lean_closure_set(v___f_365_, 1, v_inst_352_);
lean_closure_set(v___f_365_, 2, v_p_353_);
lean_closure_set(v___f_365_, 3, v_f_354_);
lean_closure_set(v___f_365_, 4, v___x_364_);
lean_closure_set(v___f_365_, 5, v_b_363_);
lean_closure_set(v___f_365_, 6, v___y_360_);
v___x_366_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_351_, v_inst_352_, v_p_353_, v_f_354_, v_stopWhenVisited_355_, v_d_362_, v___y_360_);
v___x_367_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v___x_366_, v___f_365_);
return v___x_367_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_351_ = stack[0].m_obj;
lean_object* v_inst_352_ = stack[1].m_obj;
lean_object* v_p_353_ = stack[2].m_obj;
lean_object* v_f_354_ = stack[3].m_obj;
uint8_t v_stopWhenVisited_355_ = stack[4].m_num;
lean_object* v_toBind_356_ = stack[5].m_obj;
lean_object* v_e_357_ = stack[6].m_obj;
lean_object* v_toApplicative_358_ = stack[7].m_obj;
lean_object* v_____r_359_ = stack[8].m_obj;
lean_object* v___y_360_ = stack[9].m_obj;
lean_object* v_res_394_;
v_res_394_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(v_inst_351_, v_inst_352_, v_p_353_, v_f_354_, v_stopWhenVisited_355_, v_toBind_356_, v_e_357_, v_toApplicative_358_, v_____r_359_, v___y_360_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed(lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_p_397_, lean_object* v_f_398_, lean_object* v_stopWhenVisited_399_, lean_object* v_toBind_400_, lean_object* v_e_401_, lean_object* v_toApplicative_402_, lean_object* v_____r_403_, lean_object* v___y_404_){
_start:
{
uint8_t v_stopWhenVisited_boxed_405_; lean_object* v_res_406_; 
v_stopWhenVisited_boxed_405_ = lean_unbox(v_stopWhenVisited_399_);
v_res_406_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4(v_inst_395_, v_inst_396_, v_p_397_, v_f_398_, v_stopWhenVisited_boxed_405_, v_toBind_400_, v_e_401_, v_toApplicative_402_, v_____r_403_, v___y_404_);
lean_dec(v___y_404_);
return v_res_406_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_p_409_, lean_object* v_f_410_, uint8_t v_stopWhenVisited_411_, lean_object* v_e_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_toApplicative_414_; lean_object* v_toBind_415_; lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_toApplicative_414_ = lean_ctor_get(v_inst_408_, 0);
v_toBind_415_ = lean_ctor_get(v_inst_408_, 1);
lean_inc_n(v_toBind_415_, 4);
v___x_416_ = lean_box(v_stopWhenVisited_411_);
lean_inc_ref_n(v_toApplicative_414_, 3);
lean_inc_ref_n(v_e_412_, 3);
lean_inc(v_f_410_);
lean_inc_ref(v_p_409_);
lean_inc_ref_n(v_inst_408_, 2);
lean_inc_n(v_inst_407_, 2);
v___f_417_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_417_, 0, v_inst_407_);
lean_closure_set(v___f_417_, 1, v_inst_408_);
lean_closure_set(v___f_417_, 2, v_p_409_);
lean_closure_set(v___f_417_, 3, v_f_410_);
lean_closure_set(v___f_417_, 4, v___x_416_);
lean_closure_set(v___f_417_, 5, v_toBind_415_);
lean_closure_set(v___f_417_, 6, v_e_412_);
lean_closure_set(v___f_417_, 7, v_toApplicative_414_);
v___x_418_ = lean_box(v_stopWhenVisited_411_);
lean_inc_n(v_a_413_, 3);
lean_inc_ref_n(v___f_417_, 2);
v___f_419_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__5___boxed), 5, 4);
lean_closure_set(v___f_419_, 0, v___x_418_);
lean_closure_set(v___f_419_, 1, v___f_417_);
lean_closure_set(v___f_419_, 2, v_a_413_);
lean_closure_set(v___f_419_, 3, v_toApplicative_414_);
v___f_420_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_420_, 0, v_f_410_);
lean_closure_set(v___f_420_, 1, v_e_412_);
lean_closure_set(v___f_420_, 2, v_toBind_415_);
lean_closure_set(v___f_420_, 3, v___f_419_);
lean_closure_set(v___f_420_, 4, v___f_417_);
lean_closure_set(v___f_420_, 5, v_a_413_);
v___f_421_ = lean_alloc_closure((void*)(l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__7___boxed), 10, 9);
lean_closure_set(v___f_421_, 0, v_p_409_);
lean_closure_set(v___f_421_, 1, v_e_412_);
lean_closure_set(v___f_421_, 2, v___f_417_);
lean_closure_set(v___f_421_, 3, v_a_413_);
lean_closure_set(v___f_421_, 4, v_inst_407_);
lean_closure_set(v___f_421_, 5, v_inst_408_);
lean_closure_set(v___f_421_, 6, v_toBind_415_);
lean_closure_set(v___f_421_, 7, v___f_420_);
lean_closure_set(v___f_421_, 8, v_toApplicative_414_);
v___x_422_ = l_Lean_ForEachExprWhere_visited___redArg(v_inst_407_, v_inst_408_, v_e_412_, v_a_413_);
v___x_423_ = lean_apply_4(v_toBind_415_, lean_box(0), lean_box(0), v___x_422_, v___f_421_);
return v___x_423_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_407_ = stack[0].m_obj;
lean_object* v_inst_408_ = stack[1].m_obj;
lean_object* v_p_409_ = stack[2].m_obj;
lean_object* v_f_410_ = stack[3].m_obj;
uint8_t v_stopWhenVisited_411_ = stack[4].m_num;
lean_object* v_e_412_ = stack[5].m_obj;
lean_object* v_a_413_ = stack[6].m_obj;
lean_object* v_res_424_;
v_res_424_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_407_, v_inst_408_, v_p_409_, v_f_410_, v_stopWhenVisited_411_, v_e_412_, v_a_413_);
stack->m_obj
 = v_res_424_;
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_p_427_, lean_object* v_f_428_, uint8_t v_stopWhenVisited_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_425_, v_inst_426_, v_p_427_, v_f_428_, v_stopWhenVisited_429_, v_b_430_, v___y_431_);
return v___x_433_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_425_ = stack[0].m_obj;
lean_object* v_inst_426_ = stack[1].m_obj;
lean_object* v_p_427_ = stack[2].m_obj;
lean_object* v_f_428_ = stack[3].m_obj;
uint8_t v_stopWhenVisited_429_ = stack[4].m_num;
lean_object* v_b_430_ = stack[5].m_obj;
lean_object* v___y_431_ = stack[6].m_obj;
lean_object* v_a_432_ = stack[7].m_obj;
lean_object* v_res_434_;
v_res_434_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___lam__0(v_inst_425_, v_inst_426_, v_p_427_, v_f_428_, v_stopWhenVisited_429_, v_b_430_, v___y_431_, v_a_432_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg___boxed(lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_p_437_, lean_object* v_f_438_, lean_object* v_stopWhenVisited_439_, lean_object* v_e_440_, lean_object* v_a_441_){
_start:
{
uint8_t v_stopWhenVisited_boxed_442_; lean_object* v_res_443_; 
v_stopWhenVisited_boxed_442_ = lean_unbox(v_stopWhenVisited_439_);
v_res_443_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_435_, v_inst_436_, v_p_437_, v_f_438_, v_stopWhenVisited_boxed_442_, v_e_440_, v_a_441_);
lean_dec(v_a_441_);
return v_res_443_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(lean_object* v_00_u03c9_444_, lean_object* v_m_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_p_449_, lean_object* v_f_450_, uint8_t v_stopWhenVisited_451_, lean_object* v_e_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_447_, v_inst_448_, v_p_449_, v_f_450_, v_stopWhenVisited_451_, v_e_452_, v_a_453_);
return v___x_454_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_446_ = stack[2].m_obj;
lean_object* v_inst_447_ = stack[3].m_obj;
lean_object* v_inst_448_ = stack[4].m_obj;
lean_object* v_p_449_ = stack[5].m_obj;
lean_object* v_f_450_ = stack[6].m_obj;
uint8_t v_stopWhenVisited_451_ = stack[7].m_num;
lean_object* v_e_452_ = stack[8].m_obj;
lean_object* v_a_453_ = stack[9].m_obj;
lean_object* v_res_455_;
v_res_455_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(lean_box(0), lean_box(0), v_inst_446_, v_inst_447_, v_inst_448_, v_p_449_, v_f_450_, v_stopWhenVisited_451_, v_e_452_, v_a_453_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___boxed(lean_object* v_00_u03c9_456_, lean_object* v_m_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_p_461_, lean_object* v_f_462_, lean_object* v_stopWhenVisited_463_, lean_object* v_e_464_, lean_object* v_a_465_){
_start:
{
uint8_t v_stopWhenVisited_boxed_466_; lean_object* v_res_467_; 
v_stopWhenVisited_boxed_466_ = lean_unbox(v_stopWhenVisited_463_);
v_res_467_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go(v_00_u03c9_456_, v_m_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_p_461_, v_f_462_, v_stopWhenVisited_boxed_466_, v_e_464_, v_a_465_);
lean_dec(v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__0(lean_object* v_a_468_, lean_object* v_toPure_469_, lean_object* v_s_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_a_468_);
lean_ctor_set(v___x_471_, 1, v_s_470_);
v___x_472_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__1(lean_object* v_toPure_473_, lean_object* v_ref_474_, lean_object* v_inst_475_, lean_object* v_toBind_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___f_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___f_478_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_478_, 0, v_a_477_);
lean_closure_set(v___f_478_, 1, v_toPure_473_);
v___x_479_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_479_, 0, lean_box(0));
lean_closure_set(v___x_479_, 1, lean_box(0));
lean_closure_set(v___x_479_, 2, v_ref_474_);
v___x_480_ = lean_apply_2(v_inst_475_, lean_box(0), v___x_479_);
v___x_481_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v___x_480_, v___f_478_);
return v___x_481_;
}
}
lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2(lean_object* v_toPure_482_, lean_object* v_inst_483_, lean_object* v_toBind_484_, lean_object* v_inst_485_, lean_object* v_p_486_, lean_object* v_f_487_, uint8_t v_stopWhenVisited_488_, lean_object* v_e_489_, lean_object* v_ref_490_){
_start:
{
lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_toBind_484_);
lean_inc(v_inst_483_);
lean_inc(v_ref_490_);
v___f_491_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_491_, 0, v_toPure_482_);
lean_closure_set(v___f_491_, 1, v_ref_490_);
lean_closure_set(v___f_491_, 2, v_inst_483_);
lean_closure_set(v___f_491_, 3, v_toBind_484_);
v___x_492_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___redArg(v_inst_483_, v_inst_485_, v_p_486_, v_f_487_, v_stopWhenVisited_488_, v_e_489_, v_ref_490_);
lean_dec(v_ref_490_);
v___x_493_ = lean_apply_4(v_toBind_484_, lean_box(0), lean_box(0), v___x_492_, v___f_491_);
return v___x_493_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visit___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_482_ = stack[0].m_obj;
lean_object* v_inst_483_ = stack[1].m_obj;
lean_object* v_toBind_484_ = stack[2].m_obj;
lean_object* v_inst_485_ = stack[3].m_obj;
lean_object* v_p_486_ = stack[4].m_obj;
lean_object* v_f_487_ = stack[5].m_obj;
uint8_t v_stopWhenVisited_488_ = stack[6].m_num;
lean_object* v_e_489_ = stack[7].m_obj;
lean_object* v_ref_490_ = stack[8].m_obj;
lean_object* v_res_494_;
v_res_494_ = l_Lean_ForEachExprWhere_visit___redArg___lam__2(v_toPure_482_, v_inst_483_, v_toBind_484_, v_inst_485_, v_p_486_, v_f_487_, v_stopWhenVisited_488_, v_e_489_, v_ref_490_);
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed(lean_object* v_toPure_495_, lean_object* v_inst_496_, lean_object* v_toBind_497_, lean_object* v_inst_498_, lean_object* v_p_499_, lean_object* v_f_500_, lean_object* v_stopWhenVisited_501_, lean_object* v_e_502_, lean_object* v_ref_503_){
_start:
{
uint8_t v_stopWhenVisited_boxed_504_; lean_object* v_res_505_; 
v_stopWhenVisited_boxed_504_ = lean_unbox(v_stopWhenVisited_501_);
v_res_505_ = l_Lean_ForEachExprWhere_visit___redArg___lam__2(v_toPure_495_, v_inst_496_, v_toBind_497_, v_inst_498_, v_p_499_, v_f_500_, v_stopWhenVisited_boxed_504_, v_e_502_, v_ref_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___lam__3(lean_object* v_toPure_506_, lean_object* v_____x_507_){
_start:
{
lean_object* v_fst_508_; lean_object* v___x_509_; 
v_fst_508_ = lean_ctor_get(v_____x_507_, 0);
lean_inc(v_fst_508_);
lean_dec_ref(v_____x_507_);
v___x_509_ = lean_apply_2(v_toPure_506_, lean_box(0), v_fst_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = l_Lean_ForEachExprWhere_initCache;
v___x_511_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_511_, 0, lean_box(0));
lean_closure_set(v___x_511_, 1, lean_box(0));
lean_closure_set(v___x_511_, 2, v___x_510_);
return v___x_511_;
}
}
lean_object* l_Lean_ForEachExprWhere_visit___redArg(lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_p_514_, lean_object* v_f_515_, lean_object* v_e_516_, uint8_t v_stopWhenVisited_517_){
_start:
{
lean_object* v_toApplicative_518_; lean_object* v_toBind_519_; lean_object* v_toPure_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_toApplicative_518_ = lean_ctor_get(v_inst_513_, 0);
v_toBind_519_ = lean_ctor_get(v_inst_513_, 1);
lean_inc_n(v_toBind_519_, 3);
v_toPure_520_ = lean_ctor_get(v_toApplicative_518_, 1);
lean_inc_n(v_toPure_520_, 2);
v___x_521_ = lean_obj_once(&l_Lean_ForEachExprWhere_visit___redArg___closed__0, &l_Lean_ForEachExprWhere_visit___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visit___redArg___closed__0);
lean_inc(v_inst_512_);
v___x_522_ = lean_apply_2(v_inst_512_, lean_box(0), v___x_521_);
v___x_523_ = lean_box(v_stopWhenVisited_517_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_524_, 0, v_toPure_520_);
lean_closure_set(v___f_524_, 1, v_inst_512_);
lean_closure_set(v___f_524_, 2, v_toBind_519_);
lean_closure_set(v___f_524_, 3, v_inst_513_);
lean_closure_set(v___f_524_, 4, v_p_514_);
lean_closure_set(v___f_524_, 5, v_f_515_);
lean_closure_set(v___f_524_, 6, v___x_523_);
lean_closure_set(v___f_524_, 7, v_e_516_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit___redArg___lam__3), 2, 1);
lean_closure_set(v___f_525_, 0, v_toPure_520_);
v___x_526_ = lean_apply_4(v_toBind_519_, lean_box(0), lean_box(0), v___x_522_, v___f_524_);
v___x_527_ = lean_apply_4(v_toBind_519_, lean_box(0), lean_box(0), v___x_526_, v___f_525_);
return v___x_527_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visit___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_512_ = stack[0].m_obj;
lean_object* v_inst_513_ = stack[1].m_obj;
lean_object* v_p_514_ = stack[2].m_obj;
lean_object* v_f_515_ = stack[3].m_obj;
lean_object* v_e_516_ = stack[4].m_obj;
uint8_t v_stopWhenVisited_517_ = stack[5].m_num;
lean_object* v_res_528_;
v_res_528_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_512_, v_inst_513_, v_p_514_, v_f_515_, v_e_516_, v_stopWhenVisited_517_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___redArg___boxed(lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_p_531_, lean_object* v_f_532_, lean_object* v_e_533_, lean_object* v_stopWhenVisited_534_){
_start:
{
uint8_t v_stopWhenVisited_boxed_535_; lean_object* v_res_536_; 
v_stopWhenVisited_boxed_535_ = lean_unbox(v_stopWhenVisited_534_);
v_res_536_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_529_, v_inst_530_, v_p_531_, v_f_532_, v_e_533_, v_stopWhenVisited_boxed_535_);
return v_res_536_;
}
}
lean_object* l_Lean_ForEachExprWhere_visit(lean_object* v_00_u03c9_537_, lean_object* v_m_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_p_542_, lean_object* v_f_543_, lean_object* v_e_544_, uint8_t v_stopWhenVisited_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_ForEachExprWhere_visit___redArg(v_inst_540_, v_inst_541_, v_p_542_, v_f_543_, v_e_544_, v_stopWhenVisited_545_);
return v___x_546_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_539_ = stack[2].m_obj;
lean_object* v_inst_540_ = stack[3].m_obj;
lean_object* v_inst_541_ = stack[4].m_obj;
lean_object* v_p_542_ = stack[5].m_obj;
lean_object* v_f_543_ = stack[6].m_obj;
lean_object* v_e_544_ = stack[7].m_obj;
uint8_t v_stopWhenVisited_545_ = stack[8].m_num;
lean_object* v_res_547_;
v_res_547_ = l_Lean_ForEachExprWhere_visit(lean_box(0), lean_box(0), v_inst_539_, v_inst_540_, v_inst_541_, v_p_542_, v_f_543_, v_e_544_, v_stopWhenVisited_545_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___boxed(lean_object* v_00_u03c9_548_, lean_object* v_m_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_p_553_, lean_object* v_f_554_, lean_object* v_e_555_, lean_object* v_stopWhenVisited_556_){
_start:
{
uint8_t v_stopWhenVisited_boxed_557_; lean_object* v_res_558_; 
v_stopWhenVisited_boxed_557_ = lean_unbox(v_stopWhenVisited_556_);
v_res_558_ = l_Lean_ForEachExprWhere_visit(v_00_u03c9_548_, v_m_549_, v_inst_550_, v_inst_551_, v_inst_552_, v_p_553_, v_f_554_, v_e_555_, v_stopWhenVisited_boxed_557_);
return v_res_558_;
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
