// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ApplyControlFlow
// Imports: public import Lean.Meta.Tactic.Simp import Init.ByCases import Init.Omega
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "apply_ite"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(228, 253, 97, 171, 128, 176, 200, 75)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__2;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "apply_cond"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 139, 57, 144, 52, 240, 188, 35)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyUnaryControlDiscrPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = lean_box(0);
v___x_7_ = lean_unsigned_to_nat(5u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_array_push(v___x_8_, v___x_6_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg(lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
if (lean_obj_tag(v_x_13_) == 5)
{
lean_object* v_fn_24_; lean_object* v_arg_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_fn_24_ = lean_ctor_get(v_x_13_, 0);
lean_inc_ref(v_fn_24_);
v_arg_25_ = lean_ctor_get(v_x_13_, 1);
lean_inc_ref(v_arg_25_);
lean_dec_ref(v_x_13_);
v___x_26_ = lean_array_set(v_x_14_, v_x_15_, v_arg_25_);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_sub(v_x_15_, v___x_27_);
lean_dec(v_x_15_);
v_x_13_ = v_fn_24_;
v_x_14_ = v___x_26_;
v_x_15_ = v___x_28_;
goto _start;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
lean_dec(v_x_15_);
v___x_30_ = lean_array_get_size(v_x_14_);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_nat_dec_eq(v___x_30_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_sub(v___x_30_, v___x_33_);
v___x_35_ = lean_array_fget_borrowed(v_x_14_, v___x_34_);
lean_dec(v___x_34_);
lean_inc(v___x_35_);
v___x_36_ = l_Lean_Expr_cleanupAnnotations(v___x_35_);
v___x_37_ = l_Lean_Expr_isApp(v___x_36_);
if (v___x_37_ == 0)
{
lean_dec_ref(v___x_36_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_arg_38_ = lean_ctor_get(v___x_36_, 1);
lean_inc_ref(v_arg_38_);
v___x_39_ = l_Lean_Expr_appFnCleanup___redArg(v___x_36_);
v___x_40_ = l_Lean_Expr_isApp(v___x_39_);
if (v___x_40_ == 0)
{
lean_dec_ref(v___x_39_);
lean_dec_ref(v_arg_38_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_arg_41_ = lean_ctor_get(v___x_39_, 1);
lean_inc_ref(v_arg_41_);
v___x_42_ = l_Lean_Expr_appFnCleanup___redArg(v___x_39_);
v___x_43_ = l_Lean_Expr_isApp(v___x_42_);
if (v___x_43_ == 0)
{
lean_dec_ref(v___x_42_);
lean_dec_ref(v_arg_41_);
lean_dec_ref(v_arg_38_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_arg_44_ = lean_ctor_get(v___x_42_, 1);
lean_inc_ref(v_arg_44_);
v___x_45_ = l_Lean_Expr_appFnCleanup___redArg(v___x_42_);
v___x_46_ = l_Lean_Expr_isApp(v___x_45_);
if (v___x_46_ == 0)
{
lean_dec_ref(v___x_45_);
lean_dec_ref(v_arg_44_);
lean_dec_ref(v_arg_41_);
lean_dec_ref(v_arg_38_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_arg_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc_ref(v_arg_47_);
v___x_48_ = l_Lean_Expr_appFnCleanup___redArg(v___x_45_);
v___x_49_ = l_Lean_Expr_isApp(v___x_48_);
if (v___x_49_ == 0)
{
lean_dec_ref(v___x_48_);
lean_dec_ref(v_arg_47_);
lean_dec_ref(v_arg_44_);
lean_dec_ref(v_arg_41_);
lean_dec_ref(v_arg_38_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_arg_50_ = lean_ctor_get(v___x_48_, 1);
lean_inc_ref(v_arg_50_);
v___x_51_ = l_Lean_Expr_appFnCleanup___redArg(v___x_48_);
v___x_52_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__2));
v___x_53_ = l_Lean_Expr_isConstOf(v___x_51_, v___x_52_);
lean_dec_ref(v___x_51_);
if (v___x_53_ == 0)
{
lean_dec_ref(v_arg_50_);
lean_dec_ref(v_arg_47_);
lean_dec_ref(v_arg_44_);
lean_dec_ref(v_arg_41_);
lean_dec_ref(v_arg_38_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
goto v___jp_21_;
}
else
{
lean_object* v_params_54_; lean_object* v_fnApp_55_; lean_object* v_newT_56_; lean_object* v_newE_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_params_54_ = lean_array_pop(v_x_14_);
v_fnApp_55_ = l_Lean_mkAppN(v_x_13_, v_params_54_);
lean_dec_ref(v_params_54_);
lean_inc_ref(v_arg_41_);
lean_inc_ref_n(v_fnApp_55_, 2);
v_newT_56_ = l_Lean_Expr_app___override(v_fnApp_55_, v_arg_41_);
lean_inc_ref(v_arg_38_);
v_newE_57_ = l_Lean_Expr_app___override(v_fnApp_55_, v_arg_38_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v_arg_47_);
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v_arg_44_);
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v_newT_56_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v_newE_57_);
v___x_63_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__3);
lean_inc_ref(v___x_59_);
v___x_64_ = lean_array_push(v___x_63_, v___x_59_);
lean_inc_ref(v___x_60_);
v___x_65_ = lean_array_push(v___x_64_, v___x_60_);
v___x_66_ = lean_array_push(v___x_65_, v___x_61_);
v___x_67_ = lean_array_push(v___x_66_, v___x_62_);
v___x_68_ = l_Lean_Meta_mkAppOptM(v___x_52_, v___x_67_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref(v___x_68_);
v___x_70_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__5));
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v_arg_50_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v_fnApp_55_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_arg_41_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v_arg_38_);
v___x_75_ = lean_unsigned_to_nat(7u);
v___x_76_ = lean_mk_empty_array_with_capacity(v___x_75_);
v___x_77_ = lean_array_push(v___x_76_, v___x_71_);
v___x_78_ = lean_array_push(v___x_77_, v___x_58_);
v___x_79_ = lean_array_push(v___x_78_, v___x_72_);
v___x_80_ = lean_array_push(v___x_79_, v___x_59_);
v___x_81_ = lean_array_push(v___x_80_, v___x_60_);
v___x_82_ = lean_array_push(v___x_81_, v___x_73_);
v___x_83_ = lean_array_push(v___x_82_, v___x_74_);
v___x_84_ = l_Lean_Meta_mkAppOptM(v___x_70_, v___x_83_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_95_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_95_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_95_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_95_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_a_85_);
v___x_90_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_90_, 0, v_a_69_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*2, v___x_53_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_91_);
v___x_93_ = v___x_87_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec(v_a_69_);
v_a_96_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_84_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_84_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec_ref(v___x_60_);
lean_dec_ref(v___x_59_);
lean_dec_ref(v_fnApp_55_);
lean_dec_ref(v_arg_50_);
lean_dec_ref(v_arg_41_);
lean_dec_ref(v_arg_38_);
v_a_104_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_68_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_68_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
v___x_112_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__0));
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
v___jp_21_:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__0));
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___boxed(lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg(v_x_114_, v_x_115_, v_x_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0(void){
_start:
{
lean_object* v___x_123_; lean_object* v_dummy_124_; 
v___x_123_ = lean_box(0);
v_dummy_124_ = l_Lean_Expr_sort___override(v___x_123_);
return v_dummy_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc(lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_dummy_134_; lean_object* v_nargs_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_dummy_134_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0);
v_nargs_135_ = l_Lean_Expr_getAppNumArgs(v_e_125_);
lean_inc(v_nargs_135_);
v___x_136_ = lean_mk_array(v_nargs_135_, v_dummy_134_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_sub(v_nargs_135_, v___x_137_);
lean_dec(v_nargs_135_);
v___x_139_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg(v_e_125_, v___x_136_, v___x_138_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___boxed(lean_object* v_e_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc(v_e_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg(v_x_150_, v_x_151_, v_x_152_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___boxed(lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0(v_x_162_, v_x_163_, v_x_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = lean_box(0);
v___x_178_ = lean_unsigned_to_nat(4u);
v___x_179_ = lean_mk_empty_array_with_capacity(v___x_178_);
v___x_180_ = lean_array_push(v___x_179_, v___x_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
if (lean_obj_tag(v_x_186_) == 5)
{
lean_object* v_fn_197_; lean_object* v_arg_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_fn_197_ = lean_ctor_get(v_x_186_, 0);
lean_inc_ref(v_fn_197_);
v_arg_198_ = lean_ctor_get(v_x_186_, 1);
lean_inc_ref(v_arg_198_);
lean_dec_ref(v_x_186_);
v___x_199_ = lean_array_set(v_x_187_, v_x_188_, v_arg_198_);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_sub(v_x_188_, v___x_200_);
lean_dec(v_x_188_);
v_x_186_ = v_fn_197_;
v_x_187_ = v___x_199_;
v_x_188_ = v___x_201_;
goto _start;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
lean_dec(v_x_188_);
v___x_203_ = lean_array_get_size(v_x_187_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_sub(v___x_203_, v___x_206_);
v___x_208_ = lean_array_fget_borrowed(v_x_187_, v___x_207_);
lean_dec(v___x_207_);
lean_inc(v___x_208_);
v___x_209_ = l_Lean_Expr_cleanupAnnotations(v___x_208_);
v___x_210_ = l_Lean_Expr_isApp(v___x_209_);
if (v___x_210_ == 0)
{
lean_dec_ref(v___x_209_);
lean_dec_ref(v_x_187_);
lean_dec_ref(v_x_186_);
goto v___jp_194_;
}
else
{
lean_object* v_arg_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_arg_211_ = lean_ctor_get(v___x_209_, 1);
lean_inc_ref(v_arg_211_);
v___x_212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_209_);
v___x_213_ = l_Lean_Expr_isApp(v___x_212_);
if (v___x_213_ == 0)
{
lean_dec_ref(v___x_212_);
lean_dec_ref(v_arg_211_);
lean_dec_ref(v_x_187_);
lean_dec_ref(v_x_186_);
goto v___jp_194_;
}
else
{
lean_object* v_arg_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_arg_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc_ref(v_arg_214_);
v___x_215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_212_);
v___x_216_ = l_Lean_Expr_isApp(v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v___x_215_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_211_);
lean_dec_ref(v_x_187_);
lean_dec_ref(v_x_186_);
goto v___jp_194_;
}
else
{
lean_object* v_arg_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_arg_217_ = lean_ctor_get(v___x_215_, 1);
lean_inc_ref(v_arg_217_);
v___x_218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_215_);
v___x_219_ = l_Lean_Expr_isApp(v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v___x_218_);
lean_dec_ref(v_arg_217_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_211_);
lean_dec_ref(v_x_187_);
lean_dec_ref(v_x_186_);
goto v___jp_194_;
}
else
{
lean_object* v_arg_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_arg_220_ = lean_ctor_get(v___x_218_, 1);
lean_inc_ref(v_arg_220_);
v___x_221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_218_);
v___x_222_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__1));
v___x_223_ = l_Lean_Expr_isConstOf(v___x_221_, v___x_222_);
lean_dec_ref(v___x_221_);
if (v___x_223_ == 0)
{
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_217_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_211_);
lean_dec_ref(v_x_187_);
lean_dec_ref(v_x_186_);
goto v___jp_194_;
}
else
{
lean_object* v_params_224_; lean_object* v_fnApp_225_; lean_object* v_newT_226_; lean_object* v_newE_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_params_224_ = lean_array_pop(v_x_187_);
v_fnApp_225_ = l_Lean_mkAppN(v_x_186_, v_params_224_);
lean_dec_ref(v_params_224_);
lean_inc_ref(v_arg_214_);
lean_inc_ref_n(v_fnApp_225_, 2);
v_newT_226_ = l_Lean_Expr_app___override(v_fnApp_225_, v_arg_214_);
lean_inc_ref(v_arg_211_);
v_newE_227_ = l_Lean_Expr_app___override(v_fnApp_225_, v_arg_211_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_arg_217_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_newT_226_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v_newE_227_);
v___x_232_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__2);
lean_inc_ref(v___x_229_);
v___x_233_ = lean_array_push(v___x_232_, v___x_229_);
v___x_234_ = lean_array_push(v___x_233_, v___x_230_);
v___x_235_ = lean_array_push(v___x_234_, v___x_231_);
v___x_236_ = l_Lean_Meta_mkAppOptM(v___x_222_, v___x_235_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
v___x_238_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___closed__5));
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v_arg_220_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_fnApp_225_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v_arg_214_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_arg_211_);
v___x_243_ = lean_unsigned_to_nat(6u);
v___x_244_ = lean_mk_empty_array_with_capacity(v___x_243_);
v___x_245_ = lean_array_push(v___x_244_, v___x_239_);
v___x_246_ = lean_array_push(v___x_245_, v___x_228_);
v___x_247_ = lean_array_push(v___x_246_, v___x_240_);
v___x_248_ = lean_array_push(v___x_247_, v___x_229_);
v___x_249_ = lean_array_push(v___x_248_, v___x_241_);
v___x_250_ = lean_array_push(v___x_249_, v___x_242_);
v___x_251_ = l_Lean_Meta_mkAppOptM(v___x_238_, v___x_250_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v_a_252_);
v___x_257_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_257_, 0, v_a_237_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*2, v___x_223_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_258_);
v___x_260_ = v___x_254_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_a_237_);
v_a_263_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_251_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_251_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v___x_229_);
lean_dec_ref(v_fnApp_225_);
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_214_);
lean_dec_ref(v_arg_211_);
v_a_271_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_236_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_236_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v_x_187_);
lean_dec_ref(v_x_186_);
v___x_279_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__0));
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
v___jp_194_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc_spec__0___redArg___closed__0));
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg___boxed(lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg(v_x_281_, v_x_282_, v_x_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_dummy_299_; lean_object* v_nargs_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_dummy_299_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___closed__0);
v_nargs_300_ = l_Lean_Expr_getAppNumArgs(v_e_290_);
lean_inc(v_nargs_300_);
v___x_301_ = lean_mk_array(v_nargs_300_, v_dummy_299_);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_sub(v_nargs_300_, v___x_302_);
lean_dec(v_nargs_300_);
v___x_304_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg(v_e_290_, v___x_301_, v___x_303_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc___boxed(lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc(v_e_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0(lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___redArg(v_x_315_, v_x_316_, v_x_317_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0___boxed(lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc_spec__0(v_x_327_, v_x_328_, v_x_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(lean_object* v_j_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_zero_341_; uint8_t v_isZero_342_; 
v_zero_341_ = lean_unsigned_to_nat(0u);
v_isZero_342_ = lean_nat_dec_eq(v_j_339_, v_zero_341_);
if (v_isZero_342_ == 1)
{
lean_dec(v_j_339_);
return v_a_340_;
}
else
{
lean_object* v_one_343_; lean_object* v_n_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_one_343_ = lean_unsigned_to_nat(1u);
v_n_344_ = lean_nat_sub(v_j_339_, v_one_343_);
lean_dec(v_j_339_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_array_push(v_a_340_, v___x_345_);
v_j_339_ = v_n_344_;
v_a_340_ = v___x_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath(lean_object* v_struct_348_, lean_object* v_structParams_349_, lean_object* v_projIdx_350_, lean_object* v_controlFlow_351_, lean_object* v_controlFlowParams_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_stars_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_path_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_path_361_; lean_object* v___x_362_; lean_object* v_path_363_; lean_object* v___x_364_; lean_object* v_path_365_; lean_object* v___x_366_; 
v___x_353_ = lean_nat_add(v_structParams_349_, v_controlFlowParams_352_);
v___x_354_ = lean_unsigned_to_nat(1u);
v_stars_355_ = lean_nat_sub(v___x_353_, v___x_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_unsigned_to_nat(3u);
v___x_357_ = lean_nat_add(v___x_356_, v_stars_355_);
v_path_358_ = lean_mk_empty_array_with_capacity(v___x_357_);
lean_dec(v___x_357_);
v___x_359_ = lean_unsigned_to_nat(0u);
lean_inc(v_struct_348_);
v___x_360_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_360_, 0, v_struct_348_);
lean_ctor_set(v___x_360_, 1, v_projIdx_350_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
v_path_361_ = lean_array_push(v_path_358_, v___x_360_);
v___x_362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_362_, 0, v_controlFlow_351_);
lean_ctor_set(v___x_362_, 1, v_controlFlowParams_352_);
v_path_363_ = lean_array_push(v_path_361_, v___x_362_);
v___x_364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_364_, 0, v_struct_348_);
lean_ctor_set(v___x_364_, 1, v_structParams_349_);
v_path_365_ = lean_array_push(v_path_363_, v___x_364_);
v___x_366_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(v_stars_355_, v_path_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0(lean_object* v_n_367_, lean_object* v_j_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(v_j_368_, v_a_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0___boxed(lean_object* v_n_372_, lean_object* v_j_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0(v_n_372_, v_j_373_, v_a_374_, v_a_375_);
lean_dec(v_n_372_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyUnaryControlDiscrPath(lean_object* v_type_377_, lean_object* v_typeParams_378_, lean_object* v_constName_379_, lean_object* v_controlFlow_380_, lean_object* v_controlFlowParams_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_stars_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_path_387_; lean_object* v___x_388_; lean_object* v_path_389_; lean_object* v___x_390_; lean_object* v_path_391_; lean_object* v___x_392_; lean_object* v_path_393_; lean_object* v_path_394_; 
v___x_382_ = lean_nat_add(v_typeParams_378_, v_controlFlowParams_381_);
v___x_383_ = lean_unsigned_to_nat(1u);
v_stars_384_ = lean_nat_sub(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_unsigned_to_nat(3u);
v___x_386_ = lean_nat_add(v___x_385_, v_stars_384_);
v_path_387_ = lean_mk_empty_array_with_capacity(v___x_386_);
lean_dec(v___x_386_);
v___x_388_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_388_, 0, v_constName_379_);
lean_ctor_set(v___x_388_, 1, v___x_383_);
v_path_389_ = lean_array_push(v_path_387_, v___x_388_);
v___x_390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_390_, 0, v_controlFlow_380_);
lean_ctor_set(v___x_390_, 1, v_controlFlowParams_381_);
v_path_391_ = lean_array_push(v_path_389_, v___x_390_);
v___x_392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_392_, 0, v_type_377_);
lean_ctor_set(v___x_392_, 1, v_typeParams_378_);
v_path_393_ = lean_array_push(v_path_391_, v___x_392_);
v_path_394_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(v_stars_384_, v_path_393_);
return v_path_394_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif
