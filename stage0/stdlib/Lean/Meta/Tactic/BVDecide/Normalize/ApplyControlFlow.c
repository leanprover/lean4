// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow
// Imports: public import Lean.Meta.Tactic.Simp import Init.ByCases import Init.Omega public import Lean.Meta.Sym.Simp.SimpM
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "apply_ite"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(228, 253, 97, 171, 128, 176, 200, 75)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "apply_cond"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 139, 57, 144, 52, 240, 188, 35)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v___x_6_ = lean_name_eq(v_key_4_, v_a_1_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(lean_object* v_m_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_buckets_14_; lean_object* v___x_15_; uint64_t v___y_17_; 
v_buckets_14_ = lean_ctor_get(v_m_12_, 1);
v___x_15_ = lean_array_get_size(v_buckets_14_);
if (lean_obj_tag(v_a_13_) == 0)
{
uint64_t v___x_31_; 
v___x_31_ = 1723ULL;
v___y_17_ = v___x_31_;
goto v___jp_16_;
}
else
{
uint64_t v_hash_32_; 
v_hash_32_ = lean_ctor_get_uint64(v_a_13_, sizeof(void*)*2);
v___y_17_ = v_hash_32_;
goto v___jp_16_;
}
v___jp_16_:
{
uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v_fold_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; size_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_18_ = 32ULL;
v___x_19_ = lean_uint64_shift_right(v___y_17_, v___x_18_);
v_fold_20_ = lean_uint64_xor(v___y_17_, v___x_19_);
v___x_21_ = 16ULL;
v___x_22_ = lean_uint64_shift_right(v_fold_20_, v___x_21_);
v___x_23_ = lean_uint64_xor(v_fold_20_, v___x_22_);
v___x_24_ = lean_uint64_to_usize(v___x_23_);
v___x_25_ = lean_usize_of_nat(v___x_15_);
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_sub(v___x_25_, v___x_26_);
v___x_28_ = lean_usize_land(v___x_24_, v___x_27_);
v___x_29_ = lean_array_uget_borrowed(v_buckets_14_, v___x_28_);
v___x_30_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_a_13_, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___boxed(lean_object* v_m_33_, lean_object* v_a_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_m_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_m_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_box(0);
v___x_41_ = lean_unsigned_to_nat(5u);
v___x_42_ = lean_mk_empty_array_with_capacity(v___x_41_);
v___x_43_ = lean_array_push(v___x_42_, v___x_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(lean_object* v_headSyms_49_, lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
if (lean_obj_tag(v_x_50_) == 5)
{
lean_object* v_fn_60_; lean_object* v_arg_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_fn_60_ = lean_ctor_get(v_x_50_, 0);
lean_inc_ref(v_fn_60_);
v_arg_61_ = lean_ctor_get(v_x_50_, 1);
lean_inc_ref(v_arg_61_);
lean_dec_ref_known(v_x_50_, 2);
v___x_62_ = lean_array_set(v_x_51_, v_x_52_, v_arg_61_);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_sub(v_x_52_, v___x_63_);
lean_dec(v_x_52_);
v_x_50_ = v_fn_60_;
v_x_51_ = v___x_62_;
v_x_52_ = v___x_64_;
goto _start;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
lean_dec(v_x_52_);
v___x_66_ = lean_array_get_size(v_x_51_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_sub(v___x_66_, v___x_72_);
v___x_74_ = lean_array_fget_borrowed(v_x_51_, v___x_73_);
lean_dec(v___x_73_);
lean_inc(v___x_74_);
v___x_75_ = l_Lean_Expr_cleanupAnnotations(v___x_74_);
v___x_76_ = l_Lean_Expr_isApp(v___x_75_);
if (v___x_76_ == 0)
{
lean_dec_ref(v___x_75_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
goto v___jp_69_;
}
else
{
lean_object* v_arg_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_arg_77_ = lean_ctor_get(v___x_75_, 1);
lean_inc_ref(v_arg_77_);
v___x_78_ = l_Lean_Expr_appFnCleanup___redArg(v___x_75_);
v___x_79_ = l_Lean_Expr_isApp(v___x_78_);
if (v___x_79_ == 0)
{
lean_dec_ref(v___x_78_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
goto v___jp_69_;
}
else
{
lean_object* v_arg_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_arg_80_ = lean_ctor_get(v___x_78_, 1);
lean_inc_ref(v_arg_80_);
v___x_81_ = l_Lean_Expr_appFnCleanup___redArg(v___x_78_);
v___x_82_ = l_Lean_Expr_isApp(v___x_81_);
if (v___x_82_ == 0)
{
lean_dec_ref(v___x_81_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
goto v___jp_69_;
}
else
{
lean_object* v_arg_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_arg_83_ = lean_ctor_get(v___x_81_, 1);
lean_inc_ref(v_arg_83_);
v___x_84_ = l_Lean_Expr_appFnCleanup___redArg(v___x_81_);
v___x_85_ = l_Lean_Expr_isApp(v___x_84_);
if (v___x_85_ == 0)
{
lean_dec_ref(v___x_84_);
lean_dec_ref(v_arg_83_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
goto v___jp_69_;
}
else
{
lean_object* v_arg_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_arg_86_ = lean_ctor_get(v___x_84_, 1);
lean_inc_ref(v_arg_86_);
v___x_87_ = l_Lean_Expr_appFnCleanup___redArg(v___x_84_);
v___x_88_ = l_Lean_Expr_isApp(v___x_87_);
if (v___x_88_ == 0)
{
lean_dec_ref(v___x_87_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_83_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
goto v___jp_69_;
}
else
{
lean_object* v_arg_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_arg_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc_ref(v_arg_89_);
v___x_90_ = l_Lean_Expr_appFnCleanup___redArg(v___x_87_);
v___x_91_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1));
v___x_92_ = l_Lean_Expr_isConstOf(v___x_90_, v___x_91_);
lean_dec_ref(v___x_90_);
if (v___x_92_ == 0)
{
lean_dec_ref(v_arg_89_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_83_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
goto v___jp_69_;
}
else
{
if (lean_obj_tag(v_x_50_) == 4)
{
lean_object* v_declName_93_; uint8_t v___x_94_; 
v_declName_93_ = lean_ctor_get(v_x_50_, 0);
v___x_94_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_headSyms_49_, v_declName_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec_ref_known(v_x_50_, 2);
lean_dec_ref(v_arg_89_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_83_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_x_51_);
v___x_95_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_95_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v_params_97_; lean_object* v_fnApp_98_; lean_object* v_newT_99_; lean_object* v_newE_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_params_97_ = lean_array_pop(v_x_51_);
v_fnApp_98_ = l_Lean_mkAppN(v_x_50_, v_params_97_);
lean_dec_ref(v_params_97_);
lean_inc_ref(v_arg_80_);
lean_inc_ref_n(v_fnApp_98_, 2);
v_newT_99_ = l_Lean_Expr_app___override(v_fnApp_98_, v_arg_80_);
lean_inc_ref(v_arg_77_);
v_newE_100_ = l_Lean_Expr_app___override(v_fnApp_98_, v_arg_77_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_arg_86_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_arg_83_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_newT_99_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v_newE_100_);
v___x_106_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2);
lean_inc_ref(v___x_102_);
v___x_107_ = lean_array_push(v___x_106_, v___x_102_);
lean_inc_ref(v___x_103_);
v___x_108_ = lean_array_push(v___x_107_, v___x_103_);
v___x_109_ = lean_array_push(v___x_108_, v___x_104_);
v___x_110_ = lean_array_push(v___x_109_, v___x_105_);
v___x_111_ = l_Lean_Meta_mkAppOptM(v___x_91_, v___x_110_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v___x_113_ = l_Lean_Meta_Sym_shareCommonInc(v_a_112_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4));
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_arg_89_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v_fnApp_98_);
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v_arg_80_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_arg_77_);
v___x_120_ = lean_unsigned_to_nat(7u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_array_push(v___x_121_, v___x_116_);
v___x_123_ = lean_array_push(v___x_122_, v___x_101_);
v___x_124_ = lean_array_push(v___x_123_, v___x_117_);
v___x_125_ = lean_array_push(v___x_124_, v___x_102_);
v___x_126_ = lean_array_push(v___x_125_, v___x_103_);
v___x_127_ = lean_array_push(v___x_126_, v___x_118_);
v___x_128_ = lean_array_push(v___x_127_, v___x_119_);
v___x_129_ = l_Lean_Meta_mkAppOptM(v___x_115_, v___x_128_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_138_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_134_, 0, v_a_114_);
lean_ctor_set(v___x_134_, 1, v_a_130_);
lean_ctor_set_uint8(v___x_134_, sizeof(void*)*2, v___x_68_);
lean_ctor_set_uint8(v___x_134_, sizeof(void*)*2 + 1, v___x_68_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_114_);
v_a_139_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_129_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_129_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref_known(v___x_103_, 1);
lean_dec_ref_known(v___x_102_, 1);
lean_dec_ref(v_fnApp_98_);
lean_dec_ref(v_arg_89_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
v_a_147_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_113_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_113_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref_known(v___x_103_, 1);
lean_dec_ref_known(v___x_102_, 1);
lean_dec_ref(v_fnApp_98_);
lean_dec_ref(v_arg_89_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
v_a_155_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_111_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_111_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec_ref(v_arg_89_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_83_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
v___x_163_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_163_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_163_, 1, v___x_68_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
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
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
v___x_165_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5));
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
v___jp_69_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_70_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_70_, 1, v___x_68_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___boxed(lean_object* v_headSyms_167_, lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_167_, v_x_168_, v_x_169_, v_x_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v_headSyms_167_);
return v_res_178_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0(void){
_start:
{
lean_object* v___x_179_; lean_object* v_dummy_180_; 
v___x_179_ = lean_box(0);
v_dummy_180_ = l_Lean_Expr_sort___override(v___x_179_);
return v_dummy_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(lean_object* v_headSyms_181_, lean_object* v_e_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_dummy_193_; lean_object* v_nargs_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_dummy_193_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0);
v_nargs_194_ = l_Lean_Expr_getAppNumArgs(v_e_182_);
lean_inc(v_nargs_194_);
v___x_195_ = lean_mk_array(v_nargs_194_, v_dummy_193_);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_sub(v_nargs_194_, v___x_196_);
lean_dec(v_nargs_194_);
v___x_198_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_181_, v_e_182_, v___x_195_, v___x_197_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(lean_object* v_headSyms_199_, lean_object* v_e_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(v_headSyms_199_, v_e_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_headSyms_199_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(lean_object* v_00_u03b2_212_, lean_object* v_m_213_, lean_object* v_a_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_m_213_, v_a_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___boxed(lean_object* v_00_u03b2_216_, lean_object* v_m_217_, lean_object* v_a_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(v_00_u03b2_216_, v_m_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_m_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(lean_object* v_headSyms_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_221_, v_x_222_, v_x_223_, v_x_224_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___boxed(lean_object* v_headSyms_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(v_headSyms_236_, v_x_237_, v_x_238_, v_x_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v_headSyms_236_);
return v_res_250_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(lean_object* v_00_u03b2_251_, lean_object* v_a_252_, lean_object* v_x_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_a_252_, v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(v_00_u03b2_255_, v_a_256_, v_x_257_);
lean_dec(v_x_257_);
lean_dec(v_a_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_unsigned_to_nat(4u);
v___x_265_ = lean_mk_empty_array_with_capacity(v___x_264_);
v___x_266_ = lean_array_push(v___x_265_, v___x_263_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(lean_object* v_headSyms_272_, lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
if (lean_obj_tag(v_x_273_) == 5)
{
lean_object* v_fn_283_; lean_object* v_arg_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_fn_283_ = lean_ctor_get(v_x_273_, 0);
lean_inc_ref(v_fn_283_);
v_arg_284_ = lean_ctor_get(v_x_273_, 1);
lean_inc_ref(v_arg_284_);
lean_dec_ref_known(v_x_273_, 2);
v___x_285_ = lean_array_set(v_x_274_, v_x_275_, v_arg_284_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_sub(v_x_275_, v___x_286_);
lean_dec(v_x_275_);
v_x_273_ = v_fn_283_;
v_x_274_ = v___x_285_;
v_x_275_ = v___x_287_;
goto _start;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
lean_dec(v_x_275_);
v___x_289_ = lean_array_get_size(v_x_274_);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_nat_dec_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_sub(v___x_289_, v___x_295_);
v___x_297_ = lean_array_fget_borrowed(v_x_274_, v___x_296_);
lean_dec(v___x_296_);
lean_inc(v___x_297_);
v___x_298_ = l_Lean_Expr_cleanupAnnotations(v___x_297_);
v___x_299_ = l_Lean_Expr_isApp(v___x_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v___x_298_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_arg_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc_ref(v_arg_300_);
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_298_);
v___x_302_ = l_Lean_Expr_isApp(v___x_301_);
if (v___x_302_ == 0)
{
lean_dec_ref(v___x_301_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_arg_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc_ref(v_arg_303_);
v___x_304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_301_);
v___x_305_ = l_Lean_Expr_isApp(v___x_304_);
if (v___x_305_ == 0)
{
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_arg_306_ = lean_ctor_get(v___x_304_, 1);
lean_inc_ref(v_arg_306_);
v___x_307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_304_);
v___x_308_ = l_Lean_Expr_isApp(v___x_307_);
if (v___x_308_ == 0)
{
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
goto v___jp_292_;
}
else
{
lean_object* v_arg_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_arg_309_ = lean_ctor_get(v___x_307_, 1);
lean_inc_ref(v_arg_309_);
v___x_310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_307_);
v___x_311_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1));
v___x_312_ = l_Lean_Expr_isConstOf(v___x_310_, v___x_311_);
lean_dec_ref(v___x_310_);
if (v___x_312_ == 0)
{
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
goto v___jp_292_;
}
else
{
if (lean_obj_tag(v_x_273_) == 4)
{
lean_object* v_declName_313_; uint8_t v___x_314_; 
v_declName_313_ = lean_ctor_get(v_x_273_, 0);
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_headSyms_272_, v_declName_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref_known(v_x_273_, 2);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_x_274_);
v___x_315_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_315_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v_params_317_; lean_object* v_fnApp_318_; lean_object* v_newT_319_; lean_object* v_newE_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_params_317_ = lean_array_pop(v_x_274_);
v_fnApp_318_ = l_Lean_mkAppN(v_x_273_, v_params_317_);
lean_dec_ref(v_params_317_);
lean_inc_ref(v_arg_303_);
lean_inc_ref_n(v_fnApp_318_, 2);
v_newT_319_ = l_Lean_Expr_app___override(v_fnApp_318_, v_arg_303_);
lean_inc_ref(v_arg_300_);
v_newE_320_ = l_Lean_Expr_app___override(v_fnApp_318_, v_arg_300_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v_arg_306_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v_newT_319_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_newE_320_);
v___x_325_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2);
lean_inc_ref(v___x_322_);
v___x_326_ = lean_array_push(v___x_325_, v___x_322_);
v___x_327_ = lean_array_push(v___x_326_, v___x_323_);
v___x_328_ = lean_array_push(v___x_327_, v___x_324_);
v___x_329_ = l_Lean_Meta_mkAppOptM(v___x_311_, v___x_328_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = l_Lean_Meta_Sym_shareCommonInc(v_a_330_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5));
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v_arg_309_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_fnApp_318_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v_arg_303_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v_arg_300_);
v___x_338_ = lean_unsigned_to_nat(6u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_array_push(v___x_339_, v___x_334_);
v___x_341_ = lean_array_push(v___x_340_, v___x_321_);
v___x_342_ = lean_array_push(v___x_341_, v___x_335_);
v___x_343_ = lean_array_push(v___x_342_, v___x_322_);
v___x_344_ = lean_array_push(v___x_343_, v___x_336_);
v___x_345_ = lean_array_push(v___x_344_, v___x_337_);
v___x_346_ = l_Lean_Meta_mkAppOptM(v___x_333_, v___x_345_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_351_, 0, v_a_332_);
lean_ctor_set(v___x_351_, 1, v_a_347_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*2, v___x_291_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*2 + 1, v___x_291_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_a_332_);
v_a_356_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_346_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_346_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref_known(v___x_322_, 1);
lean_dec_ref(v_fnApp_318_);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
v_a_364_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_331_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_331_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref_known(v___x_322_, 1);
lean_dec_ref(v_fnApp_318_);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
v_a_372_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_329_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_329_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_arg_300_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
v___x_380_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_380_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_380_, 1, v___x_291_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
v___x_382_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5));
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
v___jp_292_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_293_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_293_, 1, v___x_291_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___boxed(lean_object* v_headSyms_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_384_, v_x_385_, v_x_386_, v_x_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec_ref(v_headSyms_384_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(lean_object* v_headSyms_396_, lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_dummy_408_; lean_object* v_nargs_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_dummy_408_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0);
v_nargs_409_ = l_Lean_Expr_getAppNumArgs(v_e_397_);
lean_inc(v_nargs_409_);
v___x_410_ = lean_mk_array(v_nargs_409_, v_dummy_408_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_sub(v_nargs_409_, v___x_411_);
lean_dec(v_nargs_409_);
v___x_413_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_396_, v_e_397_, v___x_410_, v___x_412_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(lean_object* v_headSyms_414_, lean_object* v_e_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(v_headSyms_414_, v_e_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_headSyms_414_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(lean_object* v_headSyms_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_427_, v_x_428_, v_x_429_, v_x_430_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___boxed(lean_object* v_headSyms_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(v_headSyms_442_, v_x_443_, v_x_444_, v_x_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v_headSyms_442_);
return v_res_456_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin) {
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
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif
