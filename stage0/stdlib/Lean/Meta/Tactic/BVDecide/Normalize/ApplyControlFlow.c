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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0;
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
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_12_; uint64_t v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(1723u);
v___x_13_ = lean_uint64_of_nat(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(lean_object* v_m_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_buckets_16_; lean_object* v___x_17_; uint64_t v___y_19_; 
v_buckets_16_ = lean_ctor_get(v_m_14_, 1);
v___x_17_ = lean_array_get_size(v_buckets_16_);
if (lean_obj_tag(v_a_15_) == 0)
{
uint64_t v___x_33_; 
v___x_33_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0);
v___y_19_ = v___x_33_;
goto v___jp_18_;
}
else
{
uint64_t v_hash_34_; 
v_hash_34_ = lean_ctor_get_uint64(v_a_15_, sizeof(void*)*2);
v___y_19_ = v_hash_34_;
goto v___jp_18_;
}
v___jp_18_:
{
uint64_t v___x_20_; uint64_t v___x_21_; uint64_t v_fold_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_20_ = 32ULL;
v___x_21_ = lean_uint64_shift_right(v___y_19_, v___x_20_);
v_fold_22_ = lean_uint64_xor(v___y_19_, v___x_21_);
v___x_23_ = 16ULL;
v___x_24_ = lean_uint64_shift_right(v_fold_22_, v___x_23_);
v___x_25_ = lean_uint64_xor(v_fold_22_, v___x_24_);
v___x_26_ = lean_uint64_to_usize(v___x_25_);
v___x_27_ = lean_usize_of_nat(v___x_17_);
v___x_28_ = ((size_t)1ULL);
v___x_29_ = lean_usize_sub(v___x_27_, v___x_28_);
v___x_30_ = lean_usize_land(v___x_26_, v___x_29_);
v___x_31_ = lean_array_uget_borrowed(v_buckets_16_, v___x_30_);
v___x_32_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_a_15_, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___boxed(lean_object* v_m_35_, lean_object* v_a_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_m_35_, v_a_36_);
lean_dec(v_a_36_);
lean_dec_ref(v_m_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_42_ = lean_box(0);
v___x_43_ = lean_unsigned_to_nat(5u);
v___x_44_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_45_ = lean_array_push(v___x_44_, v___x_42_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(lean_object* v_headSyms_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
if (lean_obj_tag(v_x_52_) == 5)
{
lean_object* v_fn_62_; lean_object* v_arg_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_fn_62_ = lean_ctor_get(v_x_52_, 0);
lean_inc_ref(v_fn_62_);
v_arg_63_ = lean_ctor_get(v_x_52_, 1);
lean_inc_ref(v_arg_63_);
lean_dec_ref_known(v_x_52_, 2);
v___x_64_ = lean_array_set(v_x_53_, v_x_54_, v_arg_63_);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_sub(v_x_54_, v___x_65_);
lean_dec(v_x_54_);
v_x_52_ = v_fn_62_;
v_x_53_ = v___x_64_;
v_x_54_ = v___x_66_;
goto _start;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
lean_dec(v_x_54_);
v___x_68_ = lean_array_get_size(v_x_53_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_dec_eq(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_sub(v___x_68_, v___x_74_);
v___x_76_ = lean_array_fget_borrowed(v_x_53_, v___x_75_);
lean_dec(v___x_75_);
lean_inc(v___x_76_);
v___x_77_ = l_Lean_Expr_cleanupAnnotations(v___x_76_);
v___x_78_ = l_Lean_Expr_isApp(v___x_77_);
if (v___x_78_ == 0)
{
lean_dec_ref(v___x_77_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
goto v___jp_71_;
}
else
{
lean_object* v_arg_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_arg_79_ = lean_ctor_get(v___x_77_, 1);
lean_inc_ref(v_arg_79_);
v___x_80_ = l_Lean_Expr_appFnCleanup___redArg(v___x_77_);
v___x_81_ = l_Lean_Expr_isApp(v___x_80_);
if (v___x_81_ == 0)
{
lean_dec_ref(v___x_80_);
lean_dec_ref(v_arg_79_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
goto v___jp_71_;
}
else
{
lean_object* v_arg_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_arg_82_ = lean_ctor_get(v___x_80_, 1);
lean_inc_ref(v_arg_82_);
v___x_83_ = l_Lean_Expr_appFnCleanup___redArg(v___x_80_);
v___x_84_ = l_Lean_Expr_isApp(v___x_83_);
if (v___x_84_ == 0)
{
lean_dec_ref(v___x_83_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
goto v___jp_71_;
}
else
{
lean_object* v_arg_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_arg_85_ = lean_ctor_get(v___x_83_, 1);
lean_inc_ref(v_arg_85_);
v___x_86_ = l_Lean_Expr_appFnCleanup___redArg(v___x_83_);
v___x_87_ = l_Lean_Expr_isApp(v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v___x_86_);
lean_dec_ref(v_arg_85_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
goto v___jp_71_;
}
else
{
lean_object* v_arg_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_arg_88_ = lean_ctor_get(v___x_86_, 1);
lean_inc_ref(v_arg_88_);
v___x_89_ = l_Lean_Expr_appFnCleanup___redArg(v___x_86_);
v___x_90_ = l_Lean_Expr_isApp(v___x_89_);
if (v___x_90_ == 0)
{
lean_dec_ref(v___x_89_);
lean_dec_ref(v_arg_88_);
lean_dec_ref(v_arg_85_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
goto v___jp_71_;
}
else
{
lean_object* v_arg_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v_arg_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc_ref(v_arg_91_);
v___x_92_ = l_Lean_Expr_appFnCleanup___redArg(v___x_89_);
v___x_93_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1));
v___x_94_ = l_Lean_Expr_isConstOf(v___x_92_, v___x_93_);
lean_dec_ref(v___x_92_);
if (v___x_94_ == 0)
{
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_88_);
lean_dec_ref(v_arg_85_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
goto v___jp_71_;
}
else
{
if (lean_obj_tag(v_x_52_) == 4)
{
lean_object* v_declName_95_; uint8_t v___x_96_; 
v_declName_95_ = lean_ctor_get(v_x_52_, 0);
v___x_96_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_headSyms_51_, v_declName_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec_ref_known(v_x_52_, 2);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_88_);
lean_dec_ref(v_arg_85_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
lean_dec_ref(v_x_53_);
v___x_97_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_97_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
else
{
lean_object* v_params_99_; lean_object* v_fnApp_100_; lean_object* v_newT_101_; lean_object* v_newE_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_params_99_ = lean_array_pop(v_x_53_);
v_fnApp_100_ = l_Lean_mkAppN(v_x_52_, v_params_99_);
lean_dec_ref(v_params_99_);
lean_inc_ref(v_arg_82_);
lean_inc_ref_n(v_fnApp_100_, 2);
v_newT_101_ = l_Lean_Expr_app___override(v_fnApp_100_, v_arg_82_);
lean_inc_ref(v_arg_79_);
v_newE_102_ = l_Lean_Expr_app___override(v_fnApp_100_, v_arg_79_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_arg_88_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v_arg_85_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v_newT_101_);
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_newE_102_);
v___x_108_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2);
lean_inc_ref(v___x_104_);
v___x_109_ = lean_array_push(v___x_108_, v___x_104_);
lean_inc_ref(v___x_105_);
v___x_110_ = lean_array_push(v___x_109_, v___x_105_);
v___x_111_ = lean_array_push(v___x_110_, v___x_106_);
v___x_112_ = lean_array_push(v___x_111_, v___x_107_);
v___x_113_ = l_Lean_Meta_mkAppOptM(v___x_93_, v___x_112_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = l_Lean_Meta_Sym_shareCommonInc(v_a_114_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4));
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v_arg_91_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_fnApp_100_);
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v_arg_82_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v_arg_79_);
v___x_122_ = lean_unsigned_to_nat(7u);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
v___x_124_ = lean_array_push(v___x_123_, v___x_118_);
v___x_125_ = lean_array_push(v___x_124_, v___x_103_);
v___x_126_ = lean_array_push(v___x_125_, v___x_119_);
v___x_127_ = lean_array_push(v___x_126_, v___x_104_);
v___x_128_ = lean_array_push(v___x_127_, v___x_105_);
v___x_129_ = lean_array_push(v___x_128_, v___x_120_);
v___x_130_ = lean_array_push(v___x_129_, v___x_121_);
v___x_131_ = l_Lean_Meta_mkAppOptM(v___x_117_, v___x_130_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_136_, 0, v_a_116_);
lean_ctor_set(v___x_136_, 1, v_a_132_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*2, v___x_70_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*2 + 1, v___x_70_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_a_116_);
v_a_141_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_131_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_131_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref_known(v___x_105_, 1);
lean_dec_ref_known(v___x_104_, 1);
lean_dec_ref(v_fnApp_100_);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
v_a_149_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_115_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_115_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref_known(v___x_105_, 1);
lean_dec_ref_known(v___x_104_, 1);
lean_dec_ref(v_fnApp_100_);
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
v_a_157_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_113_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_113_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref(v_arg_91_);
lean_dec_ref(v_arg_88_);
lean_dec_ref(v_arg_85_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_79_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
v___x_165_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_165_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_165_, 1, v___x_70_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
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
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
v___x_167_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5));
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
v___jp_71_:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_72_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_72_, 1, v___x_70_);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___boxed(lean_object* v_headSyms_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_169_, v_x_170_, v_x_171_, v_x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v_headSyms_169_);
return v_res_180_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0(void){
_start:
{
lean_object* v___x_181_; lean_object* v_dummy_182_; 
v___x_181_ = lean_box(0);
v_dummy_182_ = l_Lean_Expr_sort___override(v___x_181_);
return v_dummy_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(lean_object* v_headSyms_183_, lean_object* v_e_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_dummy_195_; lean_object* v_nargs_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_dummy_195_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0);
v_nargs_196_ = l_Lean_Expr_getAppNumArgs(v_e_184_);
lean_inc(v_nargs_196_);
v___x_197_ = lean_mk_array(v_nargs_196_, v_dummy_195_);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_sub(v_nargs_196_, v___x_198_);
lean_dec(v_nargs_196_);
v___x_200_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_183_, v_e_184_, v___x_197_, v___x_199_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(lean_object* v_headSyms_201_, lean_object* v_e_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(v_headSyms_201_, v_e_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_headSyms_201_);
return v_res_213_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(lean_object* v_00_u03b2_214_, lean_object* v_m_215_, lean_object* v_a_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_m_215_, v_a_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___boxed(lean_object* v_00_u03b2_218_, lean_object* v_m_219_, lean_object* v_a_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(v_00_u03b2_218_, v_m_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_m_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(lean_object* v_headSyms_223_, lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_223_, v_x_224_, v_x_225_, v_x_226_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___boxed(lean_object* v_headSyms_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(v_headSyms_238_, v_x_239_, v_x_240_, v_x_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v_headSyms_238_);
return v_res_252_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(lean_object* v_00_u03b2_253_, lean_object* v_a_254_, lean_object* v_x_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_a_254_, v_x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_257_, lean_object* v_a_258_, lean_object* v_x_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(v_00_u03b2_257_, v_a_258_, v_x_259_);
lean_dec(v_x_259_);
lean_dec(v_a_258_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_box(0);
v___x_266_ = lean_unsigned_to_nat(4u);
v___x_267_ = lean_mk_empty_array_with_capacity(v___x_266_);
v___x_268_ = lean_array_push(v___x_267_, v___x_265_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(lean_object* v_headSyms_274_, lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
if (lean_obj_tag(v_x_275_) == 5)
{
lean_object* v_fn_285_; lean_object* v_arg_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_fn_285_ = lean_ctor_get(v_x_275_, 0);
lean_inc_ref(v_fn_285_);
v_arg_286_ = lean_ctor_get(v_x_275_, 1);
lean_inc_ref(v_arg_286_);
lean_dec_ref_known(v_x_275_, 2);
v___x_287_ = lean_array_set(v_x_276_, v_x_277_, v_arg_286_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_sub(v_x_277_, v___x_288_);
lean_dec(v_x_277_);
v_x_275_ = v_fn_285_;
v_x_276_ = v___x_287_;
v_x_277_ = v___x_289_;
goto _start;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
lean_dec(v_x_277_);
v___x_291_ = lean_array_get_size(v_x_276_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_nat_dec_eq(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_sub(v___x_291_, v___x_297_);
v___x_299_ = lean_array_fget_borrowed(v_x_276_, v___x_298_);
lean_dec(v___x_298_);
lean_inc(v___x_299_);
v___x_300_ = l_Lean_Expr_cleanupAnnotations(v___x_299_);
v___x_301_ = l_Lean_Expr_isApp(v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref(v___x_300_);
lean_dec_ref(v_x_276_);
lean_dec_ref(v_x_275_);
goto v___jp_294_;
}
else
{
lean_object* v_arg_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_arg_302_ = lean_ctor_get(v___x_300_, 1);
lean_inc_ref(v_arg_302_);
v___x_303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_300_);
v___x_304_ = l_Lean_Expr_isApp(v___x_303_);
if (v___x_304_ == 0)
{
lean_dec_ref(v___x_303_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_x_276_);
lean_dec_ref(v_x_275_);
goto v___jp_294_;
}
else
{
lean_object* v_arg_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_arg_305_ = lean_ctor_get(v___x_303_, 1);
lean_inc_ref(v_arg_305_);
v___x_306_ = l_Lean_Expr_appFnCleanup___redArg(v___x_303_);
v___x_307_ = l_Lean_Expr_isApp(v___x_306_);
if (v___x_307_ == 0)
{
lean_dec_ref(v___x_306_);
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_x_276_);
lean_dec_ref(v_x_275_);
goto v___jp_294_;
}
else
{
lean_object* v_arg_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_arg_308_ = lean_ctor_get(v___x_306_, 1);
lean_inc_ref(v_arg_308_);
v___x_309_ = l_Lean_Expr_appFnCleanup___redArg(v___x_306_);
v___x_310_ = l_Lean_Expr_isApp(v___x_309_);
if (v___x_310_ == 0)
{
lean_dec_ref(v___x_309_);
lean_dec_ref(v_arg_308_);
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_x_276_);
lean_dec_ref(v_x_275_);
goto v___jp_294_;
}
else
{
lean_object* v_arg_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_arg_311_ = lean_ctor_get(v___x_309_, 1);
lean_inc_ref(v_arg_311_);
v___x_312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_309_);
v___x_313_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1));
v___x_314_ = l_Lean_Expr_isConstOf(v___x_312_, v___x_313_);
lean_dec_ref(v___x_312_);
if (v___x_314_ == 0)
{
lean_dec_ref(v_arg_311_);
lean_dec_ref(v_arg_308_);
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_x_276_);
lean_dec_ref(v_x_275_);
goto v___jp_294_;
}
else
{
if (lean_obj_tag(v_x_275_) == 4)
{
lean_object* v_declName_315_; uint8_t v___x_316_; 
v_declName_315_ = lean_ctor_get(v_x_275_, 0);
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_headSyms_274_, v_declName_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec_ref_known(v_x_275_, 2);
lean_dec_ref(v_arg_311_);
lean_dec_ref(v_arg_308_);
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_x_276_);
v___x_317_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_317_, 0, v___x_316_);
lean_ctor_set_uint8(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
else
{
lean_object* v_params_319_; lean_object* v_fnApp_320_; lean_object* v_newT_321_; lean_object* v_newE_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_params_319_ = lean_array_pop(v_x_276_);
v_fnApp_320_ = l_Lean_mkAppN(v_x_275_, v_params_319_);
lean_dec_ref(v_params_319_);
lean_inc_ref(v_arg_305_);
lean_inc_ref_n(v_fnApp_320_, 2);
v_newT_321_ = l_Lean_Expr_app___override(v_fnApp_320_, v_arg_305_);
lean_inc_ref(v_arg_302_);
v_newE_322_ = l_Lean_Expr_app___override(v_fnApp_320_, v_arg_302_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_arg_308_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_newT_321_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_newE_322_);
v___x_327_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2);
lean_inc_ref(v___x_324_);
v___x_328_ = lean_array_push(v___x_327_, v___x_324_);
v___x_329_ = lean_array_push(v___x_328_, v___x_325_);
v___x_330_ = lean_array_push(v___x_329_, v___x_326_);
v___x_331_ = l_Lean_Meta_mkAppOptM(v___x_313_, v___x_330_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = l_Lean_Meta_Sym_shareCommonInc(v_a_332_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5));
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v_arg_311_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v_fnApp_320_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_arg_305_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_arg_302_);
v___x_340_ = lean_unsigned_to_nat(6u);
v___x_341_ = lean_mk_empty_array_with_capacity(v___x_340_);
v___x_342_ = lean_array_push(v___x_341_, v___x_336_);
v___x_343_ = lean_array_push(v___x_342_, v___x_323_);
v___x_344_ = lean_array_push(v___x_343_, v___x_337_);
v___x_345_ = lean_array_push(v___x_344_, v___x_324_);
v___x_346_ = lean_array_push(v___x_345_, v___x_338_);
v___x_347_ = lean_array_push(v___x_346_, v___x_339_);
v___x_348_ = l_Lean_Meta_mkAppOptM(v___x_335_, v___x_347_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_357_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_357_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_353_, 0, v_a_334_);
lean_ctor_set(v___x_353_, 1, v_a_349_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*2, v___x_293_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*2 + 1, v___x_293_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_334_);
v_a_358_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_348_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_348_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref_known(v___x_324_, 1);
lean_dec_ref(v_fnApp_320_);
lean_dec_ref(v_arg_311_);
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_302_);
v_a_366_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_333_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_333_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref_known(v___x_324_, 1);
lean_dec_ref(v_fnApp_320_);
lean_dec_ref(v_arg_311_);
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_302_);
v_a_374_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_331_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_331_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec_ref(v_arg_311_);
lean_dec_ref(v_arg_308_);
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_302_);
lean_dec_ref(v_x_276_);
lean_dec_ref(v_x_275_);
v___x_382_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_382_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_382_, 1, v___x_293_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v_x_276_);
lean_dec_ref(v_x_275_);
v___x_384_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5));
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
v___jp_294_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_295_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_295_, 1, v___x_293_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___boxed(lean_object* v_headSyms_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_386_, v_x_387_, v_x_388_, v_x_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec_ref(v_headSyms_386_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(lean_object* v_headSyms_398_, lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_dummy_410_; lean_object* v_nargs_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_dummy_410_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0);
v_nargs_411_ = l_Lean_Expr_getAppNumArgs(v_e_399_);
lean_inc(v_nargs_411_);
v___x_412_ = lean_mk_array(v_nargs_411_, v_dummy_410_);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_sub(v_nargs_411_, v___x_413_);
lean_dec(v_nargs_411_);
v___x_415_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_398_, v_e_399_, v___x_412_, v___x_414_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(lean_object* v_headSyms_416_, lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(v_headSyms_416_, v_e_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_headSyms_416_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(lean_object* v_headSyms_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_429_, v_x_430_, v_x_431_, v_x_432_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___boxed(lean_object* v_headSyms_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(v_headSyms_444_, v_x_445_, v_x_446_, v_x_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v_headSyms_444_);
return v_res_458_;
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
