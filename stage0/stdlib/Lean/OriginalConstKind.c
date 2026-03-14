// Lean compiler output
// Module: Lean.OriginalConstKind
// Imports: public import Lean.Environment import Lean.EnvExtension
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "OriginalConstKind"};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 35, 30, 26, 3, 124, 68, 19)}};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(47, 229, 144, 138, 87, 216, 24, 80)}};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 180, 73, 87, 233, 249, 201, 103)}};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "privateConstKindsExt"};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 164, 33, 147, 211, 59, 75, 212)}};
static const lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
LEAN_EXPORT lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_wasOriginallyDefn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_wasOriginallyDefn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_wasOriginallyTheorem___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_k_3_ = lean_ctor_get(v_x_2_, 1);
v_v_4_ = lean_ctor_get(v_x_2_, 2);
v_l_5_ = lean_ctor_get(v_x_2_, 3);
v_r_6_ = lean_ctor_get(v_x_2_, 4);
v___x_7_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v_init_1_, v_l_5_);
lean_inc(v_v_4_);
lean_inc(v_k_3_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_k_3_);
lean_ctor_set(v___x_8_, 1, v_v_4_);
v___x_9_ = lean_array_push(v___x_7_, v___x_8_);
v_init_1_ = v___x_9_;
v_x_2_ = v_r_6_;
goto _start;
}
else
{
return v_init_1_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v_init_11_, v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(lean_object* v_env_14_, lean_object* v_as_15_, size_t v_i_16_, size_t v_stop_17_, lean_object* v_b_18_){
_start:
{
lean_object* v___y_20_; uint8_t v___x_24_; 
v___x_24_ = lean_usize_dec_eq(v_i_16_, v_stop_17_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v_fst_26_; uint8_t v___x_27_; 
v___x_25_ = lean_array_uget_borrowed(v_as_15_, v_i_16_);
v_fst_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_fst_26_);
lean_inc_ref(v_env_14_);
v___x_27_ = l_Lean_Environment_contains(v_env_14_, v_fst_26_, v___x_24_);
if (v___x_27_ == 0)
{
v___y_20_ = v_b_18_;
goto v___jp_19_;
}
else
{
lean_object* v___x_28_; 
lean_inc(v___x_25_);
v___x_28_ = lean_array_push(v_b_18_, v___x_25_);
v___y_20_ = v___x_28_;
goto v___jp_19_;
}
}
else
{
lean_dec_ref(v_env_14_);
return v_b_18_;
}
v___jp_19_:
{
size_t v___x_21_; size_t v___x_22_; 
v___x_21_ = ((size_t)1ULL);
v___x_22_ = lean_usize_add(v_i_16_, v___x_21_);
v_i_16_ = v___x_22_;
v_b_18_ = v___y_20_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_29_, lean_object* v_as_30_, lean_object* v_i_31_, lean_object* v_stop_32_, lean_object* v_b_33_){
_start:
{
size_t v_i_boxed_34_; size_t v_stop_boxed_35_; lean_object* v_res_36_; 
v_i_boxed_34_ = lean_unbox_usize(v_i_31_);
lean_dec(v_i_31_);
v_stop_boxed_35_ = lean_unbox_usize(v_stop_32_);
lean_dec(v_stop_32_);
v_res_36_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(v_env_29_, v_as_30_, v_i_boxed_34_, v_stop_boxed_35_, v_b_33_);
lean_dec_ref(v_as_30_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_(lean_object* v___x_37_, lean_object* v_env_38_, lean_object* v_s_39_, uint8_t v_x_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_41_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_42_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v___x_41_, v_s_39_);
v___x_43_ = lean_array_get_size(v___x_42_);
v___x_44_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_45_ = lean_nat_dec_lt(v___x_37_, v___x_43_);
if (v___x_45_ == 0)
{
lean_dec_ref(v___x_42_);
lean_dec_ref(v_env_38_);
return v___x_44_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = lean_nat_dec_le(v___x_43_, v___x_43_);
if (v___x_46_ == 0)
{
if (v___x_45_ == 0)
{
lean_dec_ref(v___x_42_);
lean_dec_ref(v_env_38_);
return v___x_44_;
}
else
{
size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; 
v___x_47_ = ((size_t)0ULL);
v___x_48_ = lean_usize_of_nat(v___x_43_);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(v_env_38_, v___x_42_, v___x_47_, v___x_48_, v___x_44_);
lean_dec_ref(v___x_42_);
return v___x_49_;
}
}
else
{
size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((size_t)0ULL);
v___x_51_ = lean_usize_of_nat(v___x_43_);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(v_env_38_, v___x_42_, v___x_50_, v___x_51_, v___x_44_);
lean_dec_ref(v___x_42_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed(lean_object* v___x_53_, lean_object* v_env_54_, lean_object* v_s_55_, lean_object* v_x_56_){
_start:
{
uint8_t v_x_416__boxed_57_; lean_object* v_res_58_; 
v_x_416__boxed_57_ = lean_unbox(v_x_56_);
v_res_58_ = l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_(v___x_53_, v_env_54_, v_s_55_, v_x_416__boxed_57_);
lean_dec(v_s_55_);
lean_dec(v___x_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___f_84_ = ((lean_object*)(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_));
v___x_85_ = ((lean_object*)(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_));
v___x_86_ = lean_box(0);
v___x_87_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_85_, v___x_86_, v___f_84_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_();
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0(lean_object* v_init_90_, lean_object* v_t_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v_init_90_, v_t_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_93_, lean_object* v_t_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0(v_init_93_, v_t_94_);
lean_dec(v_t_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOriginalConstKind_x3f(lean_object* v_env_96_, lean_object* v_declName_97_){
_start:
{
uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_98_ = 0;
v___x_99_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_100_ = lean_box(1);
v___x_101_ = 0;
v___x_102_ = lean_box(v___x_98_);
lean_inc(v_declName_97_);
lean_inc_ref(v_env_96_);
v___x_103_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_102_, v___x_99_, v_env_96_, v_declName_97_, v___x_100_, v___x_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = 0;
v___x_105_ = l_Lean_Environment_setExporting(v_env_96_, v___x_104_);
v___x_106_ = l_Lean_Environment_findAsync_x3f(v___x_105_, v_declName_97_, v___x_104_);
if (lean_obj_tag(v___x_106_) == 0)
{
return v___x_103_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_116_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_116_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v_kind_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v_kind_111_ = lean_ctor_get_uint8(v_val_107_, sizeof(void*)*3);
lean_dec(v_val_107_);
v___x_112_ = lean_box(v_kind_111_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_112_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
else
{
lean_dec(v_declName_97_);
lean_dec_ref(v_env_96_);
return v___x_103_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_wasOriginallyDefn(lean_object* v_env_117_, lean_object* v_declName_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_getOriginalConstKind_x3f(v_env_117_, v_declName_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
else
{
lean_object* v_val_121_; uint8_t v___x_122_; 
v_val_121_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_121_);
lean_dec_ref(v___x_119_);
v___x_122_ = lean_unbox(v_val_121_);
lean_dec(v_val_121_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 1;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_wasOriginallyDefn___boxed(lean_object* v_env_125_, lean_object* v_declName_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_wasOriginallyDefn(v_env_125_, v_declName_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_wasOriginallyTheorem(lean_object* v_env_129_, lean_object* v_declName_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_getOriginalConstKind_x3f(v_env_129_, v_declName_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
else
{
lean_object* v_val_133_; uint8_t v___x_134_; 
v_val_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_val_133_);
lean_dec_ref(v___x_131_);
v___x_134_ = lean_unbox(v_val_133_);
lean_dec(v_val_133_);
if (v___x_134_ == 1)
{
uint8_t v___x_135_; 
v___x_135_ = 1;
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_wasOriginallyTheorem___boxed(lean_object* v_env_137_, lean_object* v_declName_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_wasOriginallyTheorem(v_env_137_, v_declName_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_OriginalConstKind(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_OriginalConstKind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_OriginalConstKind(builtin);
}
#ifdef __cplusplus
}
#endif
