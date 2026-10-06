// Lean compiler output
// Module: Lean.DeclarationRange
// Imports: public import Lean.MonadEnv
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_isRec___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_builtinDeclRanges;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declRangeExt"};
static const lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(6, 115, 220, 233, 41, 110, 120, 18)}};
static const lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_declRangeExt;
LEAN_EXPORT lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addBuiltinDeclarationRanges___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_box(1);
v___x_3_ = lean_st_mk_ref(v___x_2_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2____boxed(lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_object* v_k_9_; lean_object* v_v_10_; lean_object* v_l_11_; lean_object* v_r_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_k_9_ = lean_ctor_get(v_x_8_, 1);
v_v_10_ = lean_ctor_get(v_x_8_, 2);
v_l_11_ = lean_ctor_get(v_x_8_, 3);
v_r_12_ = lean_ctor_get(v_x_8_, 4);
v___x_13_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_7_, v_l_11_);
lean_inc(v_v_10_);
lean_inc(v_k_9_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_k_9_);
lean_ctor_set(v___x_14_, 1, v_v_10_);
v___x_15_ = lean_array_push(v___x_13_, v___x_14_);
v_init_7_ = v___x_15_;
v_x_8_ = v_r_12_;
goto _start;
}
else
{
return v_init_7_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_17_, v_x_18_);
lean_dec(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(lean_object* v_x_24_, lean_object* v_s_25_){
_start:
{
lean_object* v___x_26_; lean_object* v_ents_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_26_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v_ents_27_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v___x_26_, v_s_25_);
v___x_28_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
lean_inc_ref(v_ents_27_);
v___x_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v_ents_27_);
lean_ctor_set(v___x_29_, 2, v_ents_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(lean_object* v_x_30_, lean_object* v_s_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(v_x_30_, v_s_31_);
lean_dec(v_s_31_);
lean_dec_ref(v_x_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; lean_object* v___x_46_; 
v___f_42_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v___x_43_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v___x_44_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v___x_45_ = 0;
v___x_46_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_43_, v___x_44_, v___x_45_, v___f_42_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(lean_object* v_init_49_, lean_object* v_t_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_49_, v_t_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_52_, lean_object* v_t_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(v_init_52_, v_t_53_);
lean_dec(v_t_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object* v_declName_55_, lean_object* v_declRanges_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_58_ = l_Lean_builtinDeclRanges;
v___x_59_ = lean_st_ref_take(v___x_58_);
v___x_60_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_55_, v_declRanges_56_, v___x_59_);
v___x_61_ = lean_st_ref_put(v___x_58_, v___x_60_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDeclarationRanges___boxed(lean_object* v_declName_63_, lean_object* v_declRanges_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_addBuiltinDeclarationRanges(v_declName_63_, v_declRanges_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__0(lean_object* v___x_67_, lean_object* v_declName_68_, lean_object* v_declRanges_69_, uint8_t v___x_70_, lean_object* v_env_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_67_, v_env_71_, v_declName_68_, v_declRanges_69_, v___x_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__0___boxed(lean_object* v___x_73_, lean_object* v_declName_74_, lean_object* v_declRanges_75_, lean_object* v___x_76_, lean_object* v_env_77_){
_start:
{
uint8_t v___x_66__boxed_78_; lean_object* v_res_79_; 
v___x_66__boxed_78_ = lean_unbox(v___x_76_);
v_res_79_ = l_Lean_addDeclarationRanges___redArg___lam__0(v___x_73_, v_declName_74_, v_declRanges_75_, v___x_66__boxed_78_, v_env_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__1(lean_object* v___x_80_, lean_object* v_declName_81_, lean_object* v_declRanges_82_, lean_object* v_modifyEnv_83_, lean_object* v_toPure_84_, lean_object* v_____do__lift_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = l_Lean_declRangeExt;
v___x_87_ = lean_box(1);
lean_inc(v_declName_81_);
v___x_88_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_80_, v___x_86_, v_____do__lift_85_, v_declName_81_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___f_90_; lean_object* v___x_91_; 
lean_dec(v_toPure_84_);
v___x_89_ = lean_box(v___x_88_);
v___f_90_ = lean_alloc_closure((void*)(l_Lean_addDeclarationRanges___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_90_, 0, v___x_86_);
lean_closure_set(v___f_90_, 1, v_declName_81_);
lean_closure_set(v___f_90_, 2, v_declRanges_82_);
lean_closure_set(v___f_90_, 3, v___x_89_);
v___x_91_ = lean_apply_1(v_modifyEnv_83_, v___f_90_);
return v___x_91_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_modifyEnv_83_);
lean_dec_ref(v_declRanges_82_);
lean_dec(v_declName_81_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_2(v_toPure_84_, lean_box(0), v___x_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg(lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_declName_96_, lean_object* v_declRanges_97_){
_start:
{
lean_object* v_toApplicative_98_; lean_object* v_toBind_99_; lean_object* v_toPure_100_; uint8_t v___x_101_; 
v_toApplicative_98_ = lean_ctor_get(v_inst_94_, 0);
lean_inc_ref(v_toApplicative_98_);
v_toBind_99_ = lean_ctor_get(v_inst_94_, 1);
lean_inc(v_toBind_99_);
lean_dec_ref(v_inst_94_);
v_toPure_100_ = lean_ctor_get(v_toApplicative_98_, 1);
lean_inc(v_toPure_100_);
lean_dec_ref(v_toApplicative_98_);
v___x_101_ = l_Lean_Name_isAnonymous(v_declName_96_);
if (v___x_101_ == 0)
{
lean_object* v_getEnv_102_; lean_object* v_modifyEnv_103_; lean_object* v___x_104_; lean_object* v___f_105_; lean_object* v___x_106_; 
v_getEnv_102_ = lean_ctor_get(v_inst_95_, 0);
lean_inc(v_getEnv_102_);
v_modifyEnv_103_ = lean_ctor_get(v_inst_95_, 1);
lean_inc(v_modifyEnv_103_);
lean_dec_ref(v_inst_95_);
v___x_104_ = l_Lean_instInhabitedDeclarationRanges_default;
v___f_105_ = lean_alloc_closure((void*)(l_Lean_addDeclarationRanges___redArg___lam__1), 6, 5);
lean_closure_set(v___f_105_, 0, v___x_104_);
lean_closure_set(v___f_105_, 1, v_declName_96_);
lean_closure_set(v___f_105_, 2, v_declRanges_97_);
lean_closure_set(v___f_105_, 3, v_modifyEnv_103_);
lean_closure_set(v___f_105_, 4, v_toPure_100_);
v___x_106_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v_getEnv_102_, v___f_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_toBind_99_);
lean_dec_ref(v_declRanges_97_);
lean_dec(v_declName_96_);
lean_dec_ref(v_inst_95_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges(lean_object* v_m_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_declName_112_, lean_object* v_declRanges_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_addDeclarationRanges___redArg(v_inst_110_, v_inst_111_, v_declName_112_, v_declRanges_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0(lean_object* v___x_115_, lean_object* v_____do__lift_116_, lean_object* v_declName_117_, lean_object* v_toPure_118_, lean_object* v_____do__lift_119_){
_start:
{
lean_object* v___x_120_; lean_object* v_toEnvExtension_121_; lean_object* v_asyncMode_122_; uint8_t v___x_123_; lean_object* v___x_124_; 
v___x_120_ = l_Lean_declRangeExt;
v_toEnvExtension_121_ = lean_ctor_get(v___x_120_, 0);
v_asyncMode_122_ = lean_ctor_get(v_toEnvExtension_121_, 2);
v___x_123_ = 0;
lean_inc(v_declName_117_);
lean_inc_ref(v___x_115_);
v___x_124_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_115_, v___x_120_, v_____do__lift_116_, v_declName_117_, v_asyncMode_122_, v___x_123_);
if (lean_obj_tag(v___x_124_) == 0)
{
uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = 1;
v___x_126_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_115_, v___x_120_, v_____do__lift_119_, v_declName_117_, v_asyncMode_122_, v___x_125_);
v___x_127_ = lean_apply_2(v_toPure_118_, lean_box(0), v___x_126_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; 
lean_dec_ref(v_____do__lift_119_);
lean_dec(v_declName_117_);
lean_dec_ref(v___x_115_);
v___x_128_ = lean_apply_2(v_toPure_118_, lean_box(0), v___x_124_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1(lean_object* v___x_129_, lean_object* v_declName_130_, lean_object* v_toPure_131_, lean_object* v_toBind_132_, lean_object* v_getEnv_133_, lean_object* v_____do__lift_134_){
_start:
{
lean_object* v___f_135_; lean_object* v___x_136_; 
v___f_135_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_135_, 0, v___x_129_);
lean_closure_set(v___f_135_, 1, v_____do__lift_134_);
lean_closure_set(v___f_135_, 2, v_declName_130_);
lean_closure_set(v___f_135_, 3, v_toPure_131_);
v___x_136_ = lean_apply_4(v_toBind_132_, lean_box(0), lean_box(0), v_getEnv_133_, v___f_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg(lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_declName_139_){
_start:
{
lean_object* v_toApplicative_140_; lean_object* v_toBind_141_; lean_object* v_getEnv_142_; lean_object* v_toPure_143_; lean_object* v___x_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v_toApplicative_140_ = lean_ctor_get(v_inst_137_, 0);
lean_inc_ref(v_toApplicative_140_);
v_toBind_141_ = lean_ctor_get(v_inst_137_, 1);
lean_inc_n(v_toBind_141_, 2);
lean_dec_ref(v_inst_137_);
v_getEnv_142_ = lean_ctor_get(v_inst_138_, 0);
lean_inc_n(v_getEnv_142_, 2);
lean_dec_ref(v_inst_138_);
v_toPure_143_ = lean_ctor_get(v_toApplicative_140_, 1);
lean_inc(v_toPure_143_);
lean_dec_ref(v_toApplicative_140_);
v___x_144_ = l_Lean_instInhabitedDeclarationRanges_default;
v___f_145_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1), 6, 5);
lean_closure_set(v___f_145_, 0, v___x_144_);
lean_closure_set(v___f_145_, 1, v_declName_139_);
lean_closure_set(v___f_145_, 2, v_toPure_143_);
lean_closure_set(v___f_145_, 3, v_toBind_141_);
lean_closure_set(v___f_145_, 4, v_getEnv_142_);
v___x_146_ = lean_apply_4(v_toBind_141_, lean_box(0), lean_box(0), v_getEnv_142_, v___f_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f(lean_object* v_m_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_declName_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_148_, v_inst_149_, v_declName_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__0(lean_object* v_declName_152_, lean_object* v_toPure_153_, lean_object* v_____do__lift_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_____do__lift_154_, v_declName_152_);
v___x_156_ = lean_apply_2(v_toPure_153_, lean_box(0), v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed(lean_object* v_declName_157_, lean_object* v_toPure_158_, lean_object* v_____do__lift_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__0(v_declName_157_, v_toPure_158_, v_____do__lift_159_);
lean_dec(v_____do__lift_159_);
lean_dec(v_declName_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__1(lean_object* v___x_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_st_ref_get(v___x_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed(lean_object* v___x_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__1(v___x_164_);
lean_dec(v___x_164_);
return v_res_166_;
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_167_; lean_object* v___f_168_; 
v___x_167_ = l_Lean_builtinDeclRanges;
v___f_168_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_168_, 0, v___x_167_);
return v___f_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__2(lean_object* v_inst_169_, lean_object* v_toBind_170_, lean_object* v___f_171_, lean_object* v_toPure_172_, lean_object* v_ranges_173_){
_start:
{
if (lean_obj_tag(v_ranges_173_) == 0)
{
lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_toPure_172_);
v___f_174_ = lean_obj_once(&l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0, &l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0_once, _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0);
v___x_175_ = lean_apply_2(v_inst_169_, lean_box(0), v___f_174_);
v___x_176_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_175_, v___f_171_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; 
lean_dec(v___f_171_);
lean_dec(v_toBind_170_);
lean_dec(v_inst_169_);
v___x_177_ = lean_apply_2(v_toPure_172_, lean_box(0), v_ranges_173_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__3(lean_object* v___f_178_, lean_object* v_ranges_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_apply_1(v___f_178_, v_ranges_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__5(lean_object* v_declName_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_toBind_184_, lean_object* v___f_185_, lean_object* v___f_186_, lean_object* v_env_187_, uint8_t v_____do__lift_188_){
_start:
{
uint8_t v___y_194_; uint8_t v___x_197_; 
lean_inc(v_declName_181_);
lean_inc_ref(v_env_187_);
v___x_197_ = l_Lean_isAuxRecursor(v_env_187_, v_declName_181_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
lean_inc(v_declName_181_);
v___x_198_ = l_Lean_isNoConfusion(v_env_187_, v_declName_181_);
v___y_194_ = v___x_198_;
goto v___jp_193_;
}
else
{
lean_dec_ref(v_env_187_);
v___y_194_ = v___x_197_;
goto v___jp_193_;
}
v___jp_189_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = l_Lean_Name_getPrefix(v_declName_181_);
lean_dec(v_declName_181_);
v___x_191_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_182_, v_inst_183_, v___x_190_);
v___x_192_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_191_, v___f_185_);
return v___x_192_;
}
v___jp_193_:
{
if (v___y_194_ == 0)
{
if (v_____do__lift_188_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___f_185_);
v___x_195_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_182_, v_inst_183_, v_declName_181_);
v___x_196_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_195_, v___f_186_);
return v___x_196_;
}
else
{
lean_dec(v___f_186_);
goto v___jp_189_;
}
}
else
{
lean_dec(v___f_186_);
goto v___jp_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed(lean_object* v_declName_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_toBind_202_, lean_object* v___f_203_, lean_object* v___f_204_, lean_object* v_env_205_, lean_object* v_____do__lift_206_){
_start:
{
uint8_t v_____do__lift_251__boxed_207_; lean_object* v_res_208_; 
v_____do__lift_251__boxed_207_ = lean_unbox(v_____do__lift_206_);
v_res_208_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__5(v_declName_199_, v_inst_200_, v_inst_201_, v_toBind_202_, v___f_203_, v___f_204_, v_env_205_, v_____do__lift_251__boxed_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__4(lean_object* v_declName_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_toBind_212_, lean_object* v___f_213_, lean_object* v___f_214_, lean_object* v_env_215_){
_start:
{
lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_inc(v_toBind_212_);
lean_inc_ref(v_inst_211_);
lean_inc_ref(v_inst_210_);
lean_inc(v_declName_209_);
v___f_216_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_216_, 0, v_declName_209_);
lean_closure_set(v___f_216_, 1, v_inst_210_);
lean_closure_set(v___f_216_, 2, v_inst_211_);
lean_closure_set(v___f_216_, 3, v_toBind_212_);
lean_closure_set(v___f_216_, 4, v___f_213_);
lean_closure_set(v___f_216_, 5, v___f_214_);
lean_closure_set(v___f_216_, 6, v_env_215_);
v___x_217_ = l_Lean_isRec___redArg(v_inst_210_, v_inst_211_, v_declName_209_);
v___x_218_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_217_, v___f_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_declName_222_){
_start:
{
lean_object* v_toApplicative_223_; lean_object* v_toBind_224_; lean_object* v_getEnv_225_; lean_object* v_toPure_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___x_231_; 
v_toApplicative_223_ = lean_ctor_get(v_inst_219_, 0);
v_toBind_224_ = lean_ctor_get(v_inst_219_, 1);
lean_inc_n(v_toBind_224_, 3);
v_getEnv_225_ = lean_ctor_get(v_inst_220_, 0);
lean_inc(v_getEnv_225_);
v_toPure_226_ = lean_ctor_get(v_toApplicative_223_, 1);
lean_inc_n(v_toPure_226_, 2);
lean_inc(v_declName_222_);
v___f_227_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_227_, 0, v_declName_222_);
lean_closure_set(v___f_227_, 1, v_toPure_226_);
v___f_228_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__2), 5, 4);
lean_closure_set(v___f_228_, 0, v_inst_221_);
lean_closure_set(v___f_228_, 1, v_toBind_224_);
lean_closure_set(v___f_228_, 2, v___f_227_);
lean_closure_set(v___f_228_, 3, v_toPure_226_);
v___f_229_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_229_, 0, v___f_228_);
lean_inc_ref(v___f_229_);
v___f_230_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__4), 7, 6);
lean_closure_set(v___f_230_, 0, v_declName_222_);
lean_closure_set(v___f_230_, 1, v_inst_219_);
lean_closure_set(v___f_230_, 2, v_inst_220_);
lean_closure_set(v___f_230_, 3, v_toBind_224_);
lean_closure_set(v___f_230_, 4, v___f_229_);
lean_closure_set(v___f_230_, 5, v___f_229_);
v___x_231_ = lean_apply_4(v_toBind_224_, lean_box(0), lean_box(0), v_getEnv_225_, v___f_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f(lean_object* v_m_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_declName_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_findDeclarationRanges_x3f___redArg(v_inst_233_, v_inst_234_, v_inst_235_, v_declName_236_);
return v___x_237_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_builtinDeclRanges = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_builtinDeclRanges);
lean_dec_ref(res);
res = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_declRangeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_declRangeExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DeclarationRange(builtin);
}
#ifdef __cplusplus
}
#endif
