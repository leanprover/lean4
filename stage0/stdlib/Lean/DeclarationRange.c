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
lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5_;
v_res_5_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2____boxed(lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v_k_10_; lean_object* v_v_11_; lean_object* v_l_12_; lean_object* v_r_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_k_10_ = lean_ctor_get(v_x_9_, 1);
v_v_11_ = lean_ctor_get(v_x_9_, 2);
v_l_12_ = lean_ctor_get(v_x_9_, 3);
v_r_13_ = lean_ctor_get(v_x_9_, 4);
v___x_14_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_8_, v_l_12_);
lean_inc(v_v_11_);
lean_inc(v_k_10_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_k_10_);
lean_ctor_set(v___x_15_, 1, v_v_11_);
v___x_16_ = lean_array_push(v___x_14_, v___x_15_);
v_init_8_ = v___x_16_;
v_x_9_ = v_r_13_;
goto _start;
}
else
{
return v_init_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_18_, v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(lean_object* v_x_25_, lean_object* v_s_26_){
_start:
{
lean_object* v___x_27_; lean_object* v_ents_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_27_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v_ents_28_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v___x_27_, v_s_26_);
v___x_29_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
lean_inc_ref(v_ents_28_);
v___x_30_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_ents_28_);
lean_ctor_set(v___x_30_, 2, v_ents_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(lean_object* v_x_31_, lean_object* v_s_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(v_x_31_, v_s_32_);
lean_dec(v_s_32_);
lean_dec_ref(v_x_31_);
return v_res_33_;
}
}
lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; 
v___f_43_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v___x_44_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v___x_45_ = ((lean_object*)(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_));
v___x_46_ = 0;
v___x_47_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_44_, v___x_45_, v___x_46_, v___f_43_);
return v___x_47_;
}
}
LEAN_EXPORT void l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_48_;
v_res_48_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(lean_object* v_init_51_, lean_object* v_t_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_51_, v_t_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_54_, lean_object* v_t_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(v_init_54_, v_t_55_);
lean_dec(v_t_55_);
return v_res_56_;
}
}
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object* v_declName_57_, lean_object* v_declRanges_58_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_60_ = l_Lean_builtinDeclRanges;
v___x_61_ = lean_st_ref_take(v___x_60_);
v___x_62_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_57_, v_declRanges_58_, v___x_61_);
v___x_63_ = lean_st_ref_put(v___x_60_, v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_addBuiltinDeclarationRanges_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_57_ = stack[0].m_obj;
lean_object* v_declRanges_58_ = stack[1].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_addBuiltinDeclarationRanges(v_declName_57_, v_declRanges_58_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDeclarationRanges___boxed(lean_object* v_declName_66_, lean_object* v_declRanges_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_addBuiltinDeclarationRanges(v_declName_66_, v_declRanges_67_);
return v_res_69_;
}
}
lean_object* l_Lean_addDeclarationRanges___redArg___lam__0(lean_object* v___x_70_, lean_object* v_declName_71_, lean_object* v_declRanges_72_, uint8_t v___x_73_, lean_object* v_env_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_70_, v_env_74_, v_declName_71_, v_declRanges_72_, v___x_73_);
return v___x_75_;
}
}
LEAN_EXPORT void l_Lean_addDeclarationRanges___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_70_ = stack[0].m_obj;
lean_object* v_declName_71_ = stack[1].m_obj;
lean_object* v_declRanges_72_ = stack[2].m_obj;
uint8_t v___x_73_ = stack[3].m_num;
lean_object* v_env_74_ = stack[4].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lean_addDeclarationRanges___redArg___lam__0(v___x_70_, v_declName_71_, v_declRanges_72_, v___x_73_, v_env_74_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__0___boxed(lean_object* v___x_77_, lean_object* v_declName_78_, lean_object* v_declRanges_79_, lean_object* v___x_80_, lean_object* v_env_81_){
_start:
{
uint8_t v___x_66__boxed_82_; lean_object* v_res_83_; 
v___x_66__boxed_82_ = lean_unbox(v___x_80_);
v_res_83_ = l_Lean_addDeclarationRanges___redArg___lam__0(v___x_77_, v_declName_78_, v_declRanges_79_, v___x_66__boxed_82_, v_env_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg___lam__1(lean_object* v___x_84_, lean_object* v_declName_85_, lean_object* v_declRanges_86_, lean_object* v_modifyEnv_87_, lean_object* v_toPure_88_, lean_object* v_____do__lift_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_90_ = l_Lean_declRangeExt;
v___x_91_ = lean_box(1);
lean_inc(v_declName_85_);
v___x_92_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_84_, v___x_90_, v_____do__lift_89_, v_declName_85_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
lean_dec(v_toPure_88_);
v___x_93_ = lean_box(v___x_92_);
v___f_94_ = lean_alloc_closure((void*)(l_Lean_addDeclarationRanges___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_94_, 0, v___x_90_);
lean_closure_set(v___f_94_, 1, v_declName_85_);
lean_closure_set(v___f_94_, 2, v_declRanges_86_);
lean_closure_set(v___f_94_, 3, v___x_93_);
v___x_95_ = lean_apply_1(v_modifyEnv_87_, v___f_94_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_modifyEnv_87_);
lean_dec_ref(v_declRanges_86_);
lean_dec(v_declName_85_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_2(v_toPure_88_, lean_box(0), v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___redArg(lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_declName_100_, lean_object* v_declRanges_101_){
_start:
{
lean_object* v_toApplicative_102_; lean_object* v_toBind_103_; lean_object* v_toPure_104_; uint8_t v___x_105_; 
v_toApplicative_102_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_102_);
v_toBind_103_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_103_);
lean_dec_ref(v_inst_98_);
v_toPure_104_ = lean_ctor_get(v_toApplicative_102_, 1);
lean_inc(v_toPure_104_);
lean_dec_ref(v_toApplicative_102_);
v___x_105_ = l_Lean_Name_isAnonymous(v_declName_100_);
if (v___x_105_ == 0)
{
lean_object* v_getEnv_106_; lean_object* v_modifyEnv_107_; lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v_getEnv_106_ = lean_ctor_get(v_inst_99_, 0);
lean_inc(v_getEnv_106_);
v_modifyEnv_107_ = lean_ctor_get(v_inst_99_, 1);
lean_inc(v_modifyEnv_107_);
lean_dec_ref(v_inst_99_);
v___x_108_ = l_Lean_instInhabitedDeclarationRanges_default;
v___f_109_ = lean_alloc_closure((void*)(l_Lean_addDeclarationRanges___redArg___lam__1), 6, 5);
lean_closure_set(v___f_109_, 0, v___x_108_);
lean_closure_set(v___f_109_, 1, v_declName_100_);
lean_closure_set(v___f_109_, 2, v_declRanges_101_);
lean_closure_set(v___f_109_, 3, v_modifyEnv_107_);
lean_closure_set(v___f_109_, 4, v_toPure_104_);
v___x_110_ = lean_apply_4(v_toBind_103_, lean_box(0), lean_box(0), v_getEnv_106_, v___f_109_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_toBind_103_);
lean_dec_ref(v_declRanges_101_);
lean_dec(v_declName_100_);
lean_dec_ref(v_inst_99_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_2(v_toPure_104_, lean_box(0), v___x_111_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges(lean_object* v_m_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_declName_116_, lean_object* v_declRanges_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_addDeclarationRanges___redArg(v_inst_114_, v_inst_115_, v_declName_116_, v_declRanges_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0(lean_object* v___x_119_, lean_object* v_____do__lift_120_, lean_object* v_declName_121_, lean_object* v_toPure_122_, lean_object* v_____do__lift_123_){
_start:
{
lean_object* v___x_124_; lean_object* v_toEnvExtension_125_; lean_object* v_asyncMode_126_; uint8_t v___x_127_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_declRangeExt;
v_toEnvExtension_125_ = lean_ctor_get(v___x_124_, 0);
v_asyncMode_126_ = lean_ctor_get(v_toEnvExtension_125_, 2);
v___x_127_ = 0;
lean_inc(v_declName_121_);
lean_inc_ref(v___x_119_);
v___x_128_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_119_, v___x_124_, v_____do__lift_120_, v_declName_121_, v_asyncMode_126_, v___x_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = 1;
v___x_130_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_119_, v___x_124_, v_____do__lift_123_, v_declName_121_, v_asyncMode_126_, v___x_129_);
v___x_131_ = lean_apply_2(v_toPure_122_, lean_box(0), v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
lean_dec_ref(v_____do__lift_123_);
lean_dec(v_declName_121_);
lean_dec_ref(v___x_119_);
v___x_132_ = lean_apply_2(v_toPure_122_, lean_box(0), v___x_128_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1(lean_object* v___x_133_, lean_object* v_declName_134_, lean_object* v_toPure_135_, lean_object* v_toBind_136_, lean_object* v_getEnv_137_, lean_object* v_____do__lift_138_){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; 
v___f_139_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_139_, 0, v___x_133_);
lean_closure_set(v___f_139_, 1, v_____do__lift_138_);
lean_closure_set(v___f_139_, 2, v_declName_134_);
lean_closure_set(v___f_139_, 3, v_toPure_135_);
v___x_140_ = lean_apply_4(v_toBind_136_, lean_box(0), lean_box(0), v_getEnv_137_, v___f_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_declName_143_){
_start:
{
lean_object* v_toApplicative_144_; lean_object* v_toBind_145_; lean_object* v_getEnv_146_; lean_object* v_toPure_147_; lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v_toApplicative_144_ = lean_ctor_get(v_inst_141_, 0);
lean_inc_ref(v_toApplicative_144_);
v_toBind_145_ = lean_ctor_get(v_inst_141_, 1);
lean_inc_n(v_toBind_145_, 2);
lean_dec_ref(v_inst_141_);
v_getEnv_146_ = lean_ctor_get(v_inst_142_, 0);
lean_inc_n(v_getEnv_146_, 2);
lean_dec_ref(v_inst_142_);
v_toPure_147_ = lean_ctor_get(v_toApplicative_144_, 1);
lean_inc(v_toPure_147_);
lean_dec_ref(v_toApplicative_144_);
v___x_148_ = l_Lean_instInhabitedDeclarationRanges_default;
v___f_149_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1), 6, 5);
lean_closure_set(v___f_149_, 0, v___x_148_);
lean_closure_set(v___f_149_, 1, v_declName_143_);
lean_closure_set(v___f_149_, 2, v_toPure_147_);
lean_closure_set(v___f_149_, 3, v_toBind_145_);
lean_closure_set(v___f_149_, 4, v_getEnv_146_);
v___x_150_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v_getEnv_146_, v___f_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f(lean_object* v_m_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_declName_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_152_, v_inst_153_, v_declName_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__0(lean_object* v_declName_156_, lean_object* v_toPure_157_, lean_object* v_____do__lift_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_____do__lift_158_, v_declName_156_);
v___x_160_ = lean_apply_2(v_toPure_157_, lean_box(0), v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed(lean_object* v_declName_161_, lean_object* v_toPure_162_, lean_object* v_____do__lift_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__0(v_declName_161_, v_toPure_162_, v_____do__lift_163_);
lean_dec(v_____do__lift_163_);
lean_dec(v_declName_161_);
return v_res_164_;
}
}
lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__1(lean_object* v___x_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_st_ref_get(v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Lean_findDeclarationRanges_x3f___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_165_ = stack[0].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__1(v___x_165_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed(lean_object* v___x_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__1(v___x_169_);
lean_dec(v___x_169_);
return v_res_171_;
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___f_173_; 
v___x_172_ = l_Lean_builtinDeclRanges;
v___f_173_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_173_, 0, v___x_172_);
return v___f_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__2(lean_object* v_inst_174_, lean_object* v_toBind_175_, lean_object* v___f_176_, lean_object* v_toPure_177_, lean_object* v_ranges_178_){
_start:
{
if (lean_obj_tag(v_ranges_178_) == 0)
{
lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_toPure_177_);
v___f_179_ = lean_obj_once(&l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0, &l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0_once, _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0);
v___x_180_ = lean_apply_2(v_inst_174_, lean_box(0), v___f_179_);
v___x_181_ = lean_apply_4(v_toBind_175_, lean_box(0), lean_box(0), v___x_180_, v___f_176_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
lean_dec(v___f_176_);
lean_dec(v_toBind_175_);
lean_dec(v_inst_174_);
v___x_182_ = lean_apply_2(v_toPure_177_, lean_box(0), v_ranges_178_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__3(lean_object* v___f_183_, lean_object* v_ranges_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_apply_1(v___f_183_, v_ranges_184_);
return v___x_185_;
}
}
lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__5(lean_object* v_declName_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_toBind_189_, lean_object* v___f_190_, lean_object* v___f_191_, lean_object* v_env_192_, uint8_t v_____do__lift_193_){
_start:
{
uint8_t v___y_199_; uint8_t v___x_202_; 
lean_inc(v_declName_186_);
lean_inc_ref(v_env_192_);
v___x_202_ = l_Lean_isAuxRecursor(v_env_192_, v_declName_186_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; 
lean_inc(v_declName_186_);
v___x_203_ = l_Lean_isNoConfusion(v_env_192_, v_declName_186_);
v___y_199_ = v___x_203_;
goto v___jp_198_;
}
else
{
lean_dec_ref(v_env_192_);
v___y_199_ = v___x_202_;
goto v___jp_198_;
}
v___jp_194_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = l_Lean_Name_getPrefix(v_declName_186_);
lean_dec(v_declName_186_);
v___x_196_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_187_, v_inst_188_, v___x_195_);
v___x_197_ = lean_apply_4(v_toBind_189_, lean_box(0), lean_box(0), v___x_196_, v___f_190_);
return v___x_197_;
}
v___jp_198_:
{
if (v___y_199_ == 0)
{
if (v_____do__lift_193_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v___f_190_);
v___x_200_ = l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_187_, v_inst_188_, v_declName_186_);
v___x_201_ = lean_apply_4(v_toBind_189_, lean_box(0), lean_box(0), v___x_200_, v___f_191_);
return v___x_201_;
}
else
{
lean_dec(v___f_191_);
goto v___jp_194_;
}
}
else
{
lean_dec(v___f_191_);
goto v___jp_194_;
}
}
}
}
LEAN_EXPORT void l_Lean_findDeclarationRanges_x3f___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_186_ = stack[0].m_obj;
lean_object* v_inst_187_ = stack[1].m_obj;
lean_object* v_inst_188_ = stack[2].m_obj;
lean_object* v_toBind_189_ = stack[3].m_obj;
lean_object* v___f_190_ = stack[4].m_obj;
lean_object* v___f_191_ = stack[5].m_obj;
lean_object* v_env_192_ = stack[6].m_obj;
uint8_t v_____do__lift_193_ = stack[7].m_num;
lean_object* v_res_204_;
v_res_204_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__5(v_declName_186_, v_inst_187_, v_inst_188_, v_toBind_189_, v___f_190_, v___f_191_, v_env_192_, v_____do__lift_193_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed(lean_object* v_declName_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_toBind_208_, lean_object* v___f_209_, lean_object* v___f_210_, lean_object* v_env_211_, lean_object* v_____do__lift_212_){
_start:
{
uint8_t v_____do__lift_270__boxed_213_; lean_object* v_res_214_; 
v_____do__lift_270__boxed_213_ = lean_unbox(v_____do__lift_212_);
v_res_214_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__5(v_declName_205_, v_inst_206_, v_inst_207_, v_toBind_208_, v___f_209_, v___f_210_, v_env_211_, v_____do__lift_270__boxed_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg___lam__4(lean_object* v_declName_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_toBind_218_, lean_object* v___f_219_, lean_object* v___f_220_, lean_object* v_env_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_inc(v_toBind_218_);
lean_inc_ref(v_inst_217_);
lean_inc_ref(v_inst_216_);
lean_inc(v_declName_215_);
v___f_222_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_222_, 0, v_declName_215_);
lean_closure_set(v___f_222_, 1, v_inst_216_);
lean_closure_set(v___f_222_, 2, v_inst_217_);
lean_closure_set(v___f_222_, 3, v_toBind_218_);
lean_closure_set(v___f_222_, 4, v___f_219_);
lean_closure_set(v___f_222_, 5, v___f_220_);
lean_closure_set(v___f_222_, 6, v_env_221_);
v___x_223_ = l_Lean_isRec___redArg(v_inst_216_, v_inst_217_, v_declName_215_);
v___x_224_ = lean_apply_4(v_toBind_218_, lean_box(0), lean_box(0), v___x_223_, v___f_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___redArg(lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_declName_228_){
_start:
{
lean_object* v_toApplicative_229_; lean_object* v_toBind_230_; lean_object* v_getEnv_231_; lean_object* v_toPure_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___x_237_; 
v_toApplicative_229_ = lean_ctor_get(v_inst_225_, 0);
v_toBind_230_ = lean_ctor_get(v_inst_225_, 1);
lean_inc_n(v_toBind_230_, 3);
v_getEnv_231_ = lean_ctor_get(v_inst_226_, 0);
lean_inc(v_getEnv_231_);
v_toPure_232_ = lean_ctor_get(v_toApplicative_229_, 1);
lean_inc_n(v_toPure_232_, 2);
lean_inc(v_declName_228_);
v___f_233_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_233_, 0, v_declName_228_);
lean_closure_set(v___f_233_, 1, v_toPure_232_);
v___f_234_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__2), 5, 4);
lean_closure_set(v___f_234_, 0, v_inst_227_);
lean_closure_set(v___f_234_, 1, v_toBind_230_);
lean_closure_set(v___f_234_, 2, v___f_233_);
lean_closure_set(v___f_234_, 3, v_toPure_232_);
v___f_235_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_235_, 0, v___f_234_);
lean_inc_ref(v___f_235_);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___redArg___lam__4), 7, 6);
lean_closure_set(v___f_236_, 0, v_declName_228_);
lean_closure_set(v___f_236_, 1, v_inst_225_);
lean_closure_set(v___f_236_, 2, v_inst_226_);
lean_closure_set(v___f_236_, 3, v_toBind_230_);
lean_closure_set(v___f_236_, 4, v___f_235_);
lean_closure_set(v___f_236_, 5, v___f_235_);
v___x_237_ = lean_apply_4(v_toBind_230_, lean_box(0), lean_box(0), v_getEnv_231_, v___f_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f(lean_object* v_m_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_declName_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_findDeclarationRanges_x3f___redArg(v_inst_239_, v_inst_240_, v_inst_241_, v_declName_242_);
return v___x_243_;
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
