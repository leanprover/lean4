// Lean compiler output
// Module: Lean.Meta.ProdN
// Imports: public import Lean.Meta.InferType import Lean.Meta.DecLevel import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkProdN___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Lean_Meta_mkProdN___closed__0 = (const lean_object*)&l_Lean_Meta_mkProdN___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkProdN___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkProdN___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_object* l_Lean_Meta_mkProdN___closed__1 = (const lean_object*)&l_Lean_Meta_mkProdN___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkProdMkN___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_mkProdMkN___closed__0 = (const lean_object*)&l_Lean_Meta_mkProdMkN___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkProdMkN___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkProdN___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l_Lean_Meta_mkProdMkN___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkProdMkN___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkProdMkN___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l_Lean_Meta_mkProdMkN___closed__1 = (const lean_object*)&l_Lean_Meta_mkProdMkN___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdMkN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdMkN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getProdFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Internal error: Expected Prod, got "};
static const lean_object* l_Lean_Meta_getProdFields___closed__0 = (const lean_object*)&l_Lean_Meta_getProdFields___closed__0_value;
static lean_once_cell_t l_Lean_Meta_getProdFields___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getProdFields___closed__1;
static const lean_string_object l_Lean_Meta_getProdFields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " of type "};
static const lean_object* l_Lean_Meta_getProdFields___closed__2 = (const lean_object*)&l_Lean_Meta_getProdFields___closed__2_value;
static lean_once_cell_t l_Lean_Meta_getProdFields___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getProdFields___closed__3;
static const lean_string_object l_Lean_Meta_getProdFields___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Meta_getProdFields___closed__4 = (const lean_object*)&l_Lean_Meta_getProdFields___closed__4_value;
static const lean_ctor_object l_Lean_Meta_getProdFields___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Meta_getProdFields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getProdFields___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_getProdFields___closed__4_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Meta_getProdFields___closed__5 = (const lean_object*)&l_Lean_Meta_getProdFields___closed__5_value;
static const lean_string_object l_Lean_Meta_getProdFields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "snd"};
static const lean_object* l_Lean_Meta_getProdFields___closed__6 = (const lean_object*)&l_Lean_Meta_getProdFields___closed__6_value;
static const lean_ctor_object l_Lean_Meta_getProdFields___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Meta_getProdFields___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getProdFields___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_getProdFields___closed__6_value),LEAN_SCALAR_PTR_LITERAL(35, 40, 163, 84, 60, 49, 151, 224)}};
static const lean_object* l_Lean_Meta_getProdFields___closed__7 = (const lean_object*)&l_Lean_Meta_getProdFields___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getProdFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getProdFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(lean_object* v_upperBound_4_, lean_object* v_a_5_, lean_object* v_b_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_lt(v_a_5_, v_upperBound_4_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v_a_5_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v_b_6_);
return v___x_13_;
}
else
{
lean_object* v_snd_14_; lean_object* v_fst_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_57_; 
v_snd_14_ = lean_ctor_get(v_b_6_, 1);
v_fst_15_ = lean_ctor_get(v_b_6_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_b_6_);
if (v_isSharedCheck_57_ == 0)
{
v___x_17_ = v_b_6_;
v_isShared_18_ = v_isSharedCheck_57_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_snd_14_);
lean_inc(v_fst_15_);
lean_dec(v_b_6_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_57_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_fst_19_; lean_object* v_snd_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_56_; 
v_fst_19_ = lean_ctor_get(v_snd_14_, 0);
v_snd_20_ = lean_ctor_get(v_snd_14_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v_snd_14_);
if (v_isSharedCheck_56_ == 0)
{
v___x_22_ = v_snd_14_;
v_isShared_23_ = v_isSharedCheck_56_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_snd_20_);
lean_inc(v_fst_19_);
lean_dec(v_snd_14_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_56_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_24_ = l_Lean_instInhabitedExpr;
v___x_25_ = lean_array_get_size(v_snd_20_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_sub(v___x_25_, v___x_26_);
v___x_28_ = lean_array_get_borrowed(v___x_24_, v_snd_20_, v___x_27_);
lean_dec(v___x_27_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___x_28_);
v___x_29_ = l_Lean_Meta_getDecLevel(v___x_28_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_a_30_);
lean_dec_ref(v___x_29_);
v___x_31_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1));
v___x_32_ = lean_box(0);
lean_inc(v_fst_19_);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v_fst_19_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
lean_inc(v_a_30_);
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v_a_30_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = l_Lean_mkConst(v___x_31_, v___x_34_);
lean_inc(v___x_28_);
v___x_36_ = l_Lean_mkAppB(v___x_35_, v___x_28_, v_fst_15_);
v___x_37_ = l_Lean_mkLevelMax(v_fst_19_, v_a_30_);
v___x_38_ = l_Lean_Level_normalize(v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_array_pop(v_snd_20_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_39_);
lean_ctor_set(v___x_22_, 0, v___x_38_);
v___x_41_ = v___x_22_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___x_39_);
v___x_41_ = v_reuseFailAlloc_47_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_43_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_41_);
lean_ctor_set(v___x_17_, 0, v___x_36_);
v___x_43_ = v___x_17_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_41_);
v___x_43_ = v_reuseFailAlloc_46_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
lean_object* v___x_44_; 
v___x_44_ = lean_nat_add(v_a_5_, v___x_26_);
lean_dec(v_a_5_);
v_a_5_ = v___x_44_;
v_b_6_ = v___x_43_;
goto _start;
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_del_object(v___x_22_);
lean_dec(v_snd_20_);
lean_dec(v_fst_19_);
lean_del_object(v___x_17_);
lean_dec(v_fst_15_);
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v_a_5_);
v_a_48_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_29_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_29_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___boxed(lean_object* v_upperBound_58_, lean_object* v_a_59_, lean_object* v_b_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v_upperBound_58_, v_a_59_, v_b_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
lean_dec(v_upperBound_58_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdN(lean_object* v_ts_70_, lean_object* v_u_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_array_get_size(v_ts_70_);
v___x_79_ = lean_nat_dec_lt(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec_ref(v_ts_70_);
v___x_80_ = ((lean_object*)(l_Lean_Meta_mkProdN___closed__1));
v___x_81_ = l_Lean_Level_succ___override(v_u_71_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = l_Lean_mkConst(v___x_80_, v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_tupleTy_88_; lean_object* v___x_89_; 
lean_dec(v_u_71_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_sub(v___x_78_, v___x_86_);
v_tupleTy_88_ = lean_array_fget(v_ts_70_, v___x_87_);
lean_dec(v___x_87_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_tupleTy_88_);
v___x_89_ = l_Lean_Meta_getDecLevel(v_tupleTy_88_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
lean_dec_ref(v___x_89_);
v___x_91_ = lean_array_pop(v_ts_70_);
v___x_92_ = lean_array_get_size(v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_a_90_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_tupleTy_88_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v___x_92_, v___x_77_, v___x_94_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_104_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_fst_100_; lean_object* v___x_102_; 
v_fst_100_ = lean_ctor_get(v_a_96_, 0);
lean_inc(v_fst_100_);
lean_dec(v_a_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v_fst_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_fst_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_105_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_95_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_95_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec(v_tupleTy_88_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec_ref(v_ts_70_);
v_a_113_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_89_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_89_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdN___boxed(lean_object* v_ts_121_, lean_object* v_u_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Meta_mkProdN(v_ts_121_, v_u_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(lean_object* v_upperBound_129_, lean_object* v_inst_130_, lean_object* v_R_131_, lean_object* v_a_132_, lean_object* v_b_133_, lean_object* v_c_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v_upperBound_129_, v_a_132_, v_b_133_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___boxed(lean_object* v_upperBound_141_, lean_object* v_inst_142_, lean_object* v_R_143_, lean_object* v_a_144_, lean_object* v_b_145_, lean_object* v_c_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(v_upperBound_141_, v_inst_142_, v_R_143_, v_a_144_, v_b_145_, v_c_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v_upperBound_141_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(lean_object* v_upperBound_157_, lean_object* v_a_158_, lean_object* v_b_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_lt(v_a_158_, v_upperBound_157_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v_a_158_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v_b_159_);
return v___x_166_;
}
else
{
lean_object* v_snd_167_; lean_object* v_snd_168_; lean_object* v_fst_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_233_; 
v_snd_167_ = lean_ctor_get(v_b_159_, 1);
lean_inc(v_snd_167_);
v_snd_168_ = lean_ctor_get(v_snd_167_, 1);
lean_inc(v_snd_168_);
v_fst_169_ = lean_ctor_get(v_b_159_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_b_159_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v_b_159_, 1);
lean_dec(v_unused_234_);
v___x_171_ = v_b_159_;
v_isShared_172_ = v_isSharedCheck_233_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_fst_169_);
lean_dec(v_b_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_233_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_fst_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_231_; 
v_fst_173_ = lean_ctor_get(v_snd_167_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_snd_167_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v_snd_167_, 1);
lean_dec(v_unused_232_);
v___x_175_ = v_snd_167_;
v_isShared_176_ = v_isSharedCheck_231_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_fst_173_);
lean_dec(v_snd_167_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_231_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_fst_177_; lean_object* v_snd_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_230_; 
v_fst_177_ = lean_ctor_get(v_snd_168_, 0);
v_snd_178_ = lean_ctor_get(v_snd_168_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_snd_168_);
if (v_isSharedCheck_230_ == 0)
{
v___x_180_ = v_snd_168_;
v_isShared_181_ = v_isSharedCheck_230_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_snd_178_);
lean_inc(v_fst_177_);
lean_dec(v_snd_168_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_230_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = l_Lean_instInhabitedExpr;
v___x_183_ = lean_array_get_size(v_snd_178_);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_sub(v___x_183_, v___x_184_);
v___x_186_ = lean_array_get_borrowed(v___x_182_, v_snd_178_, v___x_185_);
lean_dec(v___x_185_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc(v___x_186_);
v___x_187_ = lean_infer_type(v___x_186_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref(v___x_187_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc(v_a_188_);
v___x_189_ = l_Lean_Meta_getDecLevel(v_a_188_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref(v___x_189_);
v___x_191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1));
v___x_192_ = lean_box(0);
lean_inc(v_fst_177_);
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v_fst_177_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_inc(v_a_190_);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v_a_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
lean_inc_ref(v___x_194_);
v___x_195_ = l_Lean_mkConst(v___x_191_, v___x_194_);
lean_inc(v___x_186_);
lean_inc(v_fst_173_);
lean_inc(v_a_188_);
v___x_196_ = l_Lean_mkApp4(v___x_195_, v_a_188_, v_fst_173_, v___x_186_, v_fst_169_);
v___x_197_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1));
v___x_198_ = l_Lean_mkConst(v___x_197_, v___x_194_);
v___x_199_ = l_Lean_mkAppB(v___x_198_, v_a_188_, v_fst_173_);
v___x_200_ = l_Lean_mkLevelMax(v_fst_177_, v_a_190_);
v___x_201_ = l_Lean_Level_normalize(v___x_200_);
lean_dec(v___x_200_);
v___x_202_ = lean_array_pop(v_snd_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_202_);
lean_ctor_set(v___x_180_, 0, v___x_201_);
v___x_204_ = v___x_180_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_213_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_206_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_204_);
lean_ctor_set(v___x_175_, 0, v___x_199_);
v___x_206_ = v___x_175_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_212_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_208_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_206_);
lean_ctor_set(v___x_171_, 0, v___x_196_);
v___x_208_ = v___x_171_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_206_);
v___x_208_ = v_reuseFailAlloc_211_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = lean_nat_add(v_a_158_, v___x_184_);
lean_dec(v_a_158_);
v_a_158_ = v___x_209_;
v_b_159_ = v___x_208_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_a_188_);
lean_del_object(v___x_180_);
lean_dec(v_snd_178_);
lean_dec(v_fst_177_);
lean_del_object(v___x_175_);
lean_dec(v_fst_173_);
lean_del_object(v___x_171_);
lean_dec(v_fst_169_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v_a_158_);
v_a_214_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_189_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_189_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_del_object(v___x_180_);
lean_dec(v_snd_178_);
lean_dec(v_fst_177_);
lean_del_object(v___x_175_);
lean_dec(v_fst_173_);
lean_del_object(v___x_171_);
lean_dec(v_fst_169_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v_a_158_);
v_a_222_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_187_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_187_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___boxed(lean_object* v_upperBound_235_, lean_object* v_a_236_, lean_object* v_b_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v_upperBound_235_, v_a_236_, v_b_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v_upperBound_235_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdMkN(lean_object* v_es_248_, lean_object* v_u_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_array_get_size(v_es_248_);
v___x_257_ = lean_nat_dec_lt(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_es_248_);
v___x_258_ = ((lean_object*)(l_Lean_Meta_mkProdMkN___closed__1));
v___x_259_ = l_Lean_Level_succ___override(v_u_249_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_inc_ref(v___x_261_);
v___x_262_ = l_Lean_mkConst(v___x_258_, v___x_261_);
v___x_263_ = ((lean_object*)(l_Lean_Meta_mkProdN___closed__1));
v___x_264_ = l_Lean_mkConst(v___x_263_, v___x_261_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_262_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_tuple_269_; lean_object* v___x_270_; 
lean_dec(v_u_249_);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_sub(v___x_256_, v___x_267_);
v_tuple_269_ = lean_array_fget(v_es_248_, v___x_268_);
lean_dec(v___x_268_);
lean_inc(v_a_253_);
lean_inc_ref(v_a_252_);
lean_inc(v_a_251_);
lean_inc_ref(v_a_250_);
lean_inc(v_tuple_269_);
v___x_270_ = lean_infer_type(v_tuple_269_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
lean_inc(v_a_253_);
lean_inc_ref(v_a_252_);
lean_inc(v_a_251_);
lean_inc_ref(v_a_250_);
lean_inc(v_a_271_);
v___x_272_ = l_Lean_Meta_getDecLevel(v_a_271_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
v___x_274_ = lean_array_pop(v_es_248_);
v___x_275_ = lean_array_get_size(v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v_a_273_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_a_271_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_tuple_269_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v___x_275_, v___x_255_, v___x_278_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_298_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_298_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_snd_284_; lean_object* v_fst_285_; lean_object* v_fst_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_snd_284_ = lean_ctor_get(v_a_280_, 1);
lean_inc(v_snd_284_);
v_fst_285_ = lean_ctor_get(v_a_280_, 0);
lean_inc(v_fst_285_);
lean_dec(v_a_280_);
v_fst_286_ = lean_ctor_get(v_snd_284_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_snd_284_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_snd_284_, 1);
lean_dec(v_unused_297_);
v___x_288_ = v_snd_284_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_fst_286_);
lean_dec(v_snd_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v_fst_286_);
lean_ctor_set(v___x_288_, 0, v_fst_285_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_fst_285_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_fst_286_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_291_);
v___x_293_ = v___x_282_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_279_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_279_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v_a_271_);
lean_dec(v_tuple_269_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_es_248_);
v_a_307_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_272_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_272_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_tuple_269_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_es_248_);
v_a_315_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_270_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_270_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdMkN___boxed(lean_object* v_es_323_, lean_object* v_u_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_mkProdMkN(v_es_323_, v_u_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(lean_object* v_upperBound_331_, lean_object* v_inst_332_, lean_object* v_R_333_, lean_object* v_a_334_, lean_object* v_b_335_, lean_object* v_c_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v_upperBound_331_, v_a_334_, v_b_335_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___boxed(lean_object* v_upperBound_343_, lean_object* v_inst_344_, lean_object* v_R_345_, lean_object* v_a_346_, lean_object* v_b_347_, lean_object* v_c_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(v_upperBound_343_, v_inst_344_, v_R_345_, v_a_346_, v_b_347_, v_c_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v_upperBound_343_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(lean_object* v_msgData_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; lean_object* v_env_362_; lean_object* v___x_363_; lean_object* v_mctx_364_; lean_object* v_lctx_365_; lean_object* v_options_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_361_ = lean_st_ref_get(v___y_359_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_361_);
v___x_363_ = lean_st_ref_get(v___y_357_);
v_mctx_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_mctx_364_);
lean_dec(v___x_363_);
v_lctx_365_ = lean_ctor_get(v___y_356_, 2);
v_options_366_ = lean_ctor_get(v___y_358_, 2);
lean_inc_ref(v_options_366_);
lean_inc_ref(v_lctx_365_);
v___x_367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_367_, 0, v_env_362_);
lean_ctor_set(v___x_367_, 1, v_mctx_364_);
lean_ctor_set(v___x_367_, 2, v_lctx_365_);
lean_ctor_set(v___x_367_, 3, v_options_366_);
v___x_368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_msgData_355_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0___boxed(lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(v_msgData_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_ref_383_; lean_object* v___x_384_; lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_ref_383_ = lean_ctor_get(v___y_380_, 5);
v___x_384_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(v_msg_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
lean_inc(v_ref_383_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_ref_383_);
lean_ctor_set(v___x_389_, 1, v_a_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set_tag(v___x_387_, 1);
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg___boxed(lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(v_msg_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
static lean_object* _init_l_Lean_Meta_getProdFields___closed__1(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__0));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Meta_getProdFields___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__2));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getProdFields(lean_object* v_tuple_415_, lean_object* v_tupleTy_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_tupleTy_416_, v_a_418_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_462_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_462_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_462_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_462_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___x_440_; uint8_t v___x_441_; 
lean_inc(v_a_423_);
v___x_440_ = l_Lean_Expr_cleanupAnnotations(v_a_423_);
v___x_441_ = l_Lean_Expr_isApp(v___x_440_);
if (v___x_441_ == 0)
{
lean_dec_ref(v___x_440_);
lean_del_object(v___x_425_);
v___y_428_ = v_a_417_;
v___y_429_ = v_a_418_;
v___y_430_ = v_a_419_;
v___y_431_ = v_a_420_;
goto v___jp_427_;
}
else
{
lean_object* v_arg_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_arg_442_ = lean_ctor_get(v___x_440_, 1);
lean_inc_ref(v_arg_442_);
v___x_443_ = l_Lean_Expr_appFnCleanup___redArg(v___x_440_);
v___x_444_ = l_Lean_Expr_isApp(v___x_443_);
if (v___x_444_ == 0)
{
lean_dec_ref(v___x_443_);
lean_dec_ref(v_arg_442_);
lean_del_object(v___x_425_);
v___y_428_ = v_a_417_;
v___y_429_ = v_a_418_;
v___y_430_ = v_a_419_;
v___y_431_ = v_a_420_;
goto v___jp_427_;
}
else
{
lean_object* v_arg_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_arg_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc_ref(v_arg_445_);
v___x_446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_443_);
v___x_447_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1));
v___x_448_ = l_Lean_Expr_isConstOf(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_dec_ref(v___x_446_);
lean_dec_ref(v_arg_445_);
lean_dec_ref(v_arg_442_);
lean_del_object(v___x_425_);
v___y_428_ = v_a_417_;
v___y_429_ = v_a_418_;
v___y_430_ = v_a_419_;
v___y_431_ = v_a_420_;
goto v___jp_427_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec(v_a_423_);
v___x_449_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__5));
v___x_450_ = l_Lean_Expr_constLevels_x21(v___x_446_);
lean_dec_ref(v___x_446_);
lean_inc(v___x_450_);
v___x_451_ = l_Lean_mkConst(v___x_449_, v___x_450_);
lean_inc_ref(v_tuple_415_);
lean_inc_ref(v_arg_442_);
lean_inc_ref(v_arg_445_);
v___x_452_ = l_Lean_mkApp3(v___x_451_, v_arg_445_, v_arg_442_, v_tuple_415_);
v___x_453_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__7));
v___x_454_ = l_Lean_mkConst(v___x_453_, v___x_450_);
lean_inc_ref(v_arg_442_);
lean_inc_ref(v_arg_445_);
v___x_455_ = l_Lean_mkApp3(v___x_454_, v_arg_445_, v_arg_442_, v_tuple_415_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_arg_442_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_arg_445_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_452_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_458_);
v___x_460_ = v___x_425_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_getProdFields___closed__1, &l_Lean_Meta_getProdFields___closed__1_once, _init_l_Lean_Meta_getProdFields___closed__1);
v___x_433_ = l_Lean_MessageData_ofExpr(v_tuple_415_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_obj_once(&l_Lean_Meta_getProdFields___closed__3, &l_Lean_Meta_getProdFields___closed__3_once, _init_l_Lean_Meta_getProdFields___closed__3);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_MessageData_ofExpr(v_a_423_);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(v___x_438_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
return v___x_439_;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_tuple_415_);
v_a_463_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_422_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_422_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getProdFields___boxed(lean_object* v_tuple_471_, lean_object* v_tupleTy_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_getProdFields(v_tuple_471_, v_tupleTy_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(lean_object* v_00_u03b1_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___boxed(lean_object* v_00_u03b1_487_, lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(v_00_u03b1_487_, v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_ProdN(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ProdN(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_ProdN(builtin);
}
#ifdef __cplusplus
}
#endif
