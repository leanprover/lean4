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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(lean_object* v_upperBound_4_, lean_object* v_a_5_, lean_object* v_b_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_lt(v_a_5_, v_upperBound_4_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
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
lean_inc(v___x_28_);
v___x_29_ = l_Lean_Meta_getDecLevel(v___x_28_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_n(v_a_30_, 2);
lean_dec_ref_known(v___x_29_, 1);
v___x_31_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1));
v___x_32_ = lean_box(0);
lean_inc(v_fst_19_);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v_fst_19_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4_ = stack[0].m_obj;
lean_object* v_a_5_ = stack[1].m_obj;
lean_object* v_b_6_ = stack[2].m_obj;
lean_object* v___y_7_ = stack[3].m_obj;
lean_object* v___y_8_ = stack[4].m_obj;
lean_object* v___y_9_ = stack[5].m_obj;
lean_object* v___y_10_ = stack[6].m_obj;
lean_object* v_res_58_;
v_res_58_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v_upperBound_4_, v_a_5_, v_b_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___boxed(lean_object* v_upperBound_59_, lean_object* v_a_60_, lean_object* v_b_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v_upperBound_59_, v_a_60_, v_b_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v_upperBound_59_);
return v_res_67_;
}
}
lean_object* l_Lean_Meta_mkProdN(lean_object* v_ts_71_, lean_object* v_u_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_array_get_size(v_ts_71_);
v___x_80_ = lean_nat_dec_lt(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref(v_ts_71_);
v___x_81_ = ((lean_object*)(l_Lean_Meta_mkProdN___closed__1));
v___x_82_ = l_Lean_Level_succ___override(v_u_72_);
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = l_Lean_mkConst(v___x_81_, v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_tupleTy_89_; lean_object* v___x_90_; 
lean_dec(v_u_72_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_sub(v___x_79_, v___x_87_);
v_tupleTy_89_ = lean_array_fget(v_ts_71_, v___x_88_);
lean_dec(v___x_88_);
lean_inc(v_tupleTy_89_);
v___x_90_ = l_Lean_Meta_getDecLevel(v_tupleTy_89_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = lean_array_pop(v_ts_71_);
v___x_93_ = lean_array_get_size(v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_a_91_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_tupleTy_89_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v___x_93_, v___x_78_, v___x_95_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_fst_101_; lean_object* v___x_103_; 
v_fst_101_ = lean_ctor_get(v_a_97_, 0);
lean_inc(v_fst_101_);
lean_dec(v_a_97_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v_fst_101_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_fst_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_96_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_96_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
lean_dec(v_tupleTy_89_);
lean_dec_ref(v_ts_71_);
v_a_114_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_90_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_90_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkProdN_0interp(lean_interpreter_value* stack)
{
lean_object* v_ts_71_ = stack[0].m_obj;
lean_object* v_u_72_ = stack[1].m_obj;
lean_object* v_a_73_ = stack[2].m_obj;
lean_object* v_a_74_ = stack[3].m_obj;
lean_object* v_a_75_ = stack[4].m_obj;
lean_object* v_a_76_ = stack[5].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_Lean_Meta_mkProdN(v_ts_71_, v_u_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdN___boxed(lean_object* v_ts_123_, lean_object* v_u_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_mkProdN(v_ts_123_, v_u_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
return v_res_130_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(lean_object* v_upperBound_131_, lean_object* v_inst_132_, lean_object* v_R_133_, lean_object* v_a_134_, lean_object* v_b_135_, lean_object* v_c_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v_upperBound_131_, v_a_134_, v_b_135_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
return v___x_142_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_131_ = stack[0].m_obj;
lean_object* v_a_134_ = stack[3].m_obj;
lean_object* v_b_135_ = stack[4].m_obj;
lean_object* v___y_137_ = stack[6].m_obj;
lean_object* v___y_138_ = stack[7].m_obj;
lean_object* v___y_139_ = stack[8].m_obj;
lean_object* v___y_140_ = stack[9].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(v_upperBound_131_, lean_box(0), lean_box(0), v_a_134_, v_b_135_, lean_box(0), v___y_137_, v___y_138_, v___y_139_, v___y_140_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___boxed(lean_object* v_upperBound_144_, lean_object* v_inst_145_, lean_object* v_R_146_, lean_object* v_a_147_, lean_object* v_b_148_, lean_object* v_c_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(v_upperBound_144_, v_inst_145_, v_R_146_, v_a_147_, v_b_148_, v_c_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v_upperBound_144_);
return v_res_155_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(lean_object* v_upperBound_160_, lean_object* v_a_161_, lean_object* v_b_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = lean_nat_dec_lt(v_a_161_, v_upperBound_160_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec(v_a_161_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_b_162_);
return v___x_169_;
}
else
{
lean_object* v_snd_170_; lean_object* v_snd_171_; lean_object* v_fst_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_236_; 
v_snd_170_ = lean_ctor_get(v_b_162_, 1);
lean_inc(v_snd_170_);
v_snd_171_ = lean_ctor_get(v_snd_170_, 1);
lean_inc(v_snd_171_);
v_fst_172_ = lean_ctor_get(v_b_162_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v_b_162_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v_b_162_, 1);
lean_dec(v_unused_237_);
v___x_174_ = v_b_162_;
v_isShared_175_ = v_isSharedCheck_236_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_fst_172_);
lean_dec(v_b_162_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_236_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_fst_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_234_; 
v_fst_176_ = lean_ctor_get(v_snd_170_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_snd_170_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v_snd_170_, 1);
lean_dec(v_unused_235_);
v___x_178_ = v_snd_170_;
v_isShared_179_ = v_isSharedCheck_234_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_fst_176_);
lean_dec(v_snd_170_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_234_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_233_; 
v_fst_180_ = lean_ctor_get(v_snd_171_, 0);
v_snd_181_ = lean_ctor_get(v_snd_171_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_snd_171_);
if (v_isSharedCheck_233_ == 0)
{
v___x_183_ = v_snd_171_;
v_isShared_184_ = v_isSharedCheck_233_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v_snd_171_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_233_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_185_ = l_Lean_instInhabitedExpr;
v___x_186_ = lean_array_get_size(v_snd_181_);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_sub(v___x_186_, v___x_187_);
v___x_189_ = lean_array_get_borrowed(v___x_185_, v_snd_181_, v___x_188_);
lean_dec(v___x_188_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___x_189_);
v___x_190_ = lean_infer_type(v___x_189_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc_n(v_a_191_, 2);
lean_dec_ref_known(v___x_190_, 1);
v___x_192_ = l_Lean_Meta_getDecLevel(v_a_191_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc_n(v_a_193_, 2);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1));
v___x_195_ = lean_box(0);
lean_inc(v_fst_180_);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v_fst_180_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v_a_193_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
lean_inc_ref(v___x_197_);
v___x_198_ = l_Lean_mkConst(v___x_194_, v___x_197_);
lean_inc(v___x_189_);
lean_inc(v_fst_176_);
lean_inc(v_a_191_);
v___x_199_ = l_Lean_mkApp4(v___x_198_, v_a_191_, v_fst_176_, v___x_189_, v_fst_172_);
v___x_200_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1));
v___x_201_ = l_Lean_mkConst(v___x_200_, v___x_197_);
v___x_202_ = l_Lean_mkAppB(v___x_201_, v_a_191_, v_fst_176_);
v___x_203_ = l_Lean_mkLevelMax(v_fst_180_, v_a_193_);
v___x_204_ = l_Lean_Level_normalize(v___x_203_);
lean_dec(v___x_203_);
v___x_205_ = lean_array_pop(v_snd_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_205_);
lean_ctor_set(v___x_183_, 0, v___x_204_);
v___x_207_ = v___x_183_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_216_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_207_);
lean_ctor_set(v___x_178_, 0, v___x_202_);
v___x_209_ = v___x_178_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_215_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_209_);
lean_ctor_set(v___x_174_, 0, v___x_199_);
v___x_211_ = v___x_174_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_214_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; 
v___x_212_ = lean_nat_add(v_a_161_, v___x_187_);
lean_dec(v_a_161_);
v_a_161_ = v___x_212_;
v_b_162_ = v___x_211_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_a_191_);
lean_del_object(v___x_183_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
lean_del_object(v___x_174_);
lean_dec(v_fst_172_);
lean_dec(v_a_161_);
v_a_217_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_192_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_192_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_del_object(v___x_183_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
lean_del_object(v___x_174_);
lean_dec(v_fst_172_);
lean_dec(v_a_161_);
v_a_225_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_190_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_190_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_160_ = stack[0].m_obj;
lean_object* v_a_161_ = stack[1].m_obj;
lean_object* v_b_162_ = stack[2].m_obj;
lean_object* v___y_163_ = stack[3].m_obj;
lean_object* v___y_164_ = stack[4].m_obj;
lean_object* v___y_165_ = stack[5].m_obj;
lean_object* v___y_166_ = stack[6].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v_upperBound_160_, v_a_161_, v_b_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___boxed(lean_object* v_upperBound_239_, lean_object* v_a_240_, lean_object* v_b_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v_upperBound_239_, v_a_240_, v_b_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v_upperBound_239_);
return v_res_247_;
}
}
lean_object* l_Lean_Meta_mkProdMkN(lean_object* v_es_252_, lean_object* v_u_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_array_get_size(v_es_252_);
v___x_261_ = lean_nat_dec_lt(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref(v_es_252_);
v___x_262_ = ((lean_object*)(l_Lean_Meta_mkProdMkN___closed__1));
v___x_263_ = l_Lean_Level_succ___override(v_u_253_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
lean_inc_ref(v___x_265_);
v___x_266_ = l_Lean_mkConst(v___x_262_, v___x_265_);
v___x_267_ = ((lean_object*)(l_Lean_Meta_mkProdN___closed__1));
v___x_268_ = l_Lean_mkConst(v___x_267_, v___x_265_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_266_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_tuple_273_; lean_object* v___x_274_; 
lean_dec(v_u_253_);
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_sub(v___x_260_, v___x_271_);
v_tuple_273_ = lean_array_fget(v_es_252_, v___x_272_);
lean_dec(v___x_272_);
lean_inc(v_a_257_);
lean_inc_ref(v_a_256_);
lean_inc(v_a_255_);
lean_inc_ref(v_a_254_);
lean_inc(v_tuple_273_);
v___x_274_ = lean_infer_type(v_tuple_273_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc_n(v_a_275_, 2);
lean_dec_ref_known(v___x_274_, 1);
v___x_276_ = l_Lean_Meta_getDecLevel(v_a_275_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v___x_278_ = lean_array_pop(v_es_252_);
v___x_279_ = lean_array_get_size(v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_a_277_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_a_275_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_tuple_273_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v___x_279_, v___x_259_, v___x_282_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_302_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_302_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_302_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_302_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_snd_288_; lean_object* v_fst_289_; lean_object* v_fst_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v_snd_288_ = lean_ctor_get(v_a_284_, 1);
lean_inc(v_snd_288_);
v_fst_289_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_fst_289_);
lean_dec(v_a_284_);
v_fst_290_ = lean_ctor_get(v_snd_288_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_snd_288_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v_snd_288_, 1);
lean_dec(v_unused_301_);
v___x_292_ = v_snd_288_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_fst_290_);
lean_dec(v_snd_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_fst_290_);
lean_ctor_set(v___x_292_, 0, v_fst_289_);
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_fst_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_fst_290_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_295_);
v___x_297_ = v___x_286_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_283_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_283_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_a_275_);
lean_dec(v_tuple_273_);
lean_dec_ref(v_es_252_);
v_a_311_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_276_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_276_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_tuple_273_);
lean_dec_ref(v_es_252_);
v_a_319_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_274_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_274_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkProdMkN_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_252_ = stack[0].m_obj;
lean_object* v_u_253_ = stack[1].m_obj;
lean_object* v_a_254_ = stack[2].m_obj;
lean_object* v_a_255_ = stack[3].m_obj;
lean_object* v_a_256_ = stack[4].m_obj;
lean_object* v_a_257_ = stack[5].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_Meta_mkProdMkN(v_es_252_, v_u_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProdMkN___boxed(lean_object* v_es_328_, lean_object* v_u_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Meta_mkProdMkN(v_es_328_, v_u_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_335_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(lean_object* v_upperBound_336_, lean_object* v_inst_337_, lean_object* v_R_338_, lean_object* v_a_339_, lean_object* v_b_340_, lean_object* v_c_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v_upperBound_336_, v_a_339_, v_b_340_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_347_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_336_ = stack[0].m_obj;
lean_object* v_a_339_ = stack[3].m_obj;
lean_object* v_b_340_ = stack[4].m_obj;
lean_object* v___y_342_ = stack[6].m_obj;
lean_object* v___y_343_ = stack[7].m_obj;
lean_object* v___y_344_ = stack[8].m_obj;
lean_object* v___y_345_ = stack[9].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(v_upperBound_336_, lean_box(0), lean_box(0), v_a_339_, v_b_340_, lean_box(0), v___y_342_, v___y_343_, v___y_344_, v___y_345_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___boxed(lean_object* v_upperBound_349_, lean_object* v_inst_350_, lean_object* v_R_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v_c_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(v_upperBound_349_, v_inst_350_, v_R_351_, v_a_352_, v_b_353_, v_c_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v_upperBound_349_);
return v_res_360_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(lean_object* v_msgData_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; lean_object* v_env_368_; uint8_t v___x_369_; lean_object* v_env_370_; lean_object* v___x_371_; lean_object* v_toCold_372_; lean_object* v_mctx_373_; lean_object* v_lctx_374_; lean_object* v_options_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_367_ = lean_st_ref_get(v___y_365_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_env_368_);
lean_dec(v___x_367_);
v___x_369_ = 0;
v_env_370_ = l_Lean_Environment_setRecordingDeps(v_env_368_, v___x_369_);
v___x_371_ = lean_st_ref_get(v___y_363_);
v_toCold_372_ = lean_ctor_get(v___y_364_, 0);
v_mctx_373_ = lean_ctor_get(v___x_371_, 0);
lean_inc_ref(v_mctx_373_);
lean_dec(v___x_371_);
v_lctx_374_ = lean_ctor_get(v___y_362_, 2);
v_options_375_ = lean_ctor_get(v_toCold_372_, 2);
lean_inc_ref(v_options_375_);
lean_inc_ref(v_lctx_374_);
v___x_376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_376_, 0, v_env_370_);
lean_ctor_set(v___x_376_, 1, v_mctx_373_);
lean_ctor_set(v___x_376_, 2, v_lctx_374_);
lean_ctor_set(v___x_376_, 3, v_options_375_);
v___x_377_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_msgData_361_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_361_ = stack[0].m_obj;
lean_object* v___y_362_ = stack[1].m_obj;
lean_object* v___y_363_ = stack[2].m_obj;
lean_object* v___y_364_ = stack[3].m_obj;
lean_object* v___y_365_ = stack[4].m_obj;
lean_object* v_res_379_;
v_res_379_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(v_msgData_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0___boxed(lean_object* v_msgData_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(v_msgData_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_386_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_ref_393_; lean_object* v___x_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_ref_393_ = lean_ctor_get(v___y_390_, 2);
v___x_394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_inc(v_ref_393_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_ref_393_);
lean_ctor_set(v___x_399_, 1, v_a_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 1);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_387_ = stack[0].m_obj;
lean_object* v___y_388_ = stack[1].m_obj;
lean_object* v___y_389_ = stack[2].m_obj;
lean_object* v___y_390_ = stack[3].m_obj;
lean_object* v___y_391_ = stack[4].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg___boxed(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
static lean_object* _init_l_Lean_Meta_getProdFields___closed__1(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__0));
v___x_414_ = l_Lean_stringToMessageData(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Meta_getProdFields___closed__3(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__2));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
lean_object* l_Lean_Meta_getProdFields(lean_object* v_tuple_426_, lean_object* v_tupleTy_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_tupleTy_427_, v_a_429_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_473_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_473_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_473_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_473_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___x_451_; uint8_t v___x_452_; 
lean_inc(v_a_434_);
v___x_451_ = l_Lean_Expr_cleanupAnnotations(v_a_434_);
v___x_452_ = l_Lean_Expr_isApp(v___x_451_);
if (v___x_452_ == 0)
{
lean_dec_ref(v___x_451_);
lean_del_object(v___x_436_);
v___y_439_ = v_a_428_;
v___y_440_ = v_a_429_;
v___y_441_ = v_a_430_;
v___y_442_ = v_a_431_;
goto v___jp_438_;
}
else
{
lean_object* v_arg_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_arg_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc_ref(v_arg_453_);
v___x_454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_451_);
v___x_455_ = l_Lean_Expr_isApp(v___x_454_);
if (v___x_455_ == 0)
{
lean_dec_ref(v___x_454_);
lean_dec_ref(v_arg_453_);
lean_del_object(v___x_436_);
v___y_439_ = v_a_428_;
v___y_440_ = v_a_429_;
v___y_441_ = v_a_430_;
v___y_442_ = v_a_431_;
goto v___jp_438_;
}
else
{
lean_object* v_arg_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_arg_456_ = lean_ctor_get(v___x_454_, 1);
lean_inc_ref(v_arg_456_);
v___x_457_ = l_Lean_Expr_appFnCleanup___redArg(v___x_454_);
v___x_458_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1));
v___x_459_ = l_Lean_Expr_isConstOf(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec_ref(v___x_457_);
lean_dec_ref(v_arg_456_);
lean_dec_ref(v_arg_453_);
lean_del_object(v___x_436_);
v___y_439_ = v_a_428_;
v___y_440_ = v_a_429_;
v___y_441_ = v_a_430_;
v___y_442_ = v_a_431_;
goto v___jp_438_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
lean_dec(v_a_434_);
v___x_460_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__5));
v___x_461_ = l_Lean_Expr_constLevels_x21(v___x_457_);
lean_dec_ref(v___x_457_);
lean_inc(v___x_461_);
v___x_462_ = l_Lean_mkConst(v___x_460_, v___x_461_);
lean_inc_ref(v_tuple_426_);
lean_inc_ref_n(v_arg_453_, 2);
lean_inc_ref_n(v_arg_456_, 2);
v___x_463_ = l_Lean_mkApp3(v___x_462_, v_arg_456_, v_arg_453_, v_tuple_426_);
v___x_464_ = ((lean_object*)(l_Lean_Meta_getProdFields___closed__7));
v___x_465_ = l_Lean_mkConst(v___x_464_, v___x_461_);
v___x_466_ = l_Lean_mkApp3(v___x_465_, v_arg_456_, v_arg_453_, v_tuple_426_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_arg_453_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_arg_456_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_463_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_469_);
v___x_471_ = v___x_436_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
v___jp_438_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_443_ = lean_obj_once(&l_Lean_Meta_getProdFields___closed__1, &l_Lean_Meta_getProdFields___closed__1_once, _init_l_Lean_Meta_getProdFields___closed__1);
v___x_444_ = l_Lean_MessageData_ofExpr(v_tuple_426_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_obj_once(&l_Lean_Meta_getProdFields___closed__3, &l_Lean_Meta_getProdFields___closed__3_once, _init_l_Lean_Meta_getProdFields___closed__3);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_MessageData_ofExpr(v_a_434_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(v___x_449_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_450_;
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_tuple_426_);
v_a_474_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_433_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_433_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getProdFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_tuple_426_ = stack[0].m_obj;
lean_object* v_tupleTy_427_ = stack[1].m_obj;
lean_object* v_a_428_ = stack[2].m_obj;
lean_object* v_a_429_ = stack[3].m_obj;
lean_object* v_a_430_ = stack[4].m_obj;
lean_object* v_a_431_ = stack[5].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_Meta_getProdFields(v_tuple_426_, v_tupleTy_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getProdFields___boxed(lean_object* v_tuple_483_, lean_object* v_tupleTy_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_getProdFields(v_tuple_483_, v_tupleTy_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
return v_res_490_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(lean_object* v_00_u03b1_491_, lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(v_msg_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_498_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_492_ = stack[1].m_obj;
lean_object* v___y_493_ = stack[2].m_obj;
lean_object* v___y_494_ = stack[3].m_obj;
lean_object* v___y_495_ = stack[4].m_obj;
lean_object* v___y_496_ = stack[5].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(lean_box(0), v_msg_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___boxed(lean_object* v_00_u03b1_500_, lean_object* v_msg_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(v_00_u03b1_500_, v_msg_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_507_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
