// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.IsRelevant
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType(lean_object* v_00_u03b1_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
uint8_t v___y_14_; uint8_t v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_Arith_isNatType(v_00_u03b1_1_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
v___x_59_ = l_Lean_Meta_Grind_Arith_isIntType(v_00_u03b1_1_);
v___y_14_ = v___x_59_;
goto v___jp_13_;
}
else
{
v___y_14_ = v___x_58_;
goto v___jp_13_;
}
v___jp_13_:
{
uint8_t v___x_15_; 
v___x_15_ = 1;
if (v___y_14_ == 0)
{
lean_object* v___x_16_; 
lean_inc_ref(v_00_u03b1_1_);
v___x_16_ = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(v_00_u03b1_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_47_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_47_ == 0)
{
v___x_19_ = v___x_16_;
v_isShared_20_ = v_isSharedCheck_47_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_47_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
if (lean_obj_tag(v_a_17_) == 0)
{
lean_object* v___x_21_; 
lean_del_object(v___x_19_);
v___x_21_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_00_u03b1_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_34_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_34_ == 0)
{
v___x_24_ = v___x_21_;
v_isShared_25_ = v_isSharedCheck_34_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_34_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
if (lean_obj_tag(v_a_22_) == 0)
{
lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_26_ = lean_box(v___y_14_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_26_);
v___x_28_ = v___x_24_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
else
{
lean_object* v___x_30_; lean_object* v___x_32_; 
lean_dec_ref(v_a_22_);
v___x_30_ = lean_box(v___x_15_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_30_);
v___x_32_ = v___x_24_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
v_a_35_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_21_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_21_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
else
{
lean_object* v___x_43_; lean_object* v___x_45_; 
lean_dec_ref(v_a_17_);
lean_dec_ref(v_00_u03b1_1_);
v___x_43_ = lean_box(v___x_15_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_43_);
v___x_45_ = v___x_19_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_dec_ref(v_00_u03b1_1_);
v_a_48_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_16_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_16_);
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
else
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec_ref(v_00_u03b1_1_);
v___x_56_ = lean_box(v___x_15_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object* v_00_u03b1_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_Grind_Arith_isSupportedType(v_00_u03b1_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec(v_a_61_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object* v_e_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = l_Lean_Expr_cleanupAnnotations(v_e_100_);
v___x_117_ = l_Lean_Expr_isApp(v___x_116_);
if (v___x_117_ == 0)
{
lean_dec_ref(v___x_116_);
goto v___jp_112_;
}
else
{
lean_object* v_arg_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_arg_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_arg_118_);
v___x_119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_116_);
v___x_120_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1));
v___x_121_ = l_Lean_Expr_isConstOf(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = l_Lean_Expr_isApp(v___x_119_);
if (v___x_122_ == 0)
{
lean_dec_ref(v___x_119_);
lean_dec_ref(v_arg_118_);
goto v___jp_112_;
}
else
{
lean_object* v_arg_123_; lean_object* v_q_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_arg_123_ = lean_ctor_get(v___x_119_, 1);
lean_inc_ref(v_arg_123_);
v___x_140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_119_);
v___x_141_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3));
v___x_142_ = l_Lean_Expr_isConstOf(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5));
v___x_144_ = l_Lean_Expr_isConstOf(v___x_140_, v___x_143_);
if (v___x_144_ == 0)
{
uint8_t v___x_145_; 
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_arg_118_);
v___x_145_ = l_Lean_Expr_isApp(v___x_140_);
if (v___x_145_ == 0)
{
lean_dec_ref(v___x_140_);
goto v___jp_112_;
}
else
{
lean_object* v_arg_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_arg_146_ = lean_ctor_get(v___x_140_, 1);
lean_inc_ref(v_arg_146_);
v___x_147_ = l_Lean_Expr_appFnCleanup___redArg(v___x_140_);
v___x_148_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7));
v___x_149_ = l_Lean_Expr_isConstOf(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
lean_dec_ref(v_arg_146_);
v___x_150_ = l_Lean_Expr_isApp(v___x_147_);
if (v___x_150_ == 0)
{
lean_dec_ref(v___x_147_);
goto v___jp_112_;
}
else
{
lean_object* v_arg_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_arg_151_ = lean_ctor_get(v___x_147_, 1);
lean_inc_ref(v_arg_151_);
v___x_152_ = l_Lean_Expr_appFnCleanup___redArg(v___x_147_);
v___x_153_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10));
v___x_154_ = l_Lean_Expr_isConstOf(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13));
v___x_156_ = l_Lean_Expr_isConstOf(v___x_152_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16));
v___x_158_ = l_Lean_Expr_isConstOf(v___x_152_, v___x_157_);
lean_dec_ref(v___x_152_);
if (v___x_158_ == 0)
{
lean_dec_ref(v_arg_151_);
goto v___jp_112_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_Arith_isSupportedType(v_arg_151_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_159_;
}
}
else
{
lean_object* v___x_160_; 
lean_dec_ref(v___x_152_);
v___x_160_ = l_Lean_Meta_Grind_Arith_isSupportedType(v_arg_151_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_160_;
}
}
else
{
lean_object* v___x_161_; 
lean_dec_ref(v___x_152_);
v___x_161_ = l_Lean_Meta_Grind_Arith_isSupportedType(v_arg_151_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_161_;
}
}
}
else
{
lean_object* v___x_162_; 
lean_dec_ref(v___x_147_);
v___x_162_ = l_Lean_Meta_Grind_Arith_isSupportedType(v_arg_146_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_162_;
}
}
}
else
{
lean_dec_ref(v___x_140_);
v_q_125_ = v_arg_118_;
v___y_126_ = v_a_101_;
v___y_127_ = v_a_102_;
v___y_128_ = v_a_103_;
v___y_129_ = v_a_104_;
v___y_130_ = v_a_105_;
v___y_131_ = v_a_106_;
v___y_132_ = v_a_107_;
v___y_133_ = v_a_108_;
v___y_134_ = v_a_109_;
v___y_135_ = v_a_110_;
goto v___jp_124_;
}
}
else
{
lean_dec_ref(v___x_140_);
v_q_125_ = v_arg_118_;
v___y_126_ = v_a_101_;
v___y_127_ = v_a_102_;
v___y_128_ = v_a_103_;
v___y_129_ = v_a_104_;
v___y_130_ = v_a_105_;
v___y_131_ = v_a_106_;
v___y_132_ = v_a_107_;
v___y_133_ = v_a_108_;
v___y_134_ = v_a_109_;
v___y_135_ = v_a_110_;
goto v___jp_124_;
}
v___jp_124_:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Grind_Arith_isRelevantPred(v_arg_123_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; uint8_t v___x_138_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
v___x_138_ = lean_unbox(v_a_137_);
lean_dec(v_a_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v___x_136_);
v_e_100_ = v_q_125_;
v_a_101_ = v___y_126_;
v_a_102_ = v___y_127_;
v_a_103_ = v___y_128_;
v_a_104_ = v___y_129_;
v_a_105_ = v___y_130_;
v_a_106_ = v___y_131_;
v_a_107_ = v___y_132_;
v_a_108_ = v___y_133_;
v_a_109_ = v___y_134_;
v_a_110_ = v___y_135_;
goto _start;
}
else
{
lean_dec_ref(v_q_125_);
return v___x_136_;
}
}
else
{
lean_dec_ref(v_q_125_);
return v___x_136_;
}
}
}
}
else
{
lean_dec_ref(v___x_119_);
v_e_100_ = v_arg_118_;
goto _start;
}
}
v___jp_112_:
{
uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = 0;
v___x_114_ = lean_box(v___x_113_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object* v_e_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Meta_Grind_Arith_isRelevantPred(v_e_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec(v_a_165_);
return v_res_176_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(builtin);
}
#ifdef __cplusplus
}
#endif
