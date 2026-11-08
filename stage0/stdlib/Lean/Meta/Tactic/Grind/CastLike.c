// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CastLike
// Imports: public import Lean.Expr import Init.Grind.Ring.Envelope import Init.Grind.Module.Envelope
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__4_value),LEAN_SCALAR_PTR_LITERAL(232, 146, 236, 221, 122, 127, 105, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__7_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isEnvelopeEmbeddingFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEnvelopeEmbeddingFn___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeFn___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName(lean_object* v_declName_20_){
_start:
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__5));
v___x_22_ = lean_name_eq(v_declName_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___closed__8));
v___x_24_ = lean_name_eq(v_declName_20_, v___x_23_);
return v___x_24_;
}
else
{
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName___boxed(lean_object* v_declName_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName(v_declName_25_);
lean_dec(v_declName_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isEnvelopeEmbeddingFn(lean_object* v_f_28_){
_start:
{
if (lean_obj_tag(v_f_28_) == 4)
{
lean_object* v_declName_29_; uint8_t v___x_30_; 
v_declName_29_ = lean_ctor_get(v_f_28_, 0);
v___x_30_ = l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName(v_declName_29_);
return v___x_30_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEnvelopeEmbeddingFn___boxed(lean_object* v_f_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Meta_Grind_isEnvelopeEmbeddingFn(v_f_32_);
lean_dec_ref(v_f_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object* v_declName_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l___private_Lean_Meta_Tactic_Grind_CastLike_0__Lean_Meta_Grind_isEnvelopeEmbeddingDeclName(v_declName_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = ((lean_object*)(l_Lean_Meta_Grind_isCastLikeDeclName___closed__2));
v___x_48_ = lean_name_eq(v_declName_45_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = ((lean_object*)(l_Lean_Meta_Grind_isCastLikeDeclName___closed__5));
v___x_50_ = lean_name_eq(v_declName_45_, v___x_49_);
return v___x_50_;
}
else
{
return v___x_48_;
}
}
else
{
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___boxed(lean_object* v_declName_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_51_);
lean_dec(v_declName_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object* v_f_54_){
_start:
{
if (lean_obj_tag(v_f_54_) == 4)
{
lean_object* v_declName_55_; uint8_t v___x_56_; 
v_declName_55_ = lean_ctor_get(v_f_54_, 0);
v___x_56_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_55_);
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = 0;
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeFn___boxed(lean_object* v_f_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_Meta_Grind_isCastLikeFn(v_f_58_);
lean_dec_ref(v_f_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object* v_e_61_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = l_Lean_Expr_getAppFn(v_e_61_);
v___x_63_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_62_);
lean_dec_ref(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeApp___boxed(lean_object* v_e_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lean_Meta_Grind_isCastLikeApp(v_e_64_);
lean_dec_ref(v_e_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
}
#ifdef __cplusplus
}
#endif
