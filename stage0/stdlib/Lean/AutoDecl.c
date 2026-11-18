// Lean compiler output
// Module: Lean.AutoDecl
// Imports: public import Lean.Structure public import Lean.CoreM
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
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
extern lean_object* l_Lean_belowSuffix;
extern lean_object* l_Lean_brecOnSuffix;
extern lean_object* l_Lean_recOnSuffix;
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_functor"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "functor_unfold"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ndrecOn"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionType"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ctorElim"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ctorElimType"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "below_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "brecOn_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "grind_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unsafe_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39_value;
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(lean_object* v_a_1_, lean_object* v_x_2_){
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
lean_object* v_head_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
v___x_6_ = lean_string_dec_eq(v_a_1_, v_head_4_);
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
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec_ref(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20));
v___x_52_ = l_Lean_belowSuffix;
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21);
v___x_55_ = l_Lean_brecOnSuffix;
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22);
v___x_58_ = l_Lean_recOnSuffix;
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23);
v___x_61_ = l_Lean_casesOnSuffix;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object* v_decl_88_, lean_object* v_a_89_){
_start:
{
uint8_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = l_Lean_Name_hasMacroScopes(v_decl_88_);
v___x_92_ = 1;
if (v___x_91_ == 0)
{
uint8_t v___x_93_; 
v___x_93_ = l_Lean_Name_isInternal(v_decl_88_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v_env_95_; uint8_t v___x_96_; 
v___x_94_ = lean_st_ref_get(v_a_89_);
v_env_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref_n(v_env_95_, 2);
lean_dec(v___x_94_);
lean_inc(v_decl_88_);
v___x_96_ = lean_is_reserved_name(v_env_95_, v_decl_88_);
if (v___x_96_ == 0)
{
if (lean_obj_tag(v_decl_88_) == 1)
{
lean_object* v_pre_97_; lean_object* v_str_98_; uint8_t v___y_100_; lean_object* v___x_148_; lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_242_; 
v_pre_97_ = lean_ctor_get(v_decl_88_, 0);
lean_inc_n(v_pre_97_, 2);
v_str_98_ = lean_ctor_get(v_decl_88_, 1);
lean_inc_ref(v_str_98_);
lean_dec_ref_known(v_decl_88_, 2);
v___x_148_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_pre_97_, v_a_89_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_242_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_242_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_242_;
goto v_resetjp_150_;
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0));
v___x_102_ = l_Lean_Name_str___override(v_pre_97_, v___x_101_);
lean_inc(v___x_102_);
lean_inc_ref(v_env_95_);
v___x_103_ = l_Lean_Environment_find_x3f(v_env_95_, v___x_102_, v___y_100_);
if (lean_obj_tag(v___x_103_) == 1)
{
lean_object* v_val_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_145_; 
v_val_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_145_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_145_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_val_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_145_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
if (lean_obj_tag(v_val_104_) == 5)
{
lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_139_; 
lean_del_object(v___x_106_);
v_isSharedCheck_139_ = !lean_is_exclusive(v_val_104_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v_val_104_, 0);
lean_dec(v_unused_140_);
v___x_109_ = v_val_104_;
v_isShared_110_ = v_isSharedCheck_139_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_val_104_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_139_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1));
v___x_112_ = lean_string_dec_eq(v_str_98_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = l_Lean_casesOnSuffix;
v___x_114_ = lean_string_dec_eq(v_str_98_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2));
v___x_116_ = lean_string_dec_eq(v_str_98_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = l_Lean_Name_str___override(v___x_102_, v_str_98_);
v___x_118_ = l_Lean_Environment_isConstructor(v_env_95_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_119_ = lean_box(v___x_96_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_119_);
v___x_121_ = v___x_109_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
else
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_box(v___x_92_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_123_);
v___x_125_ = v___x_109_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
else
{
lean_object* v___x_127_; lean_object* v___x_129_; 
lean_dec(v___x_102_);
lean_dec_ref(v_str_98_);
lean_dec_ref(v_env_95_);
v___x_127_ = lean_box(v___x_92_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_127_);
v___x_129_ = v___x_109_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_133_; 
lean_dec(v___x_102_);
lean_dec_ref(v_str_98_);
lean_dec_ref(v_env_95_);
v___x_131_ = lean_box(v___x_92_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_131_);
v___x_133_ = v___x_109_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
lean_object* v___x_135_; lean_object* v___x_137_; 
lean_dec(v___x_102_);
lean_dec_ref(v_str_98_);
lean_dec_ref(v_env_95_);
v___x_135_ = lean_box(v___x_92_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_135_);
v___x_137_ = v___x_109_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v___x_141_; lean_object* v___x_143_; 
lean_dec(v_val_104_);
lean_dec(v___x_102_);
lean_dec_ref(v_str_98_);
lean_dec_ref(v_env_95_);
v___x_141_ = lean_box(v___x_96_);
if (v_isShared_107_ == 0)
{
lean_ctor_set_tag(v___x_106_, 0);
lean_ctor_set(v___x_106_, 0, v___x_141_);
v___x_143_ = v___x_106_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v___x_103_);
lean_dec(v___x_102_);
lean_dec_ref(v_str_98_);
lean_dec_ref(v_env_95_);
v___x_146_ = lean_box(v___x_96_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
v_resetjp_150_:
{
uint8_t v___y_154_; uint8_t v___y_169_; uint8_t v___y_179_; uint8_t v___y_198_; uint8_t v___x_231_; 
v___x_231_ = lean_unbox(v_a_149_);
lean_dec(v_a_149_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_string_utf8_byte_size(v_str_98_);
v___x_233_ = lean_unsigned_to_nat(6u);
v___x_234_ = lean_nat_dec_le(v___x_233_, v___x_232_);
if (v___x_234_ == 0)
{
goto v___jp_222_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_235_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39));
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_string_memcmp(v_str_98_, v___x_235_, v___x_236_, v___x_236_, v___x_233_);
if (v___x_237_ == 0)
{
goto v___jp_222_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_238_ = lean_box(v___x_92_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_240_ = lean_box(v___x_92_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
v___jp_153_:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24);
v___x_156_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_str_98_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_box(0);
lean_inc_ref(v_str_98_);
v___x_158_ = l_Lean_Name_str___override(v___x_157_, v_str_98_);
lean_inc(v_pre_97_);
lean_inc_ref(v_env_95_);
v___x_159_ = l_Lean_isSubobjectField_x3f(v_env_95_, v_pre_97_, v___x_158_);
if (lean_obj_tag(v___x_159_) == 1)
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_dec_ref_known(v___x_159_, 1);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_160_ = lean_box(v___x_92_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_160_);
v___x_162_ = v___x_151_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_dec(v___x_159_);
lean_del_object(v___x_151_);
v___y_100_ = v___y_154_;
goto v___jp_99_;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_164_ = lean_box(v___x_92_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_164_);
v___x_166_ = v___x_151_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = lean_string_utf8_byte_size(v_str_98_);
v___x_171_ = lean_unsigned_to_nat(6u);
v___x_172_ = lean_nat_dec_le(v___x_171_, v___x_170_);
if (v___x_172_ == 0)
{
v___y_154_ = v___y_169_;
goto v___jp_153_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25));
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_string_memcmp(v_str_98_, v___x_173_, v___x_174_, v___x_174_, v___x_171_);
if (v___x_175_ == 0)
{
v___y_154_ = v___y_169_;
goto v___jp_153_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_176_ = lean_box(v___x_92_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
v___jp_178_:
{
lean_object* v___x_180_; 
lean_inc(v_pre_97_);
lean_inc_ref(v_env_95_);
v___x_180_ = l_Lean_Environment_find_x3f(v_env_95_, v_pre_97_, v___y_179_);
if (lean_obj_tag(v___x_180_) == 1)
{
lean_object* v_val_181_; 
v_val_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v___x_180_, 1);
if (lean_obj_tag(v_val_181_) == 5)
{
lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_195_; 
v_isSharedCheck_195_ = !lean_is_exclusive(v_val_181_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_val_181_, 0);
lean_dec(v_unused_196_);
v___x_183_ = v_val_181_;
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_val_181_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = lean_string_utf8_byte_size(v_str_98_);
v___x_186_ = lean_unsigned_to_nat(7u);
v___x_187_ = lean_nat_dec_le(v___x_186_, v___x_185_);
if (v___x_187_ == 0)
{
lean_del_object(v___x_183_);
v___y_169_ = v___y_179_;
goto v___jp_168_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_188_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26));
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_string_memcmp(v_str_98_, v___x_188_, v___x_189_, v___x_189_, v___x_186_);
if (v___x_190_ == 0)
{
lean_del_object(v___x_183_);
v___y_169_ = v___y_179_;
goto v___jp_168_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_191_ = lean_box(v___x_92_);
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 0);
lean_ctor_set(v___x_183_, 0, v___x_191_);
v___x_193_ = v___x_183_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
else
{
lean_dec(v_val_181_);
lean_del_object(v___x_151_);
v___y_100_ = v___y_179_;
goto v___jp_99_;
}
}
else
{
lean_dec(v___x_180_);
lean_del_object(v___x_151_);
v___y_100_ = v___y_179_;
goto v___jp_99_;
}
}
v___jp_197_:
{
uint8_t v___x_199_; 
lean_inc(v_pre_97_);
lean_inc_ref(v_env_95_);
v___x_199_ = l_Lean_Environment_isConstructor(v_env_95_, v_pre_97_);
if (v___x_199_ == 0)
{
v___y_179_ = v___y_198_;
goto v___jp_178_;
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35));
v___x_201_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_str_98_, v___x_200_);
if (v___x_201_ == 0)
{
v___y_179_ = v___x_201_;
goto v___jp_178_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_202_ = lean_box(v___x_92_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
}
v___jp_204_:
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_string_utf8_byte_size(v_str_98_);
v___x_206_ = lean_unsigned_to_nat(6u);
v___x_207_ = lean_nat_dec_le(v___x_206_, v___x_205_);
if (v___x_207_ == 0)
{
v___y_198_ = v___x_207_;
goto v___jp_197_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_208_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36));
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_string_memcmp(v_str_98_, v___x_208_, v___x_209_, v___x_209_, v___x_206_);
if (v___x_210_ == 0)
{
v___y_198_ = v___x_210_;
goto v___jp_197_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_211_ = lean_box(v___x_92_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
}
v___jp_213_:
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_string_utf8_byte_size(v_str_98_);
v___x_215_ = lean_unsigned_to_nat(7u);
v___x_216_ = lean_nat_dec_le(v___x_215_, v___x_214_);
if (v___x_216_ == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37));
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_string_memcmp(v_str_98_, v___x_217_, v___x_218_, v___x_218_, v___x_215_);
if (v___x_219_ == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_220_ = lean_box(v___x_92_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
}
v___jp_222_:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_string_utf8_byte_size(v_str_98_);
v___x_224_ = lean_unsigned_to_nat(6u);
v___x_225_ = lean_nat_dec_le(v___x_224_, v___x_223_);
if (v___x_225_ == 0)
{
goto v___jp_213_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38));
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_string_memcmp(v_str_98_, v___x_226_, v___x_227_, v___x_227_, v___x_224_);
if (v___x_228_ == 0)
{
goto v___jp_213_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_del_object(v___x_151_);
lean_dec_ref(v_str_98_);
lean_dec(v_pre_97_);
lean_dec_ref(v_env_95_);
v___x_229_ = lean_box(v___x_92_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
}
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v_env_95_);
lean_dec(v_decl_88_);
v___x_243_ = lean_box(v___x_96_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref(v_env_95_);
lean_dec(v_decl_88_);
v___x_245_ = lean_box(v___x_92_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_decl_88_);
v___x_247_ = lean_box(v___x_92_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_decl_88_);
v___x_249_ = lean_box(v___x_92_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___boxed(lean_object* v_decl_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_251_, v_a_252_);
lean_dec(v_a_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal(lean_object* v_decl_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_255_, v_a_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___boxed(lean_object* v_decl_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_isAutoDeclOrPrivate__Internal(v_decl_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
return v_res_264_;
}
}
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_AutoDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AutoDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_AutoDecl(builtin);
}
#ifdef __cplusplus
}
#endif
