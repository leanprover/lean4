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
uint8_t l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_a_1_, v_x_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0___boxed(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_a_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec_ref(v_a_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20));
v___x_53_ = l_Lean_belowSuffix;
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21);
v___x_56_ = l_Lean_brecOnSuffix;
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22);
v___x_59_ = l_Lean_recOnSuffix;
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23);
v___x_62_ = l_Lean_casesOnSuffix;
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
return v___x_63_;
}
}
lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object* v_decl_89_, lean_object* v_a_90_){
_start:
{
uint8_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = l_Lean_Name_hasMacroScopes(v_decl_89_);
v___x_93_ = 1;
if (v___x_92_ == 0)
{
uint8_t v___x_94_; 
v___x_94_ = l_Lean_Name_isInternal(v_decl_89_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v_env_96_; uint8_t v___x_97_; 
v___x_95_ = lean_st_ref_get(v_a_90_);
v_env_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref_n(v_env_96_, 2);
lean_dec(v___x_95_);
lean_inc(v_decl_89_);
v___x_97_ = lean_is_reserved_name(v_env_96_, v_decl_89_);
if (v___x_97_ == 0)
{
if (lean_obj_tag(v_decl_89_) == 1)
{
lean_object* v_pre_98_; lean_object* v_str_99_; uint8_t v___y_101_; lean_object* v___x_149_; lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_243_; 
v_pre_98_ = lean_ctor_get(v_decl_89_, 0);
lean_inc_n(v_pre_98_, 2);
v_str_99_ = lean_ctor_get(v_decl_89_, 1);
lean_inc_ref(v_str_99_);
lean_dec_ref_known(v_decl_89_, 2);
v___x_149_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_pre_98_, v_a_90_);
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_243_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_243_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_243_;
goto v_resetjp_151_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0));
v___x_103_ = l_Lean_Name_str___override(v_pre_98_, v___x_102_);
lean_inc(v___x_103_);
lean_inc_ref(v_env_96_);
v___x_104_ = l_Lean_Environment_find_x3f(v_env_96_, v___x_103_, v___y_101_);
if (lean_obj_tag(v___x_104_) == 1)
{
lean_object* v_val_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_146_; 
v_val_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_146_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_146_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_val_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_146_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
if (lean_obj_tag(v_val_105_) == 5)
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_140_; 
lean_del_object(v___x_107_);
v_isSharedCheck_140_ = !lean_is_exclusive(v_val_105_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_val_105_, 0);
lean_dec(v_unused_141_);
v___x_110_ = v_val_105_;
v_isShared_111_ = v_isSharedCheck_140_;
goto v_resetjp_109_;
}
else
{
lean_dec(v_val_105_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_140_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1));
v___x_113_ = lean_string_dec_eq(v_str_99_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = l_Lean_casesOnSuffix;
v___x_115_ = lean_string_dec_eq(v_str_99_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2));
v___x_117_ = lean_string_dec_eq(v_str_99_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = l_Lean_Name_str___override(v___x_103_, v_str_99_);
v___x_119_ = l_Lean_Environment_isConstructor(v_env_96_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = lean_box(v___x_97_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 0);
lean_ctor_set(v___x_110_, 0, v___x_120_);
v___x_122_ = v___x_110_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
else
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_box(v___x_93_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 0);
lean_ctor_set(v___x_110_, 0, v___x_124_);
v___x_126_ = v___x_110_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec(v___x_103_);
lean_dec_ref(v_str_99_);
lean_dec_ref(v_env_96_);
v___x_128_ = lean_box(v___x_93_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 0);
lean_ctor_set(v___x_110_, 0, v___x_128_);
v___x_130_ = v___x_110_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_dec(v___x_103_);
lean_dec_ref(v_str_99_);
lean_dec_ref(v_env_96_);
v___x_132_ = lean_box(v___x_93_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 0);
lean_ctor_set(v___x_110_, 0, v___x_132_);
v___x_134_ = v___x_110_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_138_; 
lean_dec(v___x_103_);
lean_dec_ref(v_str_99_);
lean_dec_ref(v_env_96_);
v___x_136_ = lean_box(v___x_93_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 0);
lean_ctor_set(v___x_110_, 0, v___x_136_);
v___x_138_ = v___x_110_;
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
}
else
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec(v_val_105_);
lean_dec(v___x_103_);
lean_dec_ref(v_str_99_);
lean_dec_ref(v_env_96_);
v___x_142_ = lean_box(v___x_97_);
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 0);
lean_ctor_set(v___x_107_, 0, v___x_142_);
v___x_144_ = v___x_107_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
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
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v___x_104_);
lean_dec(v___x_103_);
lean_dec_ref(v_str_99_);
lean_dec_ref(v_env_96_);
v___x_147_ = lean_box(v___x_97_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
v_resetjp_151_:
{
uint8_t v___y_155_; uint8_t v___y_170_; uint8_t v___y_180_; uint8_t v___y_199_; uint8_t v___x_232_; 
v___x_232_ = lean_unbox(v_a_150_);
lean_dec(v_a_150_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_233_ = lean_string_utf8_byte_size(v_str_99_);
v___x_234_ = lean_unsigned_to_nat(6u);
v___x_235_ = lean_nat_dec_le(v___x_234_, v___x_233_);
if (v___x_235_ == 0)
{
goto v___jp_223_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39));
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_string_memcmp(v_str_99_, v___x_236_, v___x_237_, v___x_237_, v___x_234_);
if (v___x_238_ == 0)
{
goto v___jp_223_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_239_ = lean_box(v___x_93_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_241_ = lean_box(v___x_93_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
v___jp_154_:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24);
v___x_157_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_str_99_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_box(0);
lean_inc_ref(v_str_99_);
v___x_159_ = l_Lean_Name_str___override(v___x_158_, v_str_99_);
lean_inc(v_pre_98_);
lean_inc_ref(v_env_96_);
v___x_160_ = l_Lean_isSubobjectField_x3f(v_env_96_, v_pre_98_, v___x_159_);
if (lean_obj_tag(v___x_160_) == 1)
{
lean_object* v___x_161_; lean_object* v___x_163_; 
lean_dec_ref_known(v___x_160_, 1);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_161_ = lean_box(v___x_93_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_161_);
v___x_163_ = v___x_152_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
lean_dec(v___x_160_);
lean_del_object(v___x_152_);
v___y_101_ = v___y_155_;
goto v___jp_100_;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_165_ = lean_box(v___x_93_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_165_);
v___x_167_ = v___x_152_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_171_ = lean_string_utf8_byte_size(v_str_99_);
v___x_172_ = lean_unsigned_to_nat(6u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v___x_171_);
if (v___x_173_ == 0)
{
v___y_155_ = v___y_170_;
goto v___jp_154_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25));
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_string_memcmp(v_str_99_, v___x_174_, v___x_175_, v___x_175_, v___x_172_);
if (v___x_176_ == 0)
{
v___y_155_ = v___y_170_;
goto v___jp_154_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_177_ = lean_box(v___x_93_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
}
v___jp_179_:
{
lean_object* v___x_181_; 
lean_inc(v_pre_98_);
lean_inc_ref(v_env_96_);
v___x_181_ = l_Lean_Environment_find_x3f(v_env_96_, v_pre_98_, v___y_180_);
if (lean_obj_tag(v___x_181_) == 1)
{
lean_object* v_val_182_; 
v_val_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v___x_181_, 1);
if (lean_obj_tag(v_val_182_) == 5)
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_196_; 
v_isSharedCheck_196_ = !lean_is_exclusive(v_val_182_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v_val_182_, 0);
lean_dec(v_unused_197_);
v___x_184_ = v_val_182_;
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_val_182_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_string_utf8_byte_size(v_str_99_);
v___x_187_ = lean_unsigned_to_nat(7u);
v___x_188_ = lean_nat_dec_le(v___x_187_, v___x_186_);
if (v___x_188_ == 0)
{
lean_del_object(v___x_184_);
v___y_170_ = v___y_180_;
goto v___jp_169_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_189_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26));
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_string_memcmp(v_str_99_, v___x_189_, v___x_190_, v___x_190_, v___x_187_);
if (v___x_191_ == 0)
{
lean_del_object(v___x_184_);
v___y_170_ = v___y_180_;
goto v___jp_169_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_194_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_192_ = lean_box(v___x_93_);
if (v_isShared_185_ == 0)
{
lean_ctor_set_tag(v___x_184_, 0);
lean_ctor_set(v___x_184_, 0, v___x_192_);
v___x_194_ = v___x_184_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
else
{
lean_dec(v_val_182_);
lean_del_object(v___x_152_);
v___y_101_ = v___y_180_;
goto v___jp_100_;
}
}
else
{
lean_dec(v___x_181_);
lean_del_object(v___x_152_);
v___y_101_ = v___y_180_;
goto v___jp_100_;
}
}
v___jp_198_:
{
uint8_t v___x_200_; 
lean_inc(v_pre_98_);
lean_inc_ref(v_env_96_);
v___x_200_ = l_Lean_Environment_isConstructor(v_env_96_, v_pre_98_);
if (v___x_200_ == 0)
{
v___y_180_ = v___y_199_;
goto v___jp_179_;
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35));
v___x_202_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_str_99_, v___x_201_);
if (v___x_202_ == 0)
{
v___y_180_ = v___x_202_;
goto v___jp_179_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_203_ = lean_box(v___x_93_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
v___jp_205_:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_string_utf8_byte_size(v_str_99_);
v___x_207_ = lean_unsigned_to_nat(6u);
v___x_208_ = lean_nat_dec_le(v___x_207_, v___x_206_);
if (v___x_208_ == 0)
{
v___y_199_ = v___x_208_;
goto v___jp_198_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36));
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_string_memcmp(v_str_99_, v___x_209_, v___x_210_, v___x_210_, v___x_207_);
if (v___x_211_ == 0)
{
v___y_199_ = v___x_211_;
goto v___jp_198_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_212_ = lean_box(v___x_93_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_215_ = lean_string_utf8_byte_size(v_str_99_);
v___x_216_ = lean_unsigned_to_nat(7u);
v___x_217_ = lean_nat_dec_le(v___x_216_, v___x_215_);
if (v___x_217_ == 0)
{
goto v___jp_205_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37));
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_string_memcmp(v_str_99_, v___x_218_, v___x_219_, v___x_219_, v___x_216_);
if (v___x_220_ == 0)
{
goto v___jp_205_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_221_ = lean_box(v___x_93_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
}
v___jp_223_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = lean_string_utf8_byte_size(v_str_99_);
v___x_225_ = lean_unsigned_to_nat(6u);
v___x_226_ = lean_nat_dec_le(v___x_225_, v___x_224_);
if (v___x_226_ == 0)
{
goto v___jp_214_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_227_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38));
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_string_memcmp(v_str_99_, v___x_227_, v___x_228_, v___x_228_, v___x_225_);
if (v___x_229_ == 0)
{
goto v___jp_214_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_str_99_);
lean_dec(v_pre_98_);
lean_dec_ref(v_env_96_);
v___x_230_ = lean_box(v___x_93_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_env_96_);
lean_dec(v_decl_89_);
v___x_244_ = lean_box(v___x_97_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v_env_96_);
lean_dec(v_decl_89_);
v___x_246_ = lean_box(v___x_93_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_decl_89_);
v___x_248_ = lean_box(v___x_93_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v_decl_89_);
v___x_250_ = lean_box(v___x_93_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT void l_Lean_isAutoDeclOrPrivate__Internal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_89_ = stack[0].m_obj;
lean_object* v_a_90_ = stack[1].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_89_, v_a_90_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___boxed(lean_object* v_decl_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_253_, v_a_254_);
lean_dec(v_a_254_);
return v_res_256_;
}
}
lean_object* l_Lean_isAutoDeclOrPrivate__Internal(lean_object* v_decl_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_257_, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT void l_Lean_isAutoDeclOrPrivate__Internal_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_257_ = stack[0].m_obj;
lean_object* v_a_258_ = stack[1].m_obj;
lean_object* v_a_259_ = stack[2].m_obj;
lean_object* v_res_262_;
v_res_262_ = l_Lean_isAutoDeclOrPrivate__Internal(v_decl_257_, v_a_258_, v_a_259_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___boxed(lean_object* v_decl_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_isAutoDeclOrPrivate__Internal(v_decl_263_, v_a_264_, v_a_265_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_267_;
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
