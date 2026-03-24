// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.OrderInsts
// Imports: public import Lean.Meta.Tactic.Grind.SynthInstance
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Grind_grind_debug;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LawfulOrderLT"};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 67, 105, 183, 31, 31, 114)}};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "type has `LE` and `LT`, but the `LT` instance is not lawful, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "IsPreorder"};
static const lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 213, 76, 156, 147, 68, 250, 139)}};
static const lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "type has `LE`, but is not a preorder, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "type has `LE`, but is not a partial order, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "type has `LE`, but is not a linear order, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "IsLinearPreorder"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 98, 195, 196, 59, 47, 77, 198)}};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "type has `LE`, but is not a linear preorder, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3));
v___x_22_ = l_Lean_stringToMessageData(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object* v_u_23_, lean_object* v_type_24_, lean_object* v_ltInst_x3f_25_, lean_object* v_leInst_x3f_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
if (lean_obj_tag(v_ltInst_x3f_25_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_26_) == 1)
{
lean_object* v_val_40_; lean_object* v_val_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v_lawfulOrderLTType_46_; lean_object* v___x_47_; 
v_val_40_ = lean_ctor_get(v_ltInst_x3f_25_, 0);
lean_inc(v_val_40_);
lean_dec_ref(v_ltInst_x3f_25_);
v_val_41_ = lean_ctor_get(v_leInst_x3f_26_, 0);
lean_inc(v_val_41_);
lean_dec_ref(v_leInst_x3f_26_);
v___x_42_ = ((lean_object*)(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2));
v___x_43_ = lean_box(0);
v___x_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_44_, 0, v_u_23_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = l_Lean_mkConst(v___x_42_, v___x_44_);
v_lawfulOrderLTType_46_ = l_Lean_mkApp3(v___x_45_, v_type_24_, v_val_40_, v_val_41_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
lean_inc_ref(v_lawfulOrderLTType_46_);
v___x_47_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_lawfulOrderLTType_46_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
if (lean_obj_tag(v_a_48_) == 1)
{
lean_dec_ref(v_a_48_);
lean_dec_ref(v_lawfulOrderLTType_46_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v___x_47_;
}
else
{
lean_object* v___x_49_; 
lean_dec(v_a_48_);
lean_dec_ref(v___x_47_);
v___x_49_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_28_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; uint8_t v_verbose_51_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v___x_49_);
v_verbose_51_ = lean_ctor_get_uint8(v_a_50_, sizeof(void*)*11 + 15);
lean_dec(v_a_50_);
if (v_verbose_51_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_46_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
goto v___jp_37_;
}
else
{
lean_object* v_options_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v_options_52_ = lean_ctor_get(v_a_34_, 2);
v___x_53_ = l_Lean_Meta_Grind_grind_debug;
v___x_54_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_52_, v___x_53_);
if (v___x_54_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_46_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
goto v___jp_37_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = lean_obj_once(&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4, &l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4);
v___x_56_ = l_Lean_indentExpr(v_lawfulOrderLTType_46_);
v___x_57_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = l_Lean_Meta_Grind_reportIssue(v___x_57_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_dec_ref(v___x_58_);
goto v___jp_37_;
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec_ref(v_lawfulOrderLTType_46_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
v_a_67_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_49_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_49_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
else
{
lean_dec_ref(v_lawfulOrderLTType_46_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v___x_47_;
}
}
else
{
lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_leInst_x3f_26_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v_isSharedCheck_82_ = !lean_is_exclusive(v_ltInst_x3f_25_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v_ltInst_x3f_25_, 0);
lean_dec(v_unused_83_);
v___x_76_ = v_ltInst_x3f_25_;
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
else
{
lean_dec(v_ltInst_x3f_25_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_box(0);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 0);
lean_ctor_set(v___x_76_, 0, v___x_78_);
v___x_80_ = v___x_76_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_leInst_x3f_26_);
lean_dec(v_ltInst_x3f_25_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
v___jp_37_:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_box(0);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(lean_object* v_u_86_, lean_object* v_type_87_, lean_object* v_ltInst_x3f_88_, lean_object* v_leInst_x3f_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_86_, v_type_87_, v_ltInst_x3f_88_, v_leInst_x3f_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(lean_object* v_u_101_, lean_object* v_type_102_, lean_object* v_ltInst_x3f_103_, lean_object* v_leInst_x3f_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_101_, v_type_102_, v_ltInst_x3f_103_, v_leInst_x3f_104_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___boxed(lean_object* v_u_117_, lean_object* v_type_118_, lean_object* v_ltInst_x3f_119_, lean_object* v_leInst_x3f_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(v_u_117_, v_type_118_, v_ltInst_x3f_119_, v_leInst_x3f_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec(v_a_121_);
return v_res_132_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2));
v___x_139_ = l_Lean_stringToMessageData(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object* v_u_140_, lean_object* v_type_141_, lean_object* v_leInst_x3f_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_142_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_isPreorderType_161_; lean_object* v___x_162_; 
v_val_156_ = lean_ctor_get(v_leInst_x3f_142_, 0);
lean_inc(v_val_156_);
lean_dec_ref(v_leInst_x3f_142_);
v___x_157_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1));
v___x_158_ = lean_box(0);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v_u_140_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Lean_mkConst(v___x_157_, v___x_159_);
v_isPreorderType_161_ = l_Lean_mkAppB(v___x_160_, v_type_141_, v_val_156_);
lean_inc(v_a_151_);
lean_inc_ref(v_a_150_);
lean_inc(v_a_149_);
lean_inc_ref(v_a_148_);
lean_inc_ref(v_isPreorderType_161_);
v___x_162_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isPreorderType_161_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
if (lean_obj_tag(v_a_163_) == 1)
{
lean_dec_ref(v_a_163_);
lean_dec_ref(v_isPreorderType_161_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v___x_162_;
}
else
{
lean_object* v___x_164_; 
lean_dec(v_a_163_);
lean_dec_ref(v___x_162_);
v___x_164_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_144_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; uint8_t v_verbose_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref(v___x_164_);
v_verbose_166_ = lean_ctor_get_uint8(v_a_165_, sizeof(void*)*11 + 15);
lean_dec(v_a_165_);
if (v_verbose_166_ == 0)
{
lean_dec_ref(v_isPreorderType_161_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
goto v___jp_153_;
}
else
{
lean_object* v_options_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_options_167_ = lean_ctor_get(v_a_150_, 2);
v___x_168_ = l_Lean_Meta_Grind_grind_debug;
v___x_169_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_dec_ref(v_isPreorderType_161_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
goto v___jp_153_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3);
v___x_171_ = l_Lean_indentExpr(v_isPreorderType_161_);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = l_Lean_Meta_Grind_reportIssue(v___x_172_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_dec_ref(v___x_173_);
goto v___jp_153_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_isPreorderType_161_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
v_a_182_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_164_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_164_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPreorderType_161_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v___x_162_;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_leInst_x3f_142_);
lean_dec_ref(v_type_141_);
lean_dec(v_u_140_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
v___jp_153_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(lean_object* v_u_192_, lean_object* v_type_193_, lean_object* v_leInst_x3f_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_192_, v_type_193_, v_leInst_x3f_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f(lean_object* v_u_206_, lean_object* v_type_207_, lean_object* v_leInst_x3f_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_206_, v_type_207_, v_leInst_x3f_208_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___boxed(lean_object* v_u_221_, lean_object* v_type_222_, lean_object* v_leInst_x3f_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f(v_u_221_, v_type_222_, v_leInst_x3f_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec(v_a_224_);
return v_res_235_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object* v_u_243_, lean_object* v_type_244_, lean_object* v_leInst_x3f_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_245_) == 1)
{
lean_object* v_val_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_isPartialOrderType_264_; lean_object* v___x_265_; 
v_val_259_ = lean_ctor_get(v_leInst_x3f_245_, 0);
lean_inc(v_val_259_);
lean_dec_ref(v_leInst_x3f_245_);
v___x_260_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1));
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v_u_243_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_Lean_mkConst(v___x_260_, v___x_262_);
v_isPartialOrderType_264_ = l_Lean_mkAppB(v___x_263_, v_type_244_, v_val_259_);
lean_inc(v_a_254_);
lean_inc_ref(v_a_253_);
lean_inc(v_a_252_);
lean_inc_ref(v_a_251_);
lean_inc_ref(v_isPartialOrderType_264_);
v___x_265_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isPartialOrderType_264_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
if (lean_obj_tag(v_a_266_) == 1)
{
lean_dec_ref(v_a_266_);
lean_dec_ref(v_isPartialOrderType_264_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v___x_265_;
}
else
{
lean_object* v___x_267_; 
lean_dec(v_a_266_);
lean_dec_ref(v___x_265_);
v___x_267_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_247_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; uint8_t v_verbose_269_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref(v___x_267_);
v_verbose_269_ = lean_ctor_get_uint8(v_a_268_, sizeof(void*)*11 + 15);
lean_dec(v_a_268_);
if (v_verbose_269_ == 0)
{
lean_dec_ref(v_isPartialOrderType_264_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
goto v___jp_256_;
}
else
{
lean_object* v_options_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_options_270_ = lean_ctor_get(v_a_253_, 2);
v___x_271_ = l_Lean_Meta_Grind_grind_debug;
v___x_272_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_dec_ref(v_isPartialOrderType_264_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
goto v___jp_256_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3);
v___x_274_ = l_Lean_indentExpr(v_isPartialOrderType_264_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = l_Lean_Meta_Grind_reportIssue(v___x_275_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_dec_ref(v___x_276_);
goto v___jp_256_;
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_isPartialOrderType_264_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
v_a_285_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_267_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_267_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPartialOrderType_264_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v___x_265_;
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_leInst_x3f_245_);
lean_dec_ref(v_type_244_);
lean_dec(v_u_243_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
v___jp_256_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(lean_object* v_u_295_, lean_object* v_type_296_, lean_object* v_leInst_x3f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_295_, v_type_296_, v_leInst_x3f_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(lean_object* v_u_309_, lean_object* v_type_310_, lean_object* v_leInst_x3f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_309_, v_type_310_, v_leInst_x3f_311_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___boxed(lean_object* v_u_324_, lean_object* v_type_325_, lean_object* v_leInst_x3f_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(v_u_324_, v_type_325_, v_leInst_x3f_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec(v_a_327_);
return v_res_338_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object* v_u_346_, lean_object* v_type_347_, lean_object* v_leInst_x3f_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_348_) == 1)
{
lean_object* v_val_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_isLinearOrderType_367_; lean_object* v___x_368_; 
v_val_362_ = lean_ctor_get(v_leInst_x3f_348_, 0);
lean_inc(v_val_362_);
lean_dec_ref(v_leInst_x3f_348_);
v___x_363_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1));
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v_u_346_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l_Lean_mkConst(v___x_363_, v___x_365_);
v_isLinearOrderType_367_ = l_Lean_mkAppB(v___x_366_, v_type_347_, v_val_362_);
lean_inc(v_a_357_);
lean_inc_ref(v_a_356_);
lean_inc(v_a_355_);
lean_inc_ref(v_a_354_);
lean_inc_ref(v_isLinearOrderType_367_);
v___x_368_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isLinearOrderType_367_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
if (lean_obj_tag(v_a_369_) == 1)
{
lean_dec_ref(v_a_369_);
lean_dec_ref(v_isLinearOrderType_367_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
return v___x_368_;
}
else
{
lean_object* v___x_370_; 
lean_dec(v_a_369_);
lean_dec_ref(v___x_368_);
v___x_370_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_350_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; uint8_t v_verbose_372_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref(v___x_370_);
v_verbose_372_ = lean_ctor_get_uint8(v_a_371_, sizeof(void*)*11 + 15);
lean_dec(v_a_371_);
if (v_verbose_372_ == 0)
{
lean_dec_ref(v_isLinearOrderType_367_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
goto v___jp_359_;
}
else
{
lean_object* v_options_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_options_373_ = lean_ctor_get(v_a_356_, 2);
v___x_374_ = l_Lean_Meta_Grind_grind_debug;
v___x_375_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_dec_ref(v_isLinearOrderType_367_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
goto v___jp_359_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3);
v___x_377_ = l_Lean_indentExpr(v_isLinearOrderType_367_);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = l_Lean_Meta_Grind_reportIssue(v___x_378_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_dec_ref(v___x_379_);
goto v___jp_359_;
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec_ref(v_isLinearOrderType_367_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
v_a_388_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_370_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_370_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_367_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
return v___x_368_;
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_leInst_x3f_348_);
lean_dec_ref(v_type_347_);
lean_dec(v_u_346_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(lean_object* v_u_398_, lean_object* v_type_399_, lean_object* v_leInst_x3f_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_398_, v_type_399_, v_leInst_x3f_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(lean_object* v_u_412_, lean_object* v_type_413_, lean_object* v_leInst_x3f_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_412_, v_type_413_, v_leInst_x3f_414_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___boxed(lean_object* v_u_427_, lean_object* v_type_428_, lean_object* v_leInst_x3f_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(v_u_427_, v_type_428_, v_leInst_x3f_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec(v_a_430_);
return v_res_441_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2));
v___x_448_ = l_Lean_stringToMessageData(v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object* v_u_449_, lean_object* v_type_450_, lean_object* v_leInst_x3f_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_451_) == 1)
{
lean_object* v_val_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_isLinearOrderType_470_; lean_object* v___x_471_; 
v_val_465_ = lean_ctor_get(v_leInst_x3f_451_, 0);
lean_inc(v_val_465_);
lean_dec_ref(v_leInst_x3f_451_);
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1));
v___x_467_ = lean_box(0);
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v_u_449_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_mkConst(v___x_466_, v___x_468_);
v_isLinearOrderType_470_ = l_Lean_mkAppB(v___x_469_, v_type_450_, v_val_465_);
lean_inc(v_a_460_);
lean_inc_ref(v_a_459_);
lean_inc(v_a_458_);
lean_inc_ref(v_a_457_);
lean_inc_ref(v_isLinearOrderType_470_);
v___x_471_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isLinearOrderType_470_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
if (lean_obj_tag(v_a_472_) == 1)
{
lean_dec_ref(v_a_472_);
lean_dec_ref(v_isLinearOrderType_470_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v___x_471_;
}
else
{
lean_object* v___x_473_; 
lean_dec_ref(v___x_471_);
lean_dec(v_a_472_);
v___x_473_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_453_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; uint8_t v_verbose_475_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
v_verbose_475_ = lean_ctor_get_uint8(v_a_474_, sizeof(void*)*11 + 15);
lean_dec(v_a_474_);
if (v_verbose_475_ == 0)
{
lean_dec_ref(v_isLinearOrderType_470_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
goto v___jp_462_;
}
else
{
lean_object* v_options_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_options_476_ = lean_ctor_get(v_a_459_, 2);
v___x_477_ = l_Lean_Meta_Grind_grind_debug;
v___x_478_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec_ref(v_isLinearOrderType_470_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
goto v___jp_462_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3);
v___x_480_ = l_Lean_indentExpr(v_isLinearOrderType_470_);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Lean_Meta_Grind_reportIssue(v___x_481_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_dec_ref(v___x_482_);
goto v___jp_462_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v_isLinearOrderType_470_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
v_a_491_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_473_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_473_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_470_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v___x_471_;
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_leInst_x3f_451_);
lean_dec_ref(v_type_450_);
lean_dec(v_u_449_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
v___jp_462_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(lean_object* v_u_501_, lean_object* v_type_502_, lean_object* v_leInst_x3f_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_501_, v_type_502_, v_leInst_x3f_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(lean_object* v_u_515_, lean_object* v_type_516_, lean_object* v_leInst_x3f_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_515_, v_type_516_, v_leInst_x3f_517_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___boxed(lean_object* v_u_530_, lean_object* v_type_531_, lean_object* v_leInst_x3f_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(v_u_530_, v_type_531_, v_leInst_x3f_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec(v_a_533_);
return v_res_544_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
}
#ifdef __cplusplus
}
#endif
