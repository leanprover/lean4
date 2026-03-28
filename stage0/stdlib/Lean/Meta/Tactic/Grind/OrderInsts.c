// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.OrderInsts
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Sym_sym_debug;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object* v_u_23_, lean_object* v_type_24_, lean_object* v_ltInst_x3f_25_, lean_object* v_leInst_x3f_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
if (lean_obj_tag(v_ltInst_x3f_25_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_26_) == 1)
{
lean_object* v_val_37_; lean_object* v_val_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v_lawfulOrderLTType_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_val_37_ = lean_ctor_get(v_ltInst_x3f_25_, 0);
lean_inc(v_val_37_);
lean_dec_ref(v_ltInst_x3f_25_);
v_val_38_ = lean_ctor_get(v_leInst_x3f_26_, 0);
lean_inc(v_val_38_);
lean_dec_ref(v_leInst_x3f_26_);
v___x_39_ = ((lean_object*)(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2));
v___x_40_ = lean_box(0);
v___x_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_41_, 0, v_u_23_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = l_Lean_mkConst(v___x_39_, v___x_41_);
v_lawfulOrderLTType_43_ = l_Lean_mkApp3(v___x_42_, v_type_24_, v_val_37_, v_val_38_);
v___x_44_ = lean_box(0);
lean_inc_ref(v_lawfulOrderLTType_43_);
v___x_45_ = l_Lean_Meta_synthInstance_x3f(v_lawfulOrderLTType_43_, v___x_44_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_46_);
if (lean_obj_tag(v_a_46_) == 1)
{
lean_dec_ref(v_a_46_);
lean_dec_ref(v_lawfulOrderLTType_43_);
return v___x_45_;
}
else
{
lean_object* v___x_47_; 
lean_dec(v_a_46_);
lean_dec_ref(v___x_45_);
v___x_47_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_27_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; uint8_t v___x_49_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v___x_47_);
v___x_49_ = lean_unbox(v_a_48_);
lean_dec(v_a_48_);
if (v___x_49_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_43_);
goto v___jp_34_;
}
else
{
lean_object* v_options_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v_options_50_ = lean_ctor_get(v_a_31_, 2);
v___x_51_ = l_Lean_Meta_Sym_sym_debug;
v___x_52_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_50_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_43_);
goto v___jp_34_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_obj_once(&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4, &l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4);
v___x_54_ = l_Lean_indentExpr(v_lawfulOrderLTType_43_);
v___x_55_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = l_Lean_Meta_Sym_reportIssue(v___x_55_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_dec_ref(v___x_56_);
goto v___jp_34_;
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_dec_ref(v_lawfulOrderLTType_43_);
v_a_65_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_47_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_47_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
else
{
lean_dec_ref(v_lawfulOrderLTType_43_);
return v___x_45_;
}
}
else
{
lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_80_; 
lean_dec(v_leInst_x3f_26_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v_isSharedCheck_80_ = !lean_is_exclusive(v_ltInst_x3f_25_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v_ltInst_x3f_25_, 0);
lean_dec(v_unused_81_);
v___x_74_ = v_ltInst_x3f_25_;
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
else
{
lean_dec(v_ltInst_x3f_25_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = lean_box(0);
if (v_isShared_75_ == 0)
{
lean_ctor_set_tag(v___x_74_, 0);
lean_ctor_set(v___x_74_, 0, v___x_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_leInst_x3f_26_);
lean_dec(v_ltInst_x3f_25_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
v___jp_34_:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(lean_object* v_u_84_, lean_object* v_type_85_, lean_object* v_ltInst_x3f_86_, lean_object* v_leInst_x3f_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_84_, v_type_85_, v_ltInst_x3f_86_, v_leInst_x3f_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(lean_object* v_u_96_, lean_object* v_type_97_, lean_object* v_ltInst_x3f_98_, lean_object* v_leInst_x3f_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_96_, v_type_97_, v_ltInst_x3f_98_, v_leInst_x3f_99_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___boxed(lean_object* v_u_112_, lean_object* v_type_113_, lean_object* v_ltInst_x3f_114_, lean_object* v_leInst_x3f_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(v_u_112_, v_type_113_, v_ltInst_x3f_114_, v_leInst_x3f_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec(v_a_116_);
return v_res_127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2));
v___x_134_ = l_Lean_stringToMessageData(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object* v_u_135_, lean_object* v_type_136_, lean_object* v_leInst_x3f_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_137_) == 1)
{
lean_object* v_val_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_isPreorderType_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_val_148_ = lean_ctor_get(v_leInst_x3f_137_, 0);
lean_inc(v_val_148_);
lean_dec_ref(v_leInst_x3f_137_);
v___x_149_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1));
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v_u_135_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = l_Lean_mkConst(v___x_149_, v___x_151_);
v_isPreorderType_153_ = l_Lean_mkAppB(v___x_152_, v_type_136_, v_val_148_);
v___x_154_ = lean_box(0);
lean_inc_ref(v_isPreorderType_153_);
v___x_155_ = l_Lean_Meta_synthInstance_x3f(v_isPreorderType_153_, v___x_154_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
if (lean_obj_tag(v_a_156_) == 1)
{
lean_dec_ref(v_a_156_);
lean_dec_ref(v_isPreorderType_153_);
return v___x_155_;
}
else
{
lean_object* v___x_157_; 
lean_dec(v_a_156_);
lean_dec_ref(v___x_155_);
v___x_157_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_138_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; uint8_t v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v___x_157_);
v___x_159_ = lean_unbox(v_a_158_);
lean_dec(v_a_158_);
if (v___x_159_ == 0)
{
lean_dec_ref(v_isPreorderType_153_);
goto v___jp_145_;
}
else
{
lean_object* v_options_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_options_160_ = lean_ctor_get(v_a_142_, 2);
v___x_161_ = l_Lean_Meta_Sym_sym_debug;
v___x_162_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_dec_ref(v_isPreorderType_153_);
goto v___jp_145_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3);
v___x_164_ = l_Lean_indentExpr(v_isPreorderType_153_);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_Meta_Sym_reportIssue(v___x_165_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_dec_ref(v___x_166_);
goto v___jp_145_;
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec_ref(v_isPreorderType_153_);
v_a_175_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_157_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_157_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPreorderType_153_);
return v___x_155_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_leInst_x3f_137_);
lean_dec_ref(v_type_136_);
lean_dec(v_u_135_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
v___jp_145_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(lean_object* v_u_185_, lean_object* v_type_186_, lean_object* v_leInst_x3f_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_185_, v_type_186_, v_leInst_x3f_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f(lean_object* v_u_196_, lean_object* v_type_197_, lean_object* v_leInst_x3f_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_196_, v_type_197_, v_leInst_x3f_198_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___boxed(lean_object* v_u_211_, lean_object* v_type_212_, lean_object* v_leInst_x3f_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f(v_u_211_, v_type_212_, v_leInst_x3f_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec(v_a_214_);
return v_res_225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object* v_u_233_, lean_object* v_type_234_, lean_object* v_leInst_x3f_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_235_) == 1)
{
lean_object* v_val_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_isPartialOrderType_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_val_246_ = lean_ctor_get(v_leInst_x3f_235_, 0);
lean_inc(v_val_246_);
lean_dec_ref(v_leInst_x3f_235_);
v___x_247_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1));
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_249_, 0, v_u_233_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = l_Lean_mkConst(v___x_247_, v___x_249_);
v_isPartialOrderType_251_ = l_Lean_mkAppB(v___x_250_, v_type_234_, v_val_246_);
v___x_252_ = lean_box(0);
lean_inc_ref(v_isPartialOrderType_251_);
v___x_253_ = l_Lean_Meta_synthInstance_x3f(v_isPartialOrderType_251_, v___x_252_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
if (lean_obj_tag(v_a_254_) == 1)
{
lean_dec_ref(v_a_254_);
lean_dec_ref(v_isPartialOrderType_251_);
return v___x_253_;
}
else
{
lean_object* v___x_255_; 
lean_dec(v_a_254_);
lean_dec_ref(v___x_253_);
v___x_255_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_236_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; uint8_t v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_255_);
v___x_257_ = lean_unbox(v_a_256_);
lean_dec(v_a_256_);
if (v___x_257_ == 0)
{
lean_dec_ref(v_isPartialOrderType_251_);
goto v___jp_243_;
}
else
{
lean_object* v_options_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_options_258_ = lean_ctor_get(v_a_240_, 2);
v___x_259_ = l_Lean_Meta_Sym_sym_debug;
v___x_260_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec_ref(v_isPartialOrderType_251_);
goto v___jp_243_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3);
v___x_262_ = l_Lean_indentExpr(v_isPartialOrderType_251_);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_Meta_Sym_reportIssue(v___x_263_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_dec_ref(v___x_264_);
goto v___jp_243_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_isPartialOrderType_251_);
v_a_273_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_255_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_255_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPartialOrderType_251_);
return v___x_253_;
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_leInst_x3f_235_);
lean_dec_ref(v_type_234_);
lean_dec(v_u_233_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
v___jp_243_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_box(0);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(lean_object* v_u_283_, lean_object* v_type_284_, lean_object* v_leInst_x3f_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_283_, v_type_284_, v_leInst_x3f_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(lean_object* v_u_294_, lean_object* v_type_295_, lean_object* v_leInst_x3f_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_294_, v_type_295_, v_leInst_x3f_296_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___boxed(lean_object* v_u_309_, lean_object* v_type_310_, lean_object* v_leInst_x3f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(v_u_309_, v_type_310_, v_leInst_x3f_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec(v_a_312_);
return v_res_323_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object* v_u_331_, lean_object* v_type_332_, lean_object* v_leInst_x3f_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_333_) == 1)
{
lean_object* v_val_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_isLinearOrderType_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_val_344_ = lean_ctor_get(v_leInst_x3f_333_, 0);
lean_inc(v_val_344_);
lean_dec_ref(v_leInst_x3f_333_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1));
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_347_, 0, v_u_331_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = l_Lean_mkConst(v___x_345_, v___x_347_);
v_isLinearOrderType_349_ = l_Lean_mkAppB(v___x_348_, v_type_332_, v_val_344_);
v___x_350_ = lean_box(0);
lean_inc_ref(v_isLinearOrderType_349_);
v___x_351_ = l_Lean_Meta_synthInstance_x3f(v_isLinearOrderType_349_, v___x_350_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
if (lean_obj_tag(v_a_352_) == 1)
{
lean_dec_ref(v_a_352_);
lean_dec_ref(v_isLinearOrderType_349_);
return v___x_351_;
}
else
{
lean_object* v___x_353_; 
lean_dec_ref(v___x_351_);
lean_dec(v_a_352_);
v___x_353_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_334_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; uint8_t v___x_355_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_353_);
v___x_355_ = lean_unbox(v_a_354_);
lean_dec(v_a_354_);
if (v___x_355_ == 0)
{
lean_dec_ref(v_isLinearOrderType_349_);
goto v___jp_341_;
}
else
{
lean_object* v_options_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_options_356_ = lean_ctor_get(v_a_338_, 2);
v___x_357_ = l_Lean_Meta_Sym_sym_debug;
v___x_358_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_dec_ref(v_isLinearOrderType_349_);
goto v___jp_341_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3);
v___x_360_ = l_Lean_indentExpr(v_isLinearOrderType_349_);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = l_Lean_Meta_Sym_reportIssue(v___x_361_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_dec_ref(v___x_362_);
goto v___jp_341_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_isLinearOrderType_349_);
v_a_371_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_353_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_353_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_349_);
return v___x_351_;
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_leInst_x3f_333_);
lean_dec_ref(v_type_332_);
lean_dec(v_u_331_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
v___jp_341_:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(lean_object* v_u_381_, lean_object* v_type_382_, lean_object* v_leInst_x3f_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_381_, v_type_382_, v_leInst_x3f_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(lean_object* v_u_392_, lean_object* v_type_393_, lean_object* v_leInst_x3f_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_392_, v_type_393_, v_leInst_x3f_394_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___boxed(lean_object* v_u_407_, lean_object* v_type_408_, lean_object* v_leInst_x3f_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(v_u_407_, v_type_408_, v_leInst_x3f_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec(v_a_410_);
return v_res_421_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object* v_u_429_, lean_object* v_type_430_, lean_object* v_leInst_x3f_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_431_) == 1)
{
lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_isLinearOrderType_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_val_442_ = lean_ctor_get(v_leInst_x3f_431_, 0);
lean_inc(v_val_442_);
lean_dec_ref(v_leInst_x3f_431_);
v___x_443_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1));
v___x_444_ = lean_box(0);
v___x_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_445_, 0, v_u_429_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_mkConst(v___x_443_, v___x_445_);
v_isLinearOrderType_447_ = l_Lean_mkAppB(v___x_446_, v_type_430_, v_val_442_);
v___x_448_ = lean_box(0);
lean_inc_ref(v_isLinearOrderType_447_);
v___x_449_ = l_Lean_Meta_synthInstance_x3f(v_isLinearOrderType_447_, v___x_448_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
if (lean_obj_tag(v_a_450_) == 1)
{
lean_dec_ref(v_a_450_);
lean_dec_ref(v_isLinearOrderType_447_);
return v___x_449_;
}
else
{
lean_object* v___x_451_; 
lean_dec_ref(v___x_449_);
lean_dec(v_a_450_);
v___x_451_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_432_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; uint8_t v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___x_451_);
v___x_453_ = lean_unbox(v_a_452_);
lean_dec(v_a_452_);
if (v___x_453_ == 0)
{
lean_dec_ref(v_isLinearOrderType_447_);
goto v___jp_439_;
}
else
{
lean_object* v_options_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_options_454_ = lean_ctor_get(v_a_436_, 2);
v___x_455_ = l_Lean_Meta_Sym_sym_debug;
v___x_456_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_isLinearOrderType_447_);
goto v___jp_439_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3);
v___x_458_ = l_Lean_indentExpr(v_isLinearOrderType_447_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_Meta_Sym_reportIssue(v___x_459_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_dec_ref(v___x_460_);
goto v___jp_439_;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_isLinearOrderType_447_);
v_a_469_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_451_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_451_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_447_);
return v___x_449_;
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_leInst_x3f_431_);
lean_dec_ref(v_type_430_);
lean_dec(v_u_429_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
v___jp_439_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(lean_object* v_u_479_, lean_object* v_type_480_, lean_object* v_leInst_x3f_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_479_, v_type_480_, v_leInst_x3f_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(lean_object* v_u_490_, lean_object* v_type_491_, lean_object* v_leInst_x3f_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_490_, v_type_491_, v_leInst_x3f_492_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___boxed(lean_object* v_u_505_, lean_object* v_type_506_, lean_object* v_leInst_x3f_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(v_u_505_, v_type_506_, v_leInst_x3f_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec(v_a_508_);
return v_res_519_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
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
