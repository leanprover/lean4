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
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
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
lean_dec_ref_known(v_ltInst_x3f_25_, 1);
v_val_38_ = lean_ctor_get(v_leInst_x3f_26_, 0);
lean_inc(v_val_38_);
lean_dec_ref_known(v_leInst_x3f_26_, 1);
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
lean_dec_ref_known(v_a_46_, 1);
lean_dec_ref(v_lawfulOrderLTType_43_);
return v___x_45_;
}
else
{
lean_object* v___x_47_; 
lean_dec_ref_known(v___x_45_, 1);
lean_dec(v_a_46_);
v___x_47_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_27_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; uint8_t v_verbose_49_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_47_, 1);
v_verbose_49_ = lean_ctor_get_uint8(v_a_48_, 0);
lean_dec(v_a_48_);
if (v_verbose_49_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_43_);
goto v___jp_34_;
}
else
{
lean_object* v_toCold_50_; lean_object* v_options_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_toCold_50_ = lean_ctor_get(v_a_31_, 0);
v_options_51_ = lean_ctor_get(v_toCold_50_, 2);
v___x_52_ = l_Lean_Meta_Sym_sym_debug;
v___x_53_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_51_, v___x_52_);
if (v___x_53_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_43_);
goto v___jp_34_;
}
else
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4, &l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4);
v___x_55_ = l_Lean_indentExpr(v_lawfulOrderLTType_43_);
v___x_56_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = l_Lean_Meta_Sym_reportIssue(v___x_56_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_dec_ref_known(v___x_57_, 1);
goto v___jp_34_;
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
}
else
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
lean_dec_ref(v_lawfulOrderLTType_43_);
v_a_66_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_47_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_47_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_a_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
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
lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
lean_dec(v_leInst_x3f_26_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v_isSharedCheck_81_ = !lean_is_exclusive(v_ltInst_x3f_25_);
if (v_isSharedCheck_81_ == 0)
{
lean_object* v_unused_82_; 
v_unused_82_ = lean_ctor_get(v_ltInst_x3f_25_, 0);
lean_dec(v_unused_82_);
v___x_75_ = v_ltInst_x3f_25_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_dec(v_ltInst_x3f_25_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_box(0);
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 0);
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_leInst_x3f_26_);
lean_dec(v_ltInst_x3f_25_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(lean_object* v_u_85_, lean_object* v_type_86_, lean_object* v_ltInst_x3f_87_, lean_object* v_leInst_x3f_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_85_, v_type_86_, v_ltInst_x3f_87_, v_leInst_x3f_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(lean_object* v_u_97_, lean_object* v_type_98_, lean_object* v_ltInst_x3f_99_, lean_object* v_leInst_x3f_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_97_, v_type_98_, v_ltInst_x3f_99_, v_leInst_x3f_100_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___boxed(lean_object* v_u_113_, lean_object* v_type_114_, lean_object* v_ltInst_x3f_115_, lean_object* v_leInst_x3f_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(v_u_113_, v_type_114_, v_ltInst_x3f_115_, v_leInst_x3f_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec(v_a_117_);
return v_res_128_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2));
v___x_135_ = l_Lean_stringToMessageData(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object* v_u_136_, lean_object* v_type_137_, lean_object* v_leInst_x3f_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_138_) == 1)
{
lean_object* v_val_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_isPreorderType_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_val_149_ = lean_ctor_get(v_leInst_x3f_138_, 0);
lean_inc(v_val_149_);
lean_dec_ref_known(v_leInst_x3f_138_, 1);
v___x_150_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1));
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v_u_136_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_mkConst(v___x_150_, v___x_152_);
v_isPreorderType_154_ = l_Lean_mkAppB(v___x_153_, v_type_137_, v_val_149_);
v___x_155_ = lean_box(0);
lean_inc_ref(v_isPreorderType_154_);
v___x_156_ = l_Lean_Meta_synthInstance_x3f(v_isPreorderType_154_, v___x_155_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
if (lean_obj_tag(v_a_157_) == 1)
{
lean_dec_ref_known(v_a_157_, 1);
lean_dec_ref(v_isPreorderType_154_);
return v___x_156_;
}
else
{
lean_object* v___x_158_; 
lean_dec(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_139_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; uint8_t v_verbose_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v_verbose_160_ = lean_ctor_get_uint8(v_a_159_, 0);
lean_dec(v_a_159_);
if (v_verbose_160_ == 0)
{
lean_dec_ref(v_isPreorderType_154_);
goto v___jp_146_;
}
else
{
lean_object* v_toCold_161_; lean_object* v_options_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_toCold_161_ = lean_ctor_get(v_a_143_, 0);
v_options_162_ = lean_ctor_get(v_toCold_161_, 2);
v___x_163_ = l_Lean_Meta_Sym_sym_debug;
v___x_164_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec_ref(v_isPreorderType_154_);
goto v___jp_146_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3);
v___x_166_ = l_Lean_indentExpr(v_isPreorderType_154_);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Lean_Meta_Sym_reportIssue(v___x_167_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_dec_ref_known(v___x_168_, 1);
goto v___jp_146_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec_ref(v_isPreorderType_154_);
v_a_177_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_158_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_158_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPreorderType_154_);
return v___x_156_;
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_leInst_x3f_138_);
lean_dec_ref(v_type_137_);
lean_dec(v_u_136_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(lean_object* v_u_187_, lean_object* v_type_188_, lean_object* v_leInst_x3f_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_187_, v_type_188_, v_leInst_x3f_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f(lean_object* v_u_198_, lean_object* v_type_199_, lean_object* v_leInst_x3f_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_198_, v_type_199_, v_leInst_x3f_200_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___boxed(lean_object* v_u_213_, lean_object* v_type_214_, lean_object* v_leInst_x3f_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f(v_u_213_, v_type_214_, v_leInst_x3f_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec(v_a_216_);
return v_res_227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object* v_u_235_, lean_object* v_type_236_, lean_object* v_leInst_x3f_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_237_) == 1)
{
lean_object* v_val_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_isPartialOrderType_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_val_248_ = lean_ctor_get(v_leInst_x3f_237_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v_leInst_x3f_237_, 1);
v___x_249_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1));
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v_u_235_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Lean_mkConst(v___x_249_, v___x_251_);
v_isPartialOrderType_253_ = l_Lean_mkAppB(v___x_252_, v_type_236_, v_val_248_);
v___x_254_ = lean_box(0);
lean_inc_ref(v_isPartialOrderType_253_);
v___x_255_ = l_Lean_Meta_synthInstance_x3f(v_isPartialOrderType_253_, v___x_254_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
if (lean_obj_tag(v_a_256_) == 1)
{
lean_dec_ref_known(v_a_256_, 1);
lean_dec_ref(v_isPartialOrderType_253_);
return v___x_255_;
}
else
{
lean_object* v___x_257_; 
lean_dec(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
v___x_257_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_238_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; uint8_t v_verbose_259_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v_verbose_259_ = lean_ctor_get_uint8(v_a_258_, 0);
lean_dec(v_a_258_);
if (v_verbose_259_ == 0)
{
lean_dec_ref(v_isPartialOrderType_253_);
goto v___jp_245_;
}
else
{
lean_object* v_toCold_260_; lean_object* v_options_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_toCold_260_ = lean_ctor_get(v_a_242_, 0);
v_options_261_ = lean_ctor_get(v_toCold_260_, 2);
v___x_262_ = l_Lean_Meta_Sym_sym_debug;
v___x_263_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_dec_ref(v_isPartialOrderType_253_);
goto v___jp_245_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3);
v___x_265_ = l_Lean_indentExpr(v_isPartialOrderType_253_);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_Meta_Sym_reportIssue(v___x_266_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_dec_ref_known(v___x_267_, 1);
goto v___jp_245_;
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_isPartialOrderType_253_);
v_a_276_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_257_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_257_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPartialOrderType_253_);
return v___x_255_;
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec(v_leInst_x3f_237_);
lean_dec_ref(v_type_236_);
lean_dec(v_u_235_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
v___jp_245_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(lean_object* v_u_286_, lean_object* v_type_287_, lean_object* v_leInst_x3f_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_286_, v_type_287_, v_leInst_x3f_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(lean_object* v_u_297_, lean_object* v_type_298_, lean_object* v_leInst_x3f_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_297_, v_type_298_, v_leInst_x3f_299_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___boxed(lean_object* v_u_312_, lean_object* v_type_313_, lean_object* v_leInst_x3f_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(v_u_312_, v_type_313_, v_leInst_x3f_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec(v_a_315_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object* v_u_334_, lean_object* v_type_335_, lean_object* v_leInst_x3f_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_336_) == 1)
{
lean_object* v_val_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_isLinearOrderType_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_val_347_ = lean_ctor_get(v_leInst_x3f_336_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v_leInst_x3f_336_, 1);
v___x_348_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1));
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v_u_334_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = l_Lean_mkConst(v___x_348_, v___x_350_);
v_isLinearOrderType_352_ = l_Lean_mkAppB(v___x_351_, v_type_335_, v_val_347_);
v___x_353_ = lean_box(0);
lean_inc_ref(v_isLinearOrderType_352_);
v___x_354_ = l_Lean_Meta_synthInstance_x3f(v_isLinearOrderType_352_, v___x_353_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
if (lean_obj_tag(v_a_355_) == 1)
{
lean_dec_ref_known(v_a_355_, 1);
lean_dec_ref(v_isLinearOrderType_352_);
return v___x_354_;
}
else
{
lean_object* v___x_356_; 
lean_dec(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_337_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; uint8_t v_verbose_358_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v_verbose_358_ = lean_ctor_get_uint8(v_a_357_, 0);
lean_dec(v_a_357_);
if (v_verbose_358_ == 0)
{
lean_dec_ref(v_isLinearOrderType_352_);
goto v___jp_344_;
}
else
{
lean_object* v_toCold_359_; lean_object* v_options_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_toCold_359_ = lean_ctor_get(v_a_341_, 0);
v_options_360_ = lean_ctor_get(v_toCold_359_, 2);
v___x_361_ = l_Lean_Meta_Sym_sym_debug;
v___x_362_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_dec_ref(v_isLinearOrderType_352_);
goto v___jp_344_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_363_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3);
v___x_364_ = l_Lean_indentExpr(v_isLinearOrderType_352_);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l_Lean_Meta_Sym_reportIssue(v___x_365_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_dec_ref_known(v___x_366_, 1);
goto v___jp_344_;
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_isLinearOrderType_352_);
v_a_375_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_356_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_356_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_352_);
return v___x_354_;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_leInst_x3f_336_);
lean_dec_ref(v_type_335_);
lean_dec(v_u_334_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
v___jp_344_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_box(0);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(lean_object* v_u_385_, lean_object* v_type_386_, lean_object* v_leInst_x3f_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_385_, v_type_386_, v_leInst_x3f_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(lean_object* v_u_396_, lean_object* v_type_397_, lean_object* v_leInst_x3f_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_396_, v_type_397_, v_leInst_x3f_398_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___boxed(lean_object* v_u_411_, lean_object* v_type_412_, lean_object* v_leInst_x3f_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(v_u_411_, v_type_412_, v_leInst_x3f_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec(v_a_414_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2));
v___x_432_ = l_Lean_stringToMessageData(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object* v_u_433_, lean_object* v_type_434_, lean_object* v_leInst_x3f_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_435_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_isLinearOrderType_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_val_446_ = lean_ctor_get(v_leInst_x3f_435_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_leInst_x3f_435_, 1);
v___x_447_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1));
v___x_448_ = lean_box(0);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v_u_433_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_mkConst(v___x_447_, v___x_449_);
v_isLinearOrderType_451_ = l_Lean_mkAppB(v___x_450_, v_type_434_, v_val_446_);
v___x_452_ = lean_box(0);
lean_inc_ref(v_isLinearOrderType_451_);
v___x_453_ = l_Lean_Meta_synthInstance_x3f(v_isLinearOrderType_451_, v___x_452_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
if (lean_obj_tag(v_a_454_) == 1)
{
lean_dec_ref_known(v_a_454_, 1);
lean_dec_ref(v_isLinearOrderType_451_);
return v___x_453_;
}
else
{
lean_object* v___x_455_; 
lean_dec(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v___x_455_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_436_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; uint8_t v_verbose_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v_verbose_457_ = lean_ctor_get_uint8(v_a_456_, 0);
lean_dec(v_a_456_);
if (v_verbose_457_ == 0)
{
lean_dec_ref(v_isLinearOrderType_451_);
goto v___jp_443_;
}
else
{
lean_object* v_toCold_458_; lean_object* v_options_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_toCold_458_ = lean_ctor_get(v_a_440_, 0);
v_options_459_ = lean_ctor_get(v_toCold_458_, 2);
v___x_460_ = l_Lean_Meta_Sym_sym_debug;
v___x_461_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec_ref(v_isLinearOrderType_451_);
goto v___jp_443_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3);
v___x_463_ = l_Lean_indentExpr(v_isLinearOrderType_451_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_Meta_Sym_reportIssue(v___x_464_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_dec_ref_known(v___x_465_, 1);
goto v___jp_443_;
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
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
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_isLinearOrderType_451_);
v_a_474_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_455_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_455_);
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
else
{
lean_dec_ref(v_isLinearOrderType_451_);
return v___x_453_;
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_leInst_x3f_435_);
lean_dec_ref(v_type_434_);
lean_dec(v_u_433_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
v___jp_443_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_box(0);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(lean_object* v_u_484_, lean_object* v_type_485_, lean_object* v_leInst_x3f_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_484_, v_type_485_, v_leInst_x3f_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(lean_object* v_u_495_, lean_object* v_type_496_, lean_object* v_leInst_x3f_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_495_, v_type_496_, v_leInst_x3f_497_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___boxed(lean_object* v_u_510_, lean_object* v_type_511_, lean_object* v_leInst_x3f_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(v_u_510_, v_type_511_, v_leInst_x3f_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec(v_a_513_);
return v_res_524_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
