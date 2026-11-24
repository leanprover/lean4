// Lean compiler output
// Module: Lake.Formatters.Util.OpaqueType
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lake.Util.OpaqueType import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_fmtDeclarationSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__2_value;
static const lean_string_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nonemptyTypeCmd"};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__3_value;
static const lean_ctor_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__4_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 29, 126, 4, 221, 16, 76, 39)}};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__4_value;
static const lean_string_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__6_value;
static const lean_string_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__7_value;
static const lean_string_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__8_value;
static const lean_ctor_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__0_value;
static const lean_string_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtNonemptyTypeCmd"};
static const lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__1_value;
static const lean_ctor_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 150, 169, 99, 3, 223, 40, 131)}};
static const lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2 = (const lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "hydrateOpaqueTypeCmd"};
static const lean_object* l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 247, 39, 29, 239, 7, 87, 22)}};
static const lean_object* l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtHydrateOpaqueTypeCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtHydrateOpaqueTypeCmd"};
static const lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtNonemptyTypeCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 233, 54, 107, 13, 195, 114, 94)}};
static const lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__0(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5_, 0, v_bs_3_);
return v___x_5_;
}
else
{
lean_object* v_v_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; size_t v___x_9_; size_t v___x_10_; lean_object* v___x_11_; 
v_v_6_ = lean_array_uget(v_bs_3_, v_i_2_);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_7_);
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_2_, v___x_9_);
v___x_11_ = lean_array_uset(v_bs_x27_8_, v_i_2_, v_v_6_);
v_i_2_ = v___x_10_;
v_bs_3_ = v___x_11_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__0___boxed(lean_object* v_sz_13_, lean_object* v_i_14_, lean_object* v_bs_15_){
_start:
{
size_t v_sz_boxed_16_; size_t v_i_boxed_17_; lean_object* v_res_18_; 
v_sz_boxed_16_ = lean_unbox_usize(v_sz_13_);
lean_dec(v_sz_13_);
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__0(v_sz_boxed_16_, v_i_boxed_17_, v_bs_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__1(size_t v_sz_19_, size_t v_i_20_, lean_object* v_bs_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = lean_usize_dec_lt(v_i_20_, v_sz_19_);
if (v___x_22_ == 0)
{
return v_bs_21_;
}
else
{
lean_object* v_v_23_; lean_object* v___x_24_; lean_object* v_bs_x27_25_; size_t v___x_26_; size_t v___x_27_; lean_object* v___x_28_; 
v_v_23_ = lean_array_uget(v_bs_21_, v_i_20_);
v___x_24_ = lean_unsigned_to_nat(0u);
v_bs_x27_25_ = lean_array_uset(v_bs_21_, v_i_20_, v___x_24_);
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_add(v_i_20_, v___x_26_);
v___x_28_ = lean_array_uset(v_bs_x27_25_, v_i_20_, v_v_23_);
v_i_20_ = v___x_27_;
v_bs_21_ = v___x_28_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__1___boxed(lean_object* v_sz_30_, lean_object* v_i_31_, lean_object* v_bs_32_){
_start:
{
size_t v_sz_boxed_33_; size_t v_i_boxed_34_; lean_object* v_res_35_; 
v_sz_boxed_33_ = lean_unbox_usize(v_sz_30_);
lean_dec(v_sz_30_);
v_i_boxed_34_ = lean_unbox_usize(v_i_31_);
lean_dec(v_i_31_);
v_res_35_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__1(v_sz_boxed_33_, v_i_boxed_34_, v_bs_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd(lean_object* v_x_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___y_57_; lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; lean_object* v___y_62_; lean_object* v___y_63_; lean_object* v___y_68_; lean_object* v_visibility_x3f_69_; lean_object* v___y_70_; lean_object* v___y_71_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lake_Formatters_fmtNonemptyTypeCmd___closed__4));
lean_inc(v_x_53_);
v___x_116_ = l_Lean_Syntax_isOfKind(v_x_53_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_x_53_);
v___x_117_ = l_Lean_Fmt_Error_partialFormatter;
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_a_55_);
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v_docComment_x3f_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_133_ = l_Lean_Syntax_getArg(v_x_53_, v___x_119_);
v___x_134_ = l_Lean_Syntax_isNone(v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_133_);
v___x_136_ = l_Lean_Syntax_matchesNull(v___x_133_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v___x_133_);
lean_dec(v_x_53_);
v___x_137_ = l_Lean_Fmt_Error_partialFormatter;
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_a_55_);
return v___x_138_;
}
else
{
lean_object* v_docComment_x3f_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_docComment_x3f_139_ = l_Lean_Syntax_getArg(v___x_133_, v___x_119_);
lean_dec(v___x_133_);
v___x_140_ = ((lean_object*)(l_Lake_Formatters_fmtNonemptyTypeCmd___closed__9));
lean_inc(v_docComment_x3f_139_);
v___x_141_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_docComment_x3f_139_);
lean_dec(v_x_53_);
v___x_142_ = l_Lean_Fmt_Error_partialFormatter;
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_55_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_docComment_x3f_139_);
v_docComment_x3f_121_ = v___x_144_;
v___y_122_ = v_a_54_;
v___y_123_ = v_a_55_;
goto v___jp_120_;
}
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v_docComment_x3f_121_ = v___x_145_;
v___y_122_ = v_a_54_;
v___y_123_ = v_a_55_;
goto v___jp_120_;
}
v___jp_120_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = l_Lean_Syntax_getArg(v_x_53_, v___x_124_);
v___x_126_ = l_Lean_Syntax_isNone(v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
lean_inc(v___x_125_);
v___x_127_ = l_Lean_Syntax_matchesNull(v___x_125_, v___x_124_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v___x_125_);
lean_dec(v_docComment_x3f_121_);
lean_dec(v_x_53_);
v___x_128_ = l_Lean_Fmt_Error_partialFormatter;
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___y_123_);
return v___x_129_;
}
else
{
lean_object* v_visibility_x3f_130_; lean_object* v___x_131_; 
v_visibility_x3f_130_ = l_Lean_Syntax_getArg(v___x_125_, v___x_119_);
lean_dec(v___x_125_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_visibility_x3f_130_);
v___y_68_ = v_docComment_x3f_121_;
v_visibility_x3f_69_ = v___x_131_;
v___y_70_ = v___y_122_;
v___y_71_ = v___y_123_;
goto v___jp_67_;
}
}
else
{
lean_object* v___x_132_; 
lean_dec(v___x_125_);
v___x_132_ = lean_box(0);
v___y_68_ = v_docComment_x3f_121_;
v_visibility_x3f_69_ = v___x_132_;
v___y_70_ = v___y_122_;
v___y_71_ = v___y_123_;
goto v___jp_67_;
}
}
}
v___jp_56_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_mk_empty_array_with_capacity(v___y_57_);
v___x_65_ = lean_array_push(v___x_64_, v___y_63_);
v___x_66_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_59_, v___y_61_, v___x_65_, v___y_58_, v___y_60_, v___y_62_);
lean_dec_ref(v___x_65_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_72_ = lean_unsigned_to_nat(3u);
v___x_73_ = l_Lean_Syntax_getArg(v_x_53_, v___x_72_);
v___x_74_ = ((lean_object*)(l_Lake_Formatters_fmtNonemptyTypeCmd___closed__1));
lean_inc(v___x_73_);
v___x_75_ = l_Lean_Syntax_isOfKind(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v___x_73_);
lean_dec(v_visibility_x3f_69_);
lean_dec(v___y_68_);
lean_dec(v_x_53_);
v___x_76_ = l_Lean_Fmt_Error_partialFormatter;
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___y_71_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; size_t v_sz_81_; size_t v___x_82_; lean_object* v___x_83_; 
v___x_78_ = lean_unsigned_to_nat(4u);
v___x_79_ = l_Lean_Syntax_getArg(v_x_53_, v___x_78_);
v___x_80_ = l_Lean_Syntax_getArgs(v___x_79_);
lean_dec(v___x_79_);
v_sz_81_ = lean_array_size(v___x_80_);
v___x_82_ = ((size_t)0ULL);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__0(v_sz_81_, v___x_82_, v___x_80_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v___x_73_);
lean_dec(v_visibility_x3f_69_);
lean_dec(v___y_68_);
lean_dec(v_x_53_);
v___x_84_ = l_Lean_Fmt_Error_partialFormatter;
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___y_71_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_114_; 
v_val_86_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_114_ == 0)
{
v___x_88_ = v___x_83_;
v_isShared_89_ = v_isSharedCheck_114_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_val_86_);
lean_dec(v___x_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_114_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v_nonemptyTypeTk_91_; size_t v_sz_92_; lean_object* v_binders_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_90_ = lean_unsigned_to_nat(2u);
v_nonemptyTypeTk_91_ = l_Lean_Syntax_getArg(v_x_53_, v___x_90_);
lean_dec(v_x_53_);
v_sz_92_ = lean_array_size(v_val_86_);
v_binders_93_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtNonemptyTypeCmd_spec__1(v_sz_92_, v___x_82_, v_val_86_);
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_array_push(v___x_95_, v_nonemptyTypeTk_91_);
v___x_97_ = lean_box(0);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_73_);
v___x_99_ = v___x_88_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_73_);
v___x_99_ = v_reuseFailAlloc_113_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Fmt_fmtDeclarationSignature(v___x_96_, v___x_97_, v___x_99_, v_binders_93_, v___x_97_, v___x_97_, v___y_70_, v___y_71_);
if (lean_obj_tag(v___x_100_) == 0)
{
if (lean_obj_tag(v_visibility_x3f_69_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
v_a_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_100_, 2);
v___y_57_ = v___x_94_;
v___y_58_ = v_a_101_;
v___y_59_ = v___y_68_;
v___y_60_ = v___y_70_;
v___y_61_ = v___x_97_;
v___y_62_ = v_a_102_;
v___y_63_ = v___x_97_;
goto v___jp_56_;
}
else
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v_val_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_103_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_103_);
v_a_104_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_100_, 2);
v_val_105_ = lean_ctor_get(v_visibility_x3f_69_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v_visibility_x3f_69_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v_visibility_x3f_69_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_val_105_);
lean_dec(v_visibility_x3f_69_);
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
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_val_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
v___y_57_ = v___x_94_;
v___y_58_ = v_a_103_;
v___y_59_ = v___y_68_;
v___y_60_ = v___y_70_;
v___y_61_ = v___x_97_;
v___y_62_ = v_a_104_;
v___y_63_ = v___x_110_;
goto v___jp_56_;
}
}
}
}
else
{
lean_dec(v_visibility_x3f_69_);
lean_dec(v___y_68_);
return v___x_100_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtNonemptyTypeCmd___boxed(lean_object* v_x_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lake_Formatters_fmtNonemptyTypeCmd(v_x_146_, v_a_147_, v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1(){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = l_Lean_Fmt_fmtAttribute;
v___x_158_ = ((lean_object*)(l_Lake_Formatters_fmtNonemptyTypeCmd___closed__4));
v___x_159_ = ((lean_object*)(l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___closed__2));
v___x_160_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtNonemptyTypeCmd___boxed), 3, 0);
v___x_161_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_157_, v___x_158_, v___x_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1___boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1();
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtHydrateOpaqueTypeCmd(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v_visibility_x3f_184_; lean_object* v___y_185_; lean_object* v___y_186_; 
v___x_181_ = ((lean_object*)(l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__1));
lean_inc(v_x_168_);
v___x_182_ = l_Lean_Syntax_isOfKind(v_x_168_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_x_168_);
v___x_241_ = l_Lean_Fmt_Error_partialFormatter;
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_a_170_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l_Lean_Syntax_getArg(v_x_168_, v___x_243_);
v___x_245_ = l_Lean_Syntax_isNone(v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_244_);
v___x_247_ = l_Lean_Syntax_matchesNull(v___x_244_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v___x_244_);
lean_dec(v_x_168_);
v___x_248_ = l_Lean_Fmt_Error_partialFormatter;
v___x_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_a_170_);
return v___x_249_;
}
else
{
lean_object* v_visibility_x3f_250_; lean_object* v___x_251_; 
v_visibility_x3f_250_ = l_Lean_Syntax_getArg(v___x_244_, v___x_243_);
lean_dec(v___x_244_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v_visibility_x3f_250_);
v_visibility_x3f_184_ = v___x_251_;
v___y_185_ = v_a_169_;
v___y_186_ = v_a_170_;
goto v___jp_183_;
}
}
else
{
lean_object* v___x_252_; 
lean_dec(v___x_244_);
v___x_252_ = lean_box(0);
v_visibility_x3f_184_ = v___x_252_;
v___y_185_ = v_a_169_;
v___y_186_ = v_a_170_;
goto v___jp_183_;
}
}
v___jp_171_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_mk_empty_array_with_capacity(v___y_175_);
v___x_179_ = lean_array_push(v___x_178_, v___y_177_);
lean_inc(v___y_174_);
v___x_180_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_174_, v___y_174_, v___x_179_, v___y_176_, v___y_173_, v___y_172_);
lean_dec_ref(v___x_179_);
return v___x_180_;
}
v___jp_183_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_187_ = lean_unsigned_to_nat(2u);
v___x_188_ = l_Lean_Syntax_getArg(v_x_168_, v___x_187_);
v___x_189_ = ((lean_object*)(l_Lake_Formatters_fmtNonemptyTypeCmd___closed__1));
lean_inc(v___x_188_);
v___x_190_ = l_Lean_Syntax_isOfKind(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v___x_188_);
lean_dec(v_visibility_x3f_184_);
lean_dec(v_x_168_);
v___x_191_ = l_Lean_Fmt_Error_partialFormatter;
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___y_186_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(3u);
v___x_194_ = l_Lean_Syntax_getArg(v_x_168_, v___x_193_);
lean_inc(v___x_194_);
v___x_195_ = l_Lean_Syntax_isOfKind(v___x_194_, v___x_189_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec(v___x_194_);
lean_dec(v___x_188_);
lean_dec(v_visibility_x3f_184_);
lean_dec(v_x_168_);
v___x_196_ = l_Lean_Fmt_Error_partialFormatter;
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___y_186_);
return v___x_197_;
}
else
{
lean_object* v___x_198_; lean_object* v_hydrateOpaqueTypeTk_199_; lean_object* v___x_200_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v_hydrateOpaqueTypeTk_199_ = l_Lean_Syntax_getArg(v_x_168_, v___x_198_);
v___x_200_ = l_Lean_Fmt_fmt(v_hydrateOpaqueTypeTk_199_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_a_202_; lean_object* v___x_203_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
v_a_202_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_200_, 2);
v___x_203_ = l_Lean_Fmt_fmt(v___x_188_, v___y_185_, v_a_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v_a_205_; lean_object* v___x_206_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_a_204_);
v_a_205_ = lean_ctor_get(v___x_203_, 1);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_203_, 2);
v___x_206_ = l_Lean_Fmt_fmt(v___x_194_, v___y_185_, v_a_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_args_211_; lean_object* v___x_212_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
v_a_208_ = lean_ctor_get(v___x_206_, 1);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_206_, 2);
v___x_209_ = lean_unsigned_to_nat(4u);
v___x_210_ = l_Lean_Syntax_getArg(v_x_168_, v___x_209_);
lean_dec(v_x_168_);
v_args_211_ = l_Lean_Syntax_getArgs(v___x_210_);
lean_dec(v___x_210_);
v___x_212_ = l_Lean_Fmt_fmtArray___redArg(v_args_211_, v___y_185_, v_a_208_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
v_a_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_212_, 2);
v___x_215_ = lean_mk_empty_array_with_capacity(v___x_193_);
v___x_216_ = lean_array_push(v___x_215_, v_a_201_);
v___x_217_ = lean_array_push(v___x_216_, v_a_204_);
v___x_218_ = lean_array_push(v___x_217_, v_a_207_);
v___x_219_ = l_Array_append___redArg(v___x_218_, v_a_213_);
lean_dec(v_a_213_);
v___x_220_ = 0;
v___x_221_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_221_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_221_, 1, v___x_220_);
lean_ctor_set_uint8(v___x_221_, 2, v___x_220_);
lean_ctor_set_uint8(v___x_221_, 3, v___x_220_);
v___x_222_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_219_, v___x_221_);
v___x_223_ = lean_box(0);
if (lean_obj_tag(v_visibility_x3f_184_) == 0)
{
v___y_172_ = v_a_214_;
v___y_173_ = v___y_185_;
v___y_174_ = v___x_223_;
v___y_175_ = v___x_198_;
v___y_176_ = v___x_222_;
v___y_177_ = v___x_223_;
goto v___jp_171_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_val_224_ = lean_ctor_get(v_visibility_x3f_184_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_visibility_x3f_184_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v_visibility_x3f_184_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_val_224_);
lean_dec(v_visibility_x3f_184_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_val_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
v___y_172_ = v_a_214_;
v___y_173_ = v___y_185_;
v___y_174_ = v___x_223_;
v___y_175_ = v___x_198_;
v___y_176_ = v___x_222_;
v___y_177_ = v___x_229_;
goto v___jp_171_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_a_207_);
lean_dec(v_a_204_);
lean_dec(v_a_201_);
lean_dec(v_visibility_x3f_184_);
v_a_232_ = lean_ctor_get(v___x_212_, 0);
v_a_233_ = lean_ctor_get(v___x_212_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_212_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_inc(v_a_232_);
lean_dec(v___x_212_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_232_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_dec(v_a_204_);
lean_dec(v_a_201_);
lean_dec(v_visibility_x3f_184_);
lean_dec(v_x_168_);
return v___x_206_;
}
}
else
{
lean_dec(v_a_201_);
lean_dec(v___x_194_);
lean_dec(v_visibility_x3f_184_);
lean_dec(v_x_168_);
return v___x_203_;
}
}
else
{
lean_dec(v___x_194_);
lean_dec(v___x_188_);
lean_dec(v_visibility_x3f_184_);
lean_dec(v_x_168_);
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___boxed(lean_object* v_x_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lake_Formatters_fmtHydrateOpaqueTypeCmd(v_x_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1(){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = l_Lean_Fmt_fmtAttribute;
v___x_264_ = ((lean_object*)(l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___closed__1));
v___x_265_ = ((lean_object*)(l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___closed__1));
v___x_266_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtHydrateOpaqueTypeCmd___boxed), 3, 0);
v___x_267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_263_, v___x_264_, v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1___boxed(lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1();
return v_res_269_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Formatters_Util_OpaqueType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtNonemptyTypeCmd___regBuiltin_Lake_Formatters_fmtNonemptyTypeCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Util_OpaqueType_0__Lake_Formatters_fmtHydrateOpaqueTypeCmd___regBuiltin_Lake_Formatters_fmtHydrateOpaqueTypeCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Util_OpaqueType(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Formatters_Util_OpaqueType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Formatters_Util_OpaqueType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Formatters_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Formatters_Util_OpaqueType(builtin);
}
#ifdef __cplusplus
}
#endif
