// Lean compiler output
// Module: Lean.Elab.BuiltinDo.If
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.BuiltinDo.Basic
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_withDuplicableCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doIfLet"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 227, 73, 225, 0, 143, 195, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doIfLetPure"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value),LEAN_SCALAR_PTR_LITERAL(30, 29, 142, 71, 96, 53, 139, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doIfLetBind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value),LEAN_SCALAR_PTR_LITERAL(251, 203, 116, 140, 48, 138, 26, 199)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expandDoIf"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 129, 97, 131, 243, 145, 63, 99)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "If the given syntax is a `doIf`, return an equivalent `doIf` that has an `else` but no `else if`s or\n`if let`s.\n"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "else branch of if with condition {cond}"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "then branch of if with condition {cond}"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabDoIf"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 50, 230, 41, 148, 150, 129, 146)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(uint8_t v___x_1_, lean_object* v_____do__lift_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2_, v___x_1_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___y_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0___boxed(lean_object* v___x_7_, lean_object* v_____do__lift_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v___x_34972__boxed_11_; lean_object* v_res_12_; 
v___x_34972__boxed_11_ = lean_unbox(v___x_7_);
v_res_12_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_34972__boxed_11_, v_____do__lift_8_, v___y_9_, v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v_____do__lift_8_);
return v_res_12_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Array_mkArray0(lean_box(0));
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(uint8_t v___x_107_, lean_object* v_as_108_, size_t v_sz_109_, size_t v_i_110_, lean_object* v_b_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_e_115_; lean_object* v___y_116_; uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_lt(v_i_110_, v_sz_109_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_b_111_);
lean_ctor_set(v___x_123_, 1, v___y_113_);
return v___x_123_;
}
else
{
lean_object* v_a_124_; lean_object* v_fst_125_; lean_object* v_snd_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_316_; 
v_a_124_ = lean_array_uget(v_as_108_, v_i_110_);
v_fst_125_ = lean_ctor_get(v_a_124_, 0);
v_snd_126_ = lean_ctor_get(v_a_124_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_124_);
if (v_isSharedCheck_316_ == 0)
{
v___x_128_ = v_a_124_;
v_isShared_129_ = v_isSharedCheck_316_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_snd_126_);
lean_inc(v_fst_125_);
lean_dec(v_a_124_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_316_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_fst_130_; lean_object* v_snd_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_315_; 
v_fst_130_ = lean_ctor_get(v_b_111_, 0);
v_snd_131_ = lean_ctor_get(v_b_111_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_b_111_);
if (v_isSharedCheck_315_ == 0)
{
v___x_133_ = v_b_111_;
v_isShared_134_ = v_isSharedCheck_315_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_snd_131_);
lean_inc(v_fst_130_);
lean_dec(v_b_111_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_315_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_e_139_; lean_object* v___y_140_; lean_object* v___y_141_; uint8_t v___x_293_; 
v___x_135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_293_ = lean_unbox(v_snd_131_);
lean_dec(v_snd_131_);
if (v___x_293_ == 0)
{
lean_object* v_ref_294_; lean_object* v___x_295_; 
v_ref_294_ = lean_ctor_get(v___y_112_, 5);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_107_, v_ref_294_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc_n(v_a_296_, 4);
v_a_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc(v_a_297_);
lean_dec_ref(v___x_295_);
v___x_298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_301_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v_a_296_);
lean_ctor_set(v___x_302_, 1, v___x_299_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
v___x_303_ = l_Lean_Syntax_node2(v_a_296_, v___x_300_, v_fst_130_, v___x_302_);
v___x_304_ = l_Lean_Syntax_node1(v_a_296_, v___x_299_, v___x_303_);
v___x_305_ = l_Lean_Syntax_node1(v_a_296_, v___x_298_, v___x_304_);
v_e_139_ = v___x_305_;
v___y_140_ = v___y_112_;
v___y_141_ = v_a_297_;
goto v___jp_138_;
}
else
{
lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_del_object(v___x_133_);
lean_dec(v_fst_130_);
lean_del_object(v___x_128_);
lean_dec(v_snd_126_);
lean_dec(v_fst_125_);
v_a_306_ = lean_ctor_get(v___x_295_, 0);
v_a_307_ = lean_ctor_get(v___x_295_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_295_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_inc(v_a_306_);
lean_dec(v___x_295_);
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
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_306_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_a_307_);
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
v_e_139_ = v_fst_130_;
v___y_140_ = v___y_112_;
v___y_141_ = v___y_113_;
goto v___jp_138_;
}
v___jp_138_:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(v_fst_125_);
v___x_143_ = l_Lean_Syntax_isOfKind(v_fst_125_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(v_fst_125_);
v___x_145_ = l_Lean_Syntax_isOfKind(v_fst_125_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_dec(v_e_139_);
lean_del_object(v___x_133_);
lean_del_object(v___x_128_);
lean_dec(v_snd_126_);
lean_dec(v_fst_125_);
v___x_146_ = l_Lean_Macro_throwUnsupported___redArg(v___y_141_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v_a_148_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
v_a_148_ = lean_ctor_get(v___x_146_, 1);
lean_inc(v_a_148_);
lean_dec_ref(v___x_146_);
v_e_115_ = v_a_147_;
v___y_116_ = v_a_148_;
goto v___jp_114_;
}
else
{
lean_object* v_a_149_; lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_149_ = lean_ctor_get(v___x_146_, 0);
v_a_150_ = lean_ctor_get(v___x_146_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_146_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_inc(v_a_149_);
lean_dec(v___x_146_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_149_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_object* v_ref_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v_ref_158_ = lean_ctor_get(v___y_140_, 5);
v___x_159_ = l_Lean_SourceInfo_fromRef(v_ref_158_, v___x_107_);
v___x_160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(v___x_159_);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 2);
lean_ctor_set(v___x_133_, 1, v___x_160_);
lean_ctor_set(v___x_133_, 0, v___x_159_);
v___x_162_ = v___x_133_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_174_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(v___x_159_);
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 2);
lean_ctor_set(v___x_128_, 1, v___x_163_);
lean_ctor_set(v___x_128_, 0, v___x_159_);
v___x_165_ = v___x_128_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_173_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v___x_159_, 3);
v___x_168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_159_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
v___x_169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_159_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Lean_Syntax_node2(v___x_159_, v___x_166_, v___x_170_, v_e_139_);
v___x_172_ = l_Lean_Syntax_node6(v___x_159_, v___x_135_, v___x_162_, v_fst_125_, v___x_165_, v_snd_126_, v___x_168_, v___x_171_);
v_e_115_ = v___x_172_;
v___y_116_ = v___y_141_;
goto v___jp_114_;
}
}
}
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_175_ = l_Lean_Syntax_getArg(v_fst_125_, v___x_136_);
v___x_176_ = l_Lean_Syntax_getArg(v_fst_125_, v___x_137_);
lean_dec(v_fst_125_);
v___x_177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(v___x_176_);
v___x_178_ = l_Lean_Syntax_isOfKind(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(v___x_176_);
v___x_180_ = l_Lean_Syntax_isOfKind(v___x_176_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec(v___x_176_);
lean_dec(v___x_175_);
lean_dec(v_e_139_);
lean_del_object(v___x_133_);
lean_del_object(v___x_128_);
lean_dec(v_snd_126_);
v___x_181_ = l_Lean_Macro_throwUnsupported___redArg(v___y_141_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v_a_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
v_a_183_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_a_183_);
lean_dec_ref(v___x_181_);
v_e_115_ = v_a_182_;
v___y_116_ = v_a_183_;
goto v___jp_114_;
}
else
{
lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_184_ = lean_ctor_get(v___x_181_, 0);
v_a_185_ = lean_ctor_get(v___x_181_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_181_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_inc(v_a_184_);
lean_dec(v___x_181_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_ref_193_; lean_object* v___x_194_; 
v_ref_193_ = lean_ctor_get(v___y_140_, 5);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_107_, v_ref_193_, v___y_140_, v___y_141_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc_n(v_a_195_, 2);
v_a_196_ = lean_ctor_get(v___x_194_, 1);
lean_inc(v_a_196_);
lean_dec_ref(v___x_194_);
v___x_197_ = l_Lean_Syntax_getArg(v___x_176_, v___x_136_);
lean_dec(v___x_176_);
v___x_198_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 2);
lean_ctor_set(v___x_133_, 1, v___x_199_);
lean_ctor_set(v___x_133_, 0, v_a_195_);
v___x_201_ = v___x_133_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_195_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_235_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_203_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_195_, 2);
v___x_204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_204_, 0, v_a_195_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
v___x_205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 2);
lean_ctor_set(v___x_128_, 1, v___x_207_);
lean_ctor_set(v___x_128_, 0, v_a_195_);
v___x_209_ = v___x_128_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_195_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_234_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_inc_n(v_a_195_, 16);
v___x_210_ = l_Lean_Syntax_node2(v_a_195_, v___x_206_, v___x_209_, v___x_197_);
lean_inc_ref_n(v___x_204_, 3);
v___x_211_ = l_Lean_Syntax_node2(v_a_195_, v___x_205_, v___x_204_, v___x_210_);
v___x_212_ = l_Lean_Syntax_node1(v_a_195_, v___x_202_, v___x_211_);
v___x_213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v_a_195_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v_a_195_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_Syntax_node1(v_a_195_, v___x_202_, v___x_175_);
v___x_220_ = l_Lean_Syntax_node1(v_a_195_, v___x_202_, v___x_219_);
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v_a_195_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
lean_inc_ref(v___x_222_);
lean_inc_ref(v___x_218_);
v___x_223_ = l_Lean_Syntax_node4(v_a_195_, v___x_216_, v___x_218_, v___x_220_, v___x_222_, v_snd_126_);
v___x_224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v_a_195_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_Syntax_node1(v_a_195_, v___x_224_, v___x_226_);
v___x_228_ = l_Lean_Syntax_node1(v_a_195_, v___x_202_, v___x_227_);
v___x_229_ = l_Lean_Syntax_node1(v_a_195_, v___x_202_, v___x_228_);
v___x_230_ = l_Lean_Syntax_node4(v_a_195_, v___x_216_, v___x_218_, v___x_229_, v___x_222_, v_e_139_);
v___x_231_ = l_Lean_Syntax_node2(v_a_195_, v___x_202_, v___x_223_, v___x_230_);
v___x_232_ = l_Lean_Syntax_node1(v_a_195_, v___x_215_, v___x_231_);
v___x_233_ = l_Lean_Syntax_node7(v_a_195_, v___x_198_, v___x_201_, v___x_204_, v___x_204_, v___x_204_, v___x_212_, v___x_214_, v___x_232_);
v_e_115_ = v___x_233_;
v___y_116_ = v_a_196_;
goto v___jp_114_;
}
}
}
else
{
lean_object* v_a_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v___x_176_);
lean_dec(v___x_175_);
lean_dec(v_e_139_);
lean_del_object(v___x_133_);
lean_del_object(v___x_128_);
lean_dec(v_snd_126_);
v_a_236_ = lean_ctor_get(v___x_194_, 0);
v_a_237_ = lean_ctor_get(v___x_194_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_194_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_inc(v_a_236_);
lean_dec(v___x_194_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
else
{
lean_object* v_ref_245_; lean_object* v___x_246_; 
v_ref_245_ = lean_ctor_get(v___y_140_, 5);
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_107_, v_ref_245_, v___y_140_, v___y_141_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_n(v_a_247_, 2);
v_a_248_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_a_248_);
lean_dec_ref(v___x_246_);
v___x_249_ = l_Lean_Syntax_getArg(v___x_176_, v___x_136_);
lean_dec(v___x_176_);
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 2);
lean_ctor_set(v___x_133_, 1, v___x_251_);
lean_ctor_set(v___x_133_, 0, v_a_247_);
v___x_253_ = v___x_133_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_247_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_251_);
v___x_253_ = v_reuseFailAlloc_283_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_247_, 4);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v_a_247_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
lean_ctor_set(v___x_256_, 2, v___x_255_);
v___x_257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref(v___x_256_);
v___x_258_ = l_Lean_Syntax_node2(v_a_247_, v___x_257_, v___x_256_, v___x_249_);
v___x_259_ = l_Lean_Syntax_node1(v_a_247_, v___x_254_, v___x_258_);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 2);
lean_ctor_set(v___x_128_, 1, v___x_260_);
lean_ctor_set(v___x_128_, 0, v_a_247_);
v___x_262_ = v___x_128_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_247_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_282_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
lean_inc_n(v_a_247_, 12);
v___x_266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_266_, 0, v_a_247_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_Syntax_node1(v_a_247_, v___x_254_, v___x_175_);
v___x_268_ = l_Lean_Syntax_node1(v_a_247_, v___x_254_, v___x_267_);
v___x_269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_270_, 0, v_a_247_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_inc_ref(v___x_270_);
lean_inc_ref(v___x_266_);
v___x_271_ = l_Lean_Syntax_node4(v_a_247_, v___x_264_, v___x_266_, v___x_268_, v___x_270_, v_snd_126_);
v___x_272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_247_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Syntax_node1(v_a_247_, v___x_272_, v___x_274_);
v___x_276_ = l_Lean_Syntax_node1(v_a_247_, v___x_254_, v___x_275_);
v___x_277_ = l_Lean_Syntax_node1(v_a_247_, v___x_254_, v___x_276_);
v___x_278_ = l_Lean_Syntax_node4(v_a_247_, v___x_264_, v___x_266_, v___x_277_, v___x_270_, v_e_139_);
v___x_279_ = l_Lean_Syntax_node2(v_a_247_, v___x_254_, v___x_271_, v___x_278_);
v___x_280_ = l_Lean_Syntax_node1(v_a_247_, v___x_263_, v___x_279_);
lean_inc_ref_n(v___x_256_, 2);
v___x_281_ = l_Lean_Syntax_node7(v_a_247_, v___x_250_, v___x_253_, v___x_256_, v___x_256_, v___x_256_, v___x_259_, v___x_262_, v___x_280_);
v_e_115_ = v___x_281_;
v___y_116_ = v_a_248_;
goto v___jp_114_;
}
}
}
else
{
lean_object* v_a_284_; lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v___x_176_);
lean_dec(v___x_175_);
lean_dec(v_e_139_);
lean_del_object(v___x_133_);
lean_del_object(v___x_128_);
lean_dec(v_snd_126_);
v_a_284_ = lean_ctor_get(v___x_246_, 0);
v_a_285_ = lean_ctor_get(v___x_246_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_246_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_inc(v_a_284_);
lean_dec(v___x_246_);
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
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_284_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_a_285_);
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
}
}
}
}
v___jp_114_:
{
lean_object* v___x_117_; lean_object* v___x_118_; size_t v___x_119_; size_t v___x_120_; 
v___x_117_ = lean_box(v___x_107_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_e_115_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_add(v_i_110_, v___x_119_);
v_i_110_ = v___x_120_;
v_b_111_ = v___x_118_;
v___y_113_ = v___y_116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___boxed(lean_object* v___x_317_, lean_object* v_as_318_, lean_object* v_sz_319_, lean_object* v_i_320_, lean_object* v_b_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v___x_35223__boxed_324_; size_t v_sz_boxed_325_; size_t v_i_boxed_326_; lean_object* v_res_327_; 
v___x_35223__boxed_324_ = lean_unbox(v___x_317_);
v_sz_boxed_325_ = lean_unbox_usize(v_sz_319_);
lean_dec(v_sz_319_);
v_i_boxed_326_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_35223__boxed_324_, v_as_318_, v_sz_boxed_325_, v_i_boxed_326_, v_b_321_, v___y_322_, v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec_ref(v_as_318_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(lean_object* v_____do__lift_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = 0;
v___x_332_ = l_Lean_SourceInfo_fromRef(v_____do__lift_328_, v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___y_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0___boxed(lean_object* v_____do__lift_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_____do__lift_334_, v___y_335_, v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v_____do__lift_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(lean_object* v_as_338_, size_t v_sz_339_, size_t v_i_340_, lean_object* v_b_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_e_345_; lean_object* v___y_346_; uint8_t v___x_353_; 
v___x_353_ = lean_usize_dec_lt(v_i_340_, v_sz_339_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_b_341_);
lean_ctor_set(v___x_354_, 1, v___y_343_);
return v___x_354_;
}
else
{
lean_object* v_a_355_; lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_547_; 
v_a_355_ = lean_array_uget(v_as_338_, v_i_340_);
v_fst_356_ = lean_ctor_get(v_a_355_, 0);
v_snd_357_ = lean_ctor_get(v_a_355_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_a_355_);
if (v_isSharedCheck_547_ == 0)
{
v___x_359_ = v_a_355_;
v_isShared_360_ = v_isSharedCheck_547_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snd_357_);
lean_inc(v_fst_356_);
lean_dec(v_a_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_547_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_546_; 
v_fst_361_ = lean_ctor_get(v_b_341_, 0);
v_snd_362_ = lean_ctor_get(v_b_341_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_b_341_);
if (v_isSharedCheck_546_ == 0)
{
v___x_364_ = v_b_341_;
v_isShared_365_ = v_isSharedCheck_546_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_snd_362_);
lean_inc(v_fst_361_);
lean_dec(v_b_341_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_546_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_e_370_; lean_object* v___y_371_; lean_object* v___y_372_; uint8_t v___x_524_; 
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_unbox(v_snd_362_);
lean_dec(v_snd_362_);
if (v___x_524_ == 0)
{
lean_object* v_ref_525_; lean_object* v___x_526_; 
v_ref_525_ = lean_ctor_get(v___y_342_, 5);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_525_, v___y_342_, v___y_343_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_n(v_a_527_, 4);
v_a_528_ = lean_ctor_get(v___x_526_, 1);
lean_inc(v_a_528_);
lean_dec_ref(v___x_526_);
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_533_, 0, v_a_527_);
lean_ctor_set(v___x_533_, 1, v___x_530_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = l_Lean_Syntax_node2(v_a_527_, v___x_531_, v_fst_361_, v___x_533_);
v___x_535_ = l_Lean_Syntax_node1(v_a_527_, v___x_530_, v___x_534_);
v___x_536_ = l_Lean_Syntax_node1(v_a_527_, v___x_529_, v___x_535_);
v_e_370_ = v___x_536_;
v___y_371_ = v___y_342_;
v___y_372_ = v_a_528_;
goto v___jp_369_;
}
else
{
lean_object* v_a_537_; lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_del_object(v___x_364_);
lean_dec(v_fst_361_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
lean_dec(v_fst_356_);
v_a_537_ = lean_ctor_get(v___x_526_, 0);
v_a_538_ = lean_ctor_get(v___x_526_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_526_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_inc(v_a_537_);
lean_dec(v___x_526_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_537_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
v_e_370_ = v_fst_361_;
v___y_371_ = v___y_342_;
v___y_372_ = v___y_343_;
goto v___jp_369_;
}
v___jp_369_:
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(v_fst_356_);
v___x_374_ = l_Lean_Syntax_isOfKind(v_fst_356_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(v_fst_356_);
v___x_376_ = l_Lean_Syntax_isOfKind(v_fst_356_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_e_370_);
lean_del_object(v___x_364_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
lean_dec(v_fst_356_);
v___x_377_ = l_Lean_Macro_throwUnsupported___redArg(v___y_372_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v_a_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
v_a_379_ = lean_ctor_get(v___x_377_, 1);
lean_inc(v_a_379_);
lean_dec_ref(v___x_377_);
v_e_345_ = v_a_378_;
v___y_346_ = v_a_379_;
goto v___jp_344_;
}
else
{
lean_object* v_a_380_; lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_a_380_ = lean_ctor_get(v___x_377_, 0);
v_a_381_ = lean_ctor_get(v___x_377_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_377_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_inc(v_a_380_);
lean_dec(v___x_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_ref_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v_ref_389_ = lean_ctor_get(v___y_371_, 5);
v___x_390_ = l_Lean_SourceInfo_fromRef(v_ref_389_, v___x_374_);
v___x_391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(v___x_390_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 2);
lean_ctor_set(v___x_364_, 1, v___x_391_);
lean_ctor_set(v___x_364_, 0, v___x_390_);
v___x_393_ = v___x_364_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_391_);
v___x_393_ = v_reuseFailAlloc_405_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(v___x_390_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 2);
lean_ctor_set(v___x_359_, 1, v___x_394_);
lean_ctor_set(v___x_359_, 0, v___x_390_);
v___x_396_ = v___x_359_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_404_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_398_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v___x_390_, 3);
v___x_399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_390_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
v___x_400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_390_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_Syntax_node2(v___x_390_, v___x_397_, v___x_401_, v_e_370_);
v___x_403_ = l_Lean_Syntax_node6(v___x_390_, v___x_366_, v___x_393_, v_fst_356_, v___x_396_, v_snd_357_, v___x_399_, v___x_402_);
v_e_345_ = v___x_403_;
v___y_346_ = v___y_372_;
goto v___jp_344_;
}
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_406_ = l_Lean_Syntax_getArg(v_fst_356_, v___x_367_);
v___x_407_ = l_Lean_Syntax_getArg(v_fst_356_, v___x_368_);
lean_dec(v_fst_356_);
v___x_408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(v___x_407_);
v___x_409_ = l_Lean_Syntax_isOfKind(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(v___x_407_);
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_407_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v___x_407_);
lean_dec(v___x_406_);
lean_dec(v_e_370_);
lean_del_object(v___x_364_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
v___x_412_ = l_Lean_Macro_throwUnsupported___redArg(v___y_372_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_a_414_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
v_a_414_ = lean_ctor_get(v___x_412_, 1);
lean_inc(v_a_414_);
lean_dec_ref(v___x_412_);
v_e_345_ = v_a_413_;
v___y_346_ = v_a_414_;
goto v___jp_344_;
}
else
{
lean_object* v_a_415_; lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_415_ = lean_ctor_get(v___x_412_, 0);
v_a_416_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_412_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_inc(v_a_415_);
lean_dec(v___x_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_415_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v_ref_424_; lean_object* v___x_425_; 
v_ref_424_ = lean_ctor_get(v___y_371_, 5);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_424_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_n(v_a_426_, 2);
v_a_427_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_a_427_);
lean_dec_ref(v___x_425_);
v___x_428_ = l_Lean_Syntax_getArg(v___x_407_, v___x_367_);
lean_dec(v___x_407_);
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 2);
lean_ctor_set(v___x_364_, 1, v___x_430_);
lean_ctor_set(v___x_364_, 0, v_a_426_);
v___x_432_ = v___x_364_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_426_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_430_);
v___x_432_ = v_reuseFailAlloc_466_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_434_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_426_, 2);
v___x_435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_435_, 0, v_a_426_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 2);
lean_ctor_set(v___x_359_, 1, v___x_438_);
lean_ctor_set(v___x_359_, 0, v_a_426_);
v___x_440_ = v___x_359_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_426_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_465_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_inc_n(v_a_426_, 16);
v___x_441_ = l_Lean_Syntax_node2(v_a_426_, v___x_437_, v___x_440_, v___x_428_);
lean_inc_ref_n(v___x_435_, 3);
v___x_442_ = l_Lean_Syntax_node2(v_a_426_, v___x_436_, v___x_435_, v___x_441_);
v___x_443_ = l_Lean_Syntax_node1(v_a_426_, v___x_433_, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
v___x_445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_445_, 0, v_a_426_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
v___x_449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_449_, 0, v_a_426_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_Syntax_node1(v_a_426_, v___x_433_, v___x_406_);
v___x_451_ = l_Lean_Syntax_node1(v_a_426_, v___x_433_, v___x_450_);
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v_a_426_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
lean_inc_ref(v___x_453_);
lean_inc_ref(v___x_449_);
v___x_454_ = l_Lean_Syntax_node4(v_a_426_, v___x_447_, v___x_449_, v___x_451_, v___x_453_, v_snd_357_);
v___x_455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
v___x_457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_457_, 0, v_a_426_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_Syntax_node1(v_a_426_, v___x_455_, v___x_457_);
v___x_459_ = l_Lean_Syntax_node1(v_a_426_, v___x_433_, v___x_458_);
v___x_460_ = l_Lean_Syntax_node1(v_a_426_, v___x_433_, v___x_459_);
v___x_461_ = l_Lean_Syntax_node4(v_a_426_, v___x_447_, v___x_449_, v___x_460_, v___x_453_, v_e_370_);
v___x_462_ = l_Lean_Syntax_node2(v_a_426_, v___x_433_, v___x_454_, v___x_461_);
v___x_463_ = l_Lean_Syntax_node1(v_a_426_, v___x_446_, v___x_462_);
v___x_464_ = l_Lean_Syntax_node7(v_a_426_, v___x_429_, v___x_432_, v___x_435_, v___x_435_, v___x_435_, v___x_443_, v___x_445_, v___x_463_);
v_e_345_ = v___x_464_;
v___y_346_ = v_a_427_;
goto v___jp_344_;
}
}
}
else
{
lean_object* v_a_467_; lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v___x_407_);
lean_dec(v___x_406_);
lean_dec(v_e_370_);
lean_del_object(v___x_364_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
v_a_467_ = lean_ctor_get(v___x_425_, 0);
v_a_468_ = lean_ctor_get(v___x_425_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_425_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_inc(v_a_467_);
lean_dec(v___x_425_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
else
{
lean_object* v_ref_476_; lean_object* v___x_477_; 
v_ref_476_ = lean_ctor_get(v___y_371_, 5);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_476_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_a_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_n(v_a_478_, 2);
v_a_479_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_a_479_);
lean_dec_ref(v___x_477_);
v___x_480_ = l_Lean_Syntax_getArg(v___x_407_, v___x_367_);
lean_dec(v___x_407_);
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 2);
lean_ctor_set(v___x_364_, 1, v___x_482_);
lean_ctor_set(v___x_364_, 0, v_a_478_);
v___x_484_ = v___x_364_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_478_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_482_);
v___x_484_ = v_reuseFailAlloc_514_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_478_, 4);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v_a_478_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref(v___x_487_);
v___x_489_ = l_Lean_Syntax_node2(v_a_478_, v___x_488_, v___x_487_, v___x_480_);
v___x_490_ = l_Lean_Syntax_node1(v_a_478_, v___x_485_, v___x_489_);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 2);
lean_ctor_set(v___x_359_, 1, v___x_491_);
lean_ctor_set(v___x_359_, 0, v_a_478_);
v___x_493_ = v___x_359_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_478_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_513_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
lean_inc_n(v_a_478_, 12);
v___x_497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_497_, 0, v_a_478_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = l_Lean_Syntax_node1(v_a_478_, v___x_485_, v___x_406_);
v___x_499_ = l_Lean_Syntax_node1(v_a_478_, v___x_485_, v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v_a_478_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
lean_inc_ref(v___x_501_);
lean_inc_ref(v___x_497_);
v___x_502_ = l_Lean_Syntax_node4(v_a_478_, v___x_495_, v___x_497_, v___x_499_, v___x_501_, v_snd_357_);
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
v___x_505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_505_, 0, v_a_478_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_Syntax_node1(v_a_478_, v___x_503_, v___x_505_);
v___x_507_ = l_Lean_Syntax_node1(v_a_478_, v___x_485_, v___x_506_);
v___x_508_ = l_Lean_Syntax_node1(v_a_478_, v___x_485_, v___x_507_);
v___x_509_ = l_Lean_Syntax_node4(v_a_478_, v___x_495_, v___x_497_, v___x_508_, v___x_501_, v_e_370_);
v___x_510_ = l_Lean_Syntax_node2(v_a_478_, v___x_485_, v___x_502_, v___x_509_);
v___x_511_ = l_Lean_Syntax_node1(v_a_478_, v___x_494_, v___x_510_);
lean_inc_ref_n(v___x_487_, 2);
v___x_512_ = l_Lean_Syntax_node7(v_a_478_, v___x_481_, v___x_484_, v___x_487_, v___x_487_, v___x_487_, v___x_490_, v___x_493_, v___x_511_);
v_e_345_ = v___x_512_;
v___y_346_ = v_a_479_;
goto v___jp_344_;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v___x_407_);
lean_dec(v___x_406_);
lean_dec(v_e_370_);
lean_del_object(v___x_364_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
v_a_515_ = lean_ctor_get(v___x_477_, 0);
v_a_516_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_477_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_inc(v_a_515_);
lean_dec(v___x_477_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_515_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
}
}
}
v___jp_344_:
{
uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; size_t v___x_350_; size_t v___x_351_; 
v___x_347_ = 0;
v___x_348_ = lean_box(v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_e_345_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_add(v_i_340_, v___x_350_);
v_i_340_ = v___x_351_;
v_b_341_ = v___x_349_;
v___y_343_ = v___y_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___boxed(lean_object* v_as_548_, lean_object* v_sz_549_, lean_object* v_i_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
size_t v_sz_boxed_554_; size_t v_i_boxed_555_; lean_object* v_res_556_; 
v_sz_boxed_554_ = lean_unbox_usize(v_sz_549_);
lean_dec(v_sz_549_);
v_i_boxed_555_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v_as_548_, v_sz_boxed_554_, v_i_boxed_555_, v_b_551_, v___y_552_, v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v_as_548_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(size_t v_sz_560_, size_t v_i_561_, lean_object* v_bs_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_lt(v_i_561_, v_sz_560_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v_bs_562_);
return v___x_564_;
}
else
{
lean_object* v_v_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_v_565_ = lean_array_uget(v_bs_562_, v_i_561_);
v___x_566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1));
lean_inc(v_v_565_);
v___x_567_ = l_Lean_Syntax_isOfKind(v_v_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
lean_dec(v_v_565_);
lean_dec_ref(v_bs_562_);
v___x_568_ = lean_box(0);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = l_Lean_Syntax_getArg(v_v_565_, v___x_569_);
lean_inc(v___x_570_);
v___x_571_ = l_Lean_Syntax_isOfKind(v___x_570_, v___x_566_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec(v___x_570_);
lean_dec(v_v_565_);
lean_dec_ref(v_bs_562_);
v___x_572_ = lean_box(0);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_bs_x27_575_; lean_object* v_tks_576_; lean_object* v_conds_577_; lean_object* v_ts_578_; lean_object* v___x_579_; lean_object* v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v___x_583_; 
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_unsigned_to_nat(3u);
v_bs_x27_575_ = lean_array_uset(v_bs_562_, v_i_561_, v___x_569_);
v_tks_576_ = l_Lean_Syntax_getArg(v___x_570_, v___x_573_);
lean_dec(v___x_570_);
v_conds_577_ = l_Lean_Syntax_getArg(v_v_565_, v___x_573_);
v_ts_578_ = l_Lean_Syntax_getArg(v_v_565_, v___x_574_);
lean_dec(v_v_565_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_conds_577_);
lean_ctor_set(v___x_579_, 1, v_ts_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_tks_576_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_add(v_i_561_, v___x_581_);
v___x_583_ = lean_array_uset(v_bs_x27_575_, v_i_561_, v___x_580_);
v_i_561_ = v___x_582_;
v_bs_562_ = v___x_583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___boxed(lean_object* v_sz_585_, lean_object* v_i_586_, lean_object* v_bs_587_){
_start:
{
size_t v_sz_boxed_588_; size_t v_i_boxed_589_; lean_object* v_res_590_; 
v_sz_boxed_588_ = lean_unbox_usize(v_sz_585_);
lean_dec(v_sz_585_);
v_i_boxed_589_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_boxed_588_, v_i_boxed_589_, v_bs_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(size_t v_sz_591_, size_t v_i_592_, lean_object* v_bs_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_usize_dec_lt(v_i_592_, v_sz_591_);
if (v___x_594_ == 0)
{
return v_bs_593_;
}
else
{
lean_object* v_v_595_; lean_object* v_snd_596_; lean_object* v_fst_597_; lean_object* v___x_598_; lean_object* v_bs_x27_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v_v_595_ = lean_array_uget_borrowed(v_bs_593_, v_i_592_);
v_snd_596_ = lean_ctor_get(v_v_595_, 1);
v_fst_597_ = lean_ctor_get(v_snd_596_, 0);
lean_inc(v_fst_597_);
v___x_598_ = lean_unsigned_to_nat(0u);
v_bs_x27_599_ = lean_array_uset(v_bs_593_, v_i_592_, v___x_598_);
v___x_600_ = ((size_t)1ULL);
v___x_601_ = lean_usize_add(v_i_592_, v___x_600_);
v___x_602_ = lean_array_uset(v_bs_x27_599_, v_i_592_, v_fst_597_);
v_i_592_ = v___x_601_;
v_bs_593_ = v___x_602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2___boxed(lean_object* v_sz_604_, lean_object* v_i_605_, lean_object* v_bs_606_){
_start:
{
size_t v_sz_boxed_607_; size_t v_i_boxed_608_; lean_object* v_res_609_; 
v_sz_boxed_607_ = lean_unbox_usize(v_sz_604_);
lean_dec(v_sz_604_);
v_i_boxed_608_ = lean_unbox_usize(v_i_605_);
lean_dec(v_i_605_);
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_boxed_607_, v_i_boxed_608_, v_bs_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(size_t v_sz_610_, size_t v_i_611_, lean_object* v_bs_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_lt(v_i_611_, v_sz_610_);
if (v___x_613_ == 0)
{
return v_bs_612_;
}
else
{
lean_object* v_v_614_; lean_object* v_snd_615_; lean_object* v_snd_616_; lean_object* v___x_617_; lean_object* v_bs_x27_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v_v_614_ = lean_array_uget_borrowed(v_bs_612_, v_i_611_);
v_snd_615_ = lean_ctor_get(v_v_614_, 1);
v_snd_616_ = lean_ctor_get(v_snd_615_, 1);
lean_inc(v_snd_616_);
v___x_617_ = lean_unsigned_to_nat(0u);
v_bs_x27_618_ = lean_array_uset(v_bs_612_, v_i_611_, v___x_617_);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_611_, v___x_619_);
v___x_621_ = lean_array_uset(v_bs_x27_618_, v_i_611_, v_snd_616_);
v_i_611_ = v___x_620_;
v_bs_612_ = v___x_621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1___boxed(lean_object* v_sz_623_, lean_object* v_i_624_, lean_object* v_bs_625_){
_start:
{
size_t v_sz_boxed_626_; size_t v_i_boxed_627_; lean_object* v_res_628_; 
v_sz_boxed_626_ = lean_unbox_usize(v_sz_623_);
lean_dec(v_sz_623_);
v_i_boxed_627_ = lean_unbox_usize(v_i_624_);
lean_dec(v_i_624_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_boxed_626_, v_i_boxed_627_, v_bs_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf(lean_object* v_stx_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_641_; uint8_t v_eIsSeq_642_; 
v___x_641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
lean_inc(v_stx_638_);
v_eIsSeq_642_ = l_Lean_Syntax_isOfKind(v_stx_638_, v___x_641_);
if (v_eIsSeq_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v_stx_638_);
v___x_643_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v_tk_645_; lean_object* v___x_646_; lean_object* v_cond_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v_tk_645_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_644_);
v___x_646_ = lean_unsigned_to_nat(1u);
v_cond_647_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_646_);
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(v_cond_647_);
v___x_649_ = l_Lean_Syntax_isOfKind(v_cond_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; size_t v_sz_653_; size_t v___x_654_; lean_object* v___x_655_; 
v___x_650_ = lean_unsigned_to_nat(4u);
v___x_651_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_650_);
v___x_652_ = l_Lean_Syntax_getArgs(v___x_651_);
lean_dec(v___x_651_);
v_sz_653_ = lean_array_size(v___x_652_);
v___x_654_ = ((size_t)0ULL);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_653_, v___x_654_, v___x_652_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; 
lean_dec(v_cond_647_);
lean_dec(v_tk_645_);
lean_dec(v_stx_638_);
v___x_656_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_656_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_658_; lean_object* v_t_659_; size_t v_sz_660_; lean_object* v_ts_661_; lean_object* v_conds_662_; lean_object* v___y_664_; lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_val_657_ = lean_ctor_get(v___x_655_, 0);
lean_inc_n(v_val_657_, 2);
lean_dec_ref(v___x_655_);
v___x_658_ = lean_unsigned_to_nat(3u);
v_t_659_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_658_);
v_sz_660_ = lean_array_size(v_val_657_);
v_ts_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_660_, v___x_654_, v_val_657_);
v_conds_662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_660_, v___x_654_, v_val_657_);
v___x_695_ = lean_unsigned_to_nat(5u);
v___x_696_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_695_);
lean_dec(v_stx_638_);
v___x_697_ = l_Lean_Syntax_isNone(v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
lean_dec(v_tk_645_);
v___x_698_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_696_);
v___x_699_ = l_Lean_Syntax_matchesNull(v___x_696_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v___x_696_);
lean_dec_ref(v_conds_662_);
lean_dec_ref(v_ts_661_);
lean_dec(v_t_659_);
lean_dec(v_cond_647_);
v___x_700_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_700_;
}
else
{
lean_object* v_e_x3f_701_; 
v_e_x3f_701_ = l_Lean_Syntax_getArg(v___x_696_, v___x_646_);
lean_dec(v___x_696_);
v___y_664_ = v_a_639_;
v_a_665_ = v_e_x3f_701_;
v_a_666_ = v_a_640_;
goto v___jp_663_;
}
}
else
{
lean_object* v_ref_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec(v___x_696_);
v_ref_702_ = lean_ctor_get(v_a_639_, 5);
v___x_703_ = l_Lean_SourceInfo_fromRef(v_ref_702_, v___x_649_);
v___x_704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_707_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__2));
v___x_708_ = l_Lean_SourceInfo_fromRef(v_tk_645_, v_eIsSeq_642_);
lean_dec(v_tk_645_);
v___x_709_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__3));
v___x_710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
lean_inc_n(v___x_703_, 4);
v___x_711_ = l_Lean_Syntax_node1(v___x_703_, v___x_707_, v___x_710_);
v___x_712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_713_, 0, v___x_703_);
lean_ctor_set(v___x_713_, 1, v___x_705_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
v___x_714_ = l_Lean_Syntax_node2(v___x_703_, v___x_706_, v___x_711_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node1(v___x_703_, v___x_705_, v___x_714_);
v___x_716_ = l_Lean_Syntax_node1(v___x_703_, v___x_704_, v___x_715_);
v___y_664_ = v_a_639_;
v_a_665_ = v___x_716_;
v_a_666_ = v_a_640_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; size_t v_sz_674_; lean_object* v___x_675_; 
v___x_667_ = l_Array_reverse___redArg(v_conds_662_);
v___x_668_ = lean_array_push(v___x_667_, v_cond_647_);
v___x_669_ = l_Array_reverse___redArg(v_ts_661_);
v___x_670_ = lean_array_push(v___x_669_, v_t_659_);
v___x_671_ = l_Array_zip___redArg(v___x_668_, v___x_670_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_668_);
v___x_672_ = lean_box(v_eIsSeq_642_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_a_665_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v_sz_674_ = lean_array_size(v___x_671_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_649_, v___x_671_, v_sz_674_, v___x_654_, v___x_673_, v___y_664_, v_a_666_);
lean_dec_ref(v___x_671_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_685_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_a_677_ = lean_ctor_get(v___x_675_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_685_ == 0)
{
v___x_679_ = v___x_675_;
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_fst_681_; lean_object* v___x_683_; 
v_fst_681_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_fst_681_);
lean_dec(v_a_676_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v_fst_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_a_677_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
else
{
lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
v_a_686_ = lean_ctor_get(v___x_675_, 0);
v_a_687_ = lean_ctor_get(v___x_675_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_675_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_inc(v_a_686_);
lean_dec(v___x_675_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_686_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_t_719_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v_a_724_; lean_object* v_a_725_; lean_object* v_conds_756_; lean_object* v_ts_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = lean_unsigned_to_nat(3u);
v_t_719_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_718_);
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_776_);
lean_inc(v___x_777_);
v___x_778_ = l_Lean_Syntax_matchesNull(v___x_777_, v___x_644_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; size_t v_sz_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_779_ = l_Lean_Syntax_getArgs(v___x_777_);
lean_dec(v___x_777_);
v_sz_780_ = lean_array_size(v___x_779_);
v___x_781_ = ((size_t)0ULL);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_780_, v___x_781_, v___x_779_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; 
lean_dec(v_t_719_);
lean_dec(v_cond_647_);
lean_dec(v_tk_645_);
lean_dec(v_stx_638_);
v___x_783_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; size_t v_sz_785_; lean_object* v_ts_786_; lean_object* v_conds_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_val_784_ = lean_ctor_get(v___x_782_, 0);
lean_inc_n(v_val_784_, 2);
lean_dec_ref(v___x_782_);
v_sz_785_ = lean_array_size(v_val_784_);
v_ts_786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_785_, v___x_781_, v_val_784_);
v_conds_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_785_, v___x_781_, v_val_784_);
v___x_788_ = lean_unsigned_to_nat(5u);
v___x_789_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_788_);
lean_dec(v_stx_638_);
v___x_790_ = l_Lean_Syntax_isNone(v___x_789_);
if (v___x_790_ == 0)
{
uint8_t v___x_791_; 
lean_dec(v_tk_645_);
lean_inc(v___x_789_);
v___x_791_ = l_Lean_Syntax_matchesNull(v___x_789_, v___x_717_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v___x_789_);
lean_dec_ref(v_conds_787_);
lean_dec_ref(v_ts_786_);
lean_dec(v_t_719_);
lean_dec(v_cond_647_);
v___x_792_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_792_;
}
else
{
lean_object* v_e_x3f_793_; 
v_e_x3f_793_ = l_Lean_Syntax_getArg(v___x_789_, v___x_646_);
lean_dec(v___x_789_);
v___y_721_ = v_ts_786_;
v___y_722_ = v_conds_787_;
v___y_723_ = v_a_639_;
v_a_724_ = v_e_x3f_793_;
v_a_725_ = v_a_640_;
goto v___jp_720_;
}
}
else
{
lean_dec(v___x_789_);
v_conds_756_ = v_conds_787_;
v_ts_757_ = v_ts_786_;
v___y_758_ = v_a_639_;
v___y_759_ = v_a_640_;
goto v___jp_755_;
}
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(5u);
v___x_795_ = l_Lean_Syntax_getArg(v_stx_638_, v___x_794_);
lean_dec(v_stx_638_);
lean_inc(v___x_795_);
v___x_796_ = l_Lean_Syntax_matchesNull(v___x_795_, v___x_717_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; size_t v_sz_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_797_ = l_Lean_Syntax_getArgs(v___x_777_);
lean_dec(v___x_777_);
v_sz_798_ = lean_array_size(v___x_797_);
v___x_799_ = ((size_t)0ULL);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_798_, v___x_799_, v___x_797_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_801_; 
lean_dec(v___x_795_);
lean_dec(v_t_719_);
lean_dec(v_cond_647_);
lean_dec(v_tk_645_);
v___x_801_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_801_;
}
else
{
lean_object* v_val_802_; size_t v_sz_803_; lean_object* v_ts_804_; lean_object* v_conds_805_; uint8_t v___x_806_; 
v_val_802_ = lean_ctor_get(v___x_800_, 0);
lean_inc_n(v_val_802_, 2);
lean_dec_ref(v___x_800_);
v_sz_803_ = lean_array_size(v_val_802_);
v_ts_804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_803_, v___x_799_, v_val_802_);
v_conds_805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_803_, v___x_799_, v_val_802_);
v___x_806_ = l_Lean_Syntax_isNone(v___x_795_);
if (v___x_806_ == 0)
{
lean_dec(v_tk_645_);
if (v___x_796_ == 0)
{
lean_object* v___x_807_; 
lean_dec_ref(v_conds_805_);
lean_dec_ref(v_ts_804_);
lean_dec(v___x_795_);
lean_dec(v_t_719_);
lean_dec(v_cond_647_);
v___x_807_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_807_;
}
else
{
lean_object* v_e_x3f_808_; 
v_e_x3f_808_ = l_Lean_Syntax_getArg(v___x_795_, v___x_646_);
lean_dec(v___x_795_);
v___y_721_ = v_ts_804_;
v___y_722_ = v_conds_805_;
v___y_723_ = v_a_639_;
v_a_724_ = v_e_x3f_808_;
v_a_725_ = v_a_640_;
goto v___jp_720_;
}
}
else
{
lean_dec(v___x_795_);
v_conds_756_ = v_conds_805_;
v_ts_757_ = v_ts_804_;
v___y_758_ = v_a_639_;
v___y_759_ = v_a_640_;
goto v___jp_755_;
}
}
}
else
{
lean_object* v___x_809_; 
lean_dec(v___x_795_);
lean_dec(v___x_777_);
lean_dec(v_t_719_);
lean_dec(v_cond_647_);
lean_dec(v_tk_645_);
v___x_809_ = l_Lean_Macro_throwUnsupported___redArg(v_a_640_);
return v___x_809_;
}
}
v___jp_720_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___x_726_ = l_Array_reverse___redArg(v___y_722_);
v___x_727_ = lean_array_push(v___x_726_, v_cond_647_);
v___x_728_ = l_Array_reverse___redArg(v___y_721_);
v___x_729_ = lean_array_push(v___x_728_, v_t_719_);
v___x_730_ = l_Array_zip___redArg(v___x_727_, v___x_729_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v___x_731_ = lean_box(v_eIsSeq_642_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_a_724_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v_sz_733_ = lean_array_size(v___x_730_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v___x_730_, v_sz_733_, v___x_734_, v___x_732_, v___y_723_, v_a_725_);
lean_dec_ref(v___x_730_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_a_737_ = lean_ctor_get(v___x_735_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v___x_735_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_fst_741_; lean_object* v___x_743_; 
v_fst_741_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_741_);
lean_dec(v_a_736_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v_fst_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_a_737_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_746_ = lean_ctor_get(v___x_735_, 0);
v_a_747_ = lean_ctor_get(v___x_735_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_735_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_inc(v_a_746_);
lean_dec(v___x_735_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_746_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
v___jp_755_:
{
lean_object* v_ref_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_ref_760_ = lean_ctor_get(v___y_758_, 5);
v___x_761_ = 0;
v___x_762_ = l_Lean_SourceInfo_fromRef(v_ref_760_, v___x_761_);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_766_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__2));
v___x_767_ = l_Lean_SourceInfo_fromRef(v_tk_645_, v_eIsSeq_642_);
lean_dec(v_tk_645_);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__3));
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
lean_inc_n(v___x_762_, 4);
v___x_770_ = l_Lean_Syntax_node1(v___x_762_, v___x_766_, v___x_769_);
v___x_771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_772_, 0, v___x_762_);
lean_ctor_set(v___x_772_, 1, v___x_764_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = l_Lean_Syntax_node2(v___x_762_, v___x_765_, v___x_770_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node1(v___x_762_, v___x_764_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node1(v___x_762_, v___x_763_, v___x_774_);
v___y_721_ = v_ts_757_;
v___y_722_ = v_conds_756_;
v___y_723_ = v___y_758_;
v_a_724_ = v___x_775_;
v_a_725_ = v___y_759_;
goto v___jp_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___boxed(lean_object* v_stx_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_Do_expandDoIf(v_stx_810_, v_a_811_, v_a_812_);
lean_dec_ref(v_a_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1(){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_823_ = l_Lean_Elab_macroAttribute;
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_825_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3));
v___x_826_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoIf___boxed), 3, 0);
v___x_827_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_823_, v___x_824_, v___x_825_, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___boxed(lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3(){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3));
v___x_833_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0));
v___x_834_ = l_Lean_addBuiltinDocString(v___x_832_, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___boxed(lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(lean_object* v_cond_840_, lean_object* v_then___841_, uint8_t v___x_842_, lean_object* v_else___843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_doBlockResultType_852_; lean_object* v___x_853_; 
v_doBlockResultType_852_ = lean_ctor_get(v___y_844_, 3);
lean_inc_ref(v_doBlockResultType_852_);
v___x_853_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_852_, v___y_844_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_874_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_874_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_ref_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v_ref_858_ = lean_ctor_get(v___y_849_, 5);
v___x_859_ = 0;
v___x_860_ = l_Lean_SourceInfo_fromRef(v_ref_858_, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1));
v___x_862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc_n(v___x_860_, 3);
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_860_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_860_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_860_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_Syntax_node6(v___x_860_, v___x_861_, v___x_863_, v_cond_840_, v___x_865_, v_then___841_, v___x_867_, v_else___843_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
v___x_870_ = v___x_856_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_854_);
v___x_870_ = v_reuseFailAlloc_873_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
v___x_872_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_868_, v___x_870_, v___x_842_, v___x_842_, v___x_871_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
return v___x_872_;
}
}
}
else
{
lean_dec(v_else___843_);
lean_dec(v_then___841_);
lean_dec(v_cond_840_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed(lean_object* v_cond_875_, lean_object* v_then___876_, lean_object* v___x_877_, lean_object* v_else___878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v___x_3198__boxed_887_; lean_object* v_res_888_; 
v___x_3198__boxed_887_ = lean_unbox(v___x_877_);
v_res_888_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(v_cond_875_, v_then___876_, v___x_3198__boxed_887_, v_else___878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_888_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1));
v___x_893_ = l_Lean_MessageData_ofFormat(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(lean_object* v_cond_894_, uint8_t v___x_895_, lean_object* v_elseSeq_896_, lean_object* v_dec_897_, lean_object* v_then___898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_907_ = lean_box(v___x_895_);
v___f_908_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed), 12, 3);
lean_closure_set(v___f_908_, 0, v_cond_894_);
lean_closure_set(v___f_908_, 1, v_then___898_);
lean_closure_set(v___f_908_, 2, v___x_907_);
v___x_909_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
v___x_910_ = lean_box(v___x_895_);
v___x_911_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_911_, 0, v_elseSeq_896_);
lean_closure_set(v___x_911_, 1, v_dec_897_);
lean_closure_set(v___x_911_, 2, v___x_910_);
v___x_912_ = lean_box(0);
v___x_913_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_909_, v___x_911_, v___f_908_, v___x_912_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed(lean_object* v_cond_914_, lean_object* v___x_915_, lean_object* v_elseSeq_916_, lean_object* v_dec_917_, lean_object* v_then___918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v___x_3281__boxed_927_; lean_object* v_res_928_; 
v___x_3281__boxed_927_ = lean_unbox(v___x_915_);
v_res_928_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(v_cond_914_, v___x_3281__boxed_927_, v_elseSeq_916_, v_dec_917_, v_then___918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_928_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1));
v___x_933_ = l_Lean_MessageData_ofFormat(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(lean_object* v_cond_934_, lean_object* v_thenSeq_935_, lean_object* v_elseSeq_936_, lean_object* v_dec_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_946_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
v___x_947_ = 1;
v___x_948_ = lean_box(v___x_947_);
lean_inc_ref(v_dec_937_);
v___f_949_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed), 13, 4);
lean_closure_set(v___f_949_, 0, v_cond_934_);
lean_closure_set(v___f_949_, 1, v___x_948_);
lean_closure_set(v___f_949_, 2, v_elseSeq_936_);
lean_closure_set(v___f_949_, 3, v_dec_937_);
v___x_950_ = lean_box(v___x_947_);
v___x_951_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_951_, 0, v_thenSeq_935_);
lean_closure_set(v___x_951_, 1, v_dec_937_);
lean_closure_set(v___x_951_, 2, v___x_950_);
v___x_952_ = lean_box(0);
v___x_953_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_946_, v___x_951_, v___f_949_, v___x_952_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___boxed(lean_object* v_cond_954_, lean_object* v_thenSeq_955_, lean_object* v_elseSeq_956_, lean_object* v_dec_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(v_cond_954_, v_thenSeq_955_, v_elseSeq_956_, v_dec_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_966_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_box(0);
v___x_968_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg(){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___boxed(lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(lean_object* v_00_u03b1_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___boxed(lean_object* v_00_u03b1_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(v_00_u03b1_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(lean_object* v_elseSeq_995_, lean_object* v_dec_996_, lean_object* v_thenSeq_997_, uint8_t v_then___998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = 1;
if (v_then___998_ == 0)
{
lean_object* v___x_1008_; 
lean_dec(v_thenSeq_997_);
v___x_1008_ = l_Lean_Elab_Do_elabDoSeq(v_elseSeq_995_, v_dec_996_, v___x_1007_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; 
lean_dec(v_elseSeq_995_);
v___x_1009_ = l_Lean_Elab_Do_elabDoSeq(v_thenSeq_997_, v_dec_996_, v___x_1007_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed(lean_object* v_elseSeq_1010_, lean_object* v_dec_1011_, lean_object* v_thenSeq_1012_, lean_object* v_then___1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v_then___00boxed_1022_; lean_object* v_res_1023_; 
v_then___00boxed_1022_ = lean_unbox(v_then___1013_);
v_res_1023_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(v_elseSeq_1010_, v_dec_1011_, v_thenSeq_1012_, v_then___00boxed_1022_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(lean_object* v_h_1035_, lean_object* v_cond_1036_, lean_object* v_then___1037_, uint8_t v___x_1038_, lean_object* v_else___1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_doBlockResultType_1048_; lean_object* v___x_1049_; 
v_doBlockResultType_1048_ = lean_ctor_get(v___y_1040_, 3);
lean_inc_ref(v_doBlockResultType_1048_);
v___x_1049_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_1048_, v___y_1040_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1104_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1104_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1104_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
lean_inc(v_h_1035_);
v___x_1055_ = l_Lean_Syntax_isOfKind(v_h_1035_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1));
lean_inc(v_h_1035_);
v___x_1057_ = l_Lean_Syntax_isOfKind(v_h_1035_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_del_object(v___x_1052_);
lean_dec(v_a_1050_);
lean_dec(v_else___1039_);
lean_dec(v_then___1037_);
lean_dec(v_cond_1036_);
lean_dec(v_h_1035_);
v___x_1058_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1058_;
}
else
{
lean_object* v_ref_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v_ref_1059_ = lean_ctor_get(v___y_1045_, 5);
v___x_1060_ = l_Lean_SourceInfo_fromRef(v_ref_1059_, v___x_1055_);
v___x_1061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
v___x_1062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc_n(v___x_1060_, 5);
v___x_1063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
v___x_1065_ = l_Lean_Syntax_node1(v___x_1060_, v___x_1064_, v_h_1035_);
v___x_1066_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
v___x_1067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1060_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_1069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1060_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_1071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1060_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_Syntax_node8(v___x_1060_, v___x_1061_, v___x_1063_, v___x_1065_, v___x_1067_, v_cond_1036_, v___x_1069_, v_then___1037_, v___x_1071_, v_else___1039_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 1);
v___x_1074_ = v___x_1052_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1050_);
v___x_1074_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1072_, v___x_1074_, v___x_1038_, v___x_1038_, v___x_1075_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1076_;
}
}
}
else
{
lean_object* v_ref_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v_ref_1078_ = lean_ctor_get(v___y_1045_, 5);
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = l_Lean_Syntax_getArg(v_h_1035_, v___x_1079_);
lean_dec(v_h_1035_);
v___x_1081_ = 0;
v___x_1082_ = l_Lean_SourceInfo_fromRef(v_ref_1078_, v___x_1081_);
v___x_1083_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
v___x_1084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc_n(v___x_1082_, 6);
v___x_1085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1082_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
v___x_1087_ = l_Lean_SourceInfo_fromRef(v___x_1080_, v___x_1038_);
lean_dec(v___x_1080_);
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
v___x_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_Syntax_node1(v___x_1082_, v___x_1054_, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_node1(v___x_1082_, v___x_1086_, v___x_1090_);
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
v___x_1093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1082_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_1095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1082_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_1097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1082_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_Syntax_node8(v___x_1082_, v___x_1083_, v___x_1085_, v___x_1091_, v___x_1093_, v_cond_1036_, v___x_1095_, v_then___1037_, v___x_1097_, v_else___1039_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 1);
v___x_1100_ = v___x_1052_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1050_);
v___x_1100_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1098_, v___x_1100_, v___x_1038_, v___x_1038_, v___x_1101_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1102_;
}
}
}
}
else
{
lean_dec(v_else___1039_);
lean_dec(v_then___1037_);
lean_dec(v_cond_1036_);
lean_dec(v_h_1035_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed(lean_object* v_h_1105_, lean_object* v_cond_1106_, lean_object* v_then___1107_, lean_object* v___x_1108_, lean_object* v_else___1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v___x_7828__boxed_1118_; lean_object* v_res_1119_; 
v___x_7828__boxed_1118_ = lean_unbox(v___x_1108_);
v_res_1119_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(v_h_1105_, v_cond_1106_, v_then___1107_, v___x_7828__boxed_1118_, v_else___1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(lean_object* v_h_1120_, lean_object* v_cond_1121_, uint8_t v___x_1122_, lean_object* v_elabDiteBranch_1123_, lean_object* v_then___1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1133_ = lean_box(v___x_1122_);
v___f_1134_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1134_, 0, v_h_1120_);
lean_closure_set(v___f_1134_, 1, v_cond_1121_);
lean_closure_set(v___f_1134_, 2, v_then___1124_);
lean_closure_set(v___f_1134_, 3, v___x_1133_);
v___x_1135_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
v___x_1136_ = 0;
v___x_1137_ = lean_box(v___x_1136_);
v___x_1138_ = lean_apply_1(v_elabDiteBranch_1123_, v___x_1137_);
v___x_1139_ = lean_box(0);
v___x_1140_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_1135_, v___x_1138_, v___f_1134_, v___x_1139_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed(lean_object* v_h_1141_, lean_object* v_cond_1142_, lean_object* v___x_1143_, lean_object* v_elabDiteBranch_1144_, lean_object* v_then___1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_7980__boxed_1154_; lean_object* v_res_1155_; 
v___x_7980__boxed_1154_ = lean_unbox(v___x_1143_);
v_res_1155_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(v_h_1141_, v_cond_1142_, v___x_7980__boxed_1154_, v_elabDiteBranch_1144_, v_then___1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(lean_object* v_h_1156_, lean_object* v_cond_1157_, lean_object* v_thenSeq_1158_, lean_object* v_elseSeq_1159_, lean_object* v_dec_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_elabDiteBranch_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_inc(v_thenSeq_1158_);
lean_inc_ref(v_dec_1160_);
lean_inc(v_elseSeq_1159_);
v_elabDiteBranch_1169_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 3);
lean_closure_set(v_elabDiteBranch_1169_, 0, v_elseSeq_1159_);
lean_closure_set(v_elabDiteBranch_1169_, 1, v_dec_1160_);
lean_closure_set(v_elabDiteBranch_1169_, 2, v_thenSeq_1158_);
v___x_1170_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
v___x_1171_ = 1;
v___x_1172_ = lean_box(v___x_1171_);
v___f_1173_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed), 13, 4);
lean_closure_set(v___f_1173_, 0, v_h_1156_);
lean_closure_set(v___f_1173_, 1, v_cond_1157_);
lean_closure_set(v___f_1173_, 2, v___x_1172_);
lean_closure_set(v___f_1173_, 3, v_elabDiteBranch_1169_);
v___x_1174_ = lean_box(v___x_1171_);
v___x_1175_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 4);
lean_closure_set(v___x_1175_, 0, v_elseSeq_1159_);
lean_closure_set(v___x_1175_, 1, v_dec_1160_);
lean_closure_set(v___x_1175_, 2, v_thenSeq_1158_);
lean_closure_set(v___x_1175_, 3, v___x_1174_);
v___x_1176_ = lean_box(0);
v___x_1177_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_1170_, v___x_1175_, v___f_1173_, v___x_1176_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___boxed(lean_object* v_h_1178_, lean_object* v_cond_1179_, lean_object* v_thenSeq_1180_, lean_object* v_elseSeq_1181_, lean_object* v_dec_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(v_h_1178_, v_cond_1179_, v_thenSeq_1180_, v_elseSeq_1181_, v_dec_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec_ref(v_a_1183_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0(lean_object* v___x_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v_thenSeq_1199_, lean_object* v_elseSeq_1200_, lean_object* v_dec_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7));
v___x_1211_ = l_Lean_Name_mkStr4(v___x_1192_, v___x_1193_, v___x_1194_, v___x_1210_);
lean_inc(v___x_1195_);
v___x_1212_ = l_Lean_Syntax_isOfKind(v___x_1195_, v___x_1211_);
lean_dec(v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v_dec_1201_);
lean_dec(v_elseSeq_1200_);
lean_dec(v_thenSeq_1199_);
lean_dec(v___x_1195_);
v___x_1213_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = l_Lean_Syntax_getArg(v___x_1195_, v___x_1196_);
lean_inc(v___x_1214_);
v___x_1215_ = l_Lean_Syntax_matchesNull(v___x_1214_, v___x_1196_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; 
lean_inc(v___x_1214_);
v___x_1216_ = l_Lean_Syntax_matchesNull(v___x_1214_, v___x_1197_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
lean_dec(v___x_1214_);
lean_dec_ref(v_dec_1201_);
lean_dec(v_elseSeq_1200_);
lean_dec(v_thenSeq_1199_);
lean_dec(v___x_1195_);
v___x_1217_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = l_Lean_Syntax_getArg(v___x_1214_, v___x_1196_);
lean_dec(v___x_1214_);
v___x_1219_ = l_Lean_Syntax_getArg(v___x_1195_, v___x_1198_);
lean_dec(v___x_1195_);
v___x_1220_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(v___x_1218_, v___x_1219_, v_thenSeq_1199_, v_elseSeq_1200_, v_dec_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1220_;
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v___x_1214_);
v___x_1221_ = l_Lean_Syntax_getArg(v___x_1195_, v___x_1198_);
lean_dec(v___x_1195_);
v___x_1222_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(v___x_1221_, v_thenSeq_1199_, v_elseSeq_1200_, v_dec_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0___boxed(lean_object** _args){
lean_object* v___x_1223_ = _args[0];
lean_object* v___x_1224_ = _args[1];
lean_object* v___x_1225_ = _args[2];
lean_object* v___x_1226_ = _args[3];
lean_object* v___x_1227_ = _args[4];
lean_object* v___x_1228_ = _args[5];
lean_object* v___x_1229_ = _args[6];
lean_object* v_thenSeq_1230_ = _args[7];
lean_object* v_elseSeq_1231_ = _args[8];
lean_object* v_dec_1232_ = _args[9];
lean_object* v___y_1233_ = _args[10];
lean_object* v___y_1234_ = _args[11];
lean_object* v___y_1235_ = _args[12];
lean_object* v___y_1236_ = _args[13];
lean_object* v___y_1237_ = _args[14];
lean_object* v___y_1238_ = _args[15];
lean_object* v___y_1239_ = _args[16];
lean_object* v___y_1240_ = _args[17];
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_Do_elabDoIf___lam__0(v___x_1223_, v___x_1224_, v___x_1225_, v___x_1226_, v___x_1227_, v___x_1228_, v___x_1229_, v_thenSeq_1230_, v_elseSeq_1231_, v_dec_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___x_1229_);
lean_dec(v___x_1228_);
lean_dec(v___x_1227_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf(lean_object* v_stx_1242_, lean_object* v_dec_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0));
v___x_1253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1));
v___x_1254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2));
v___x_1255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
lean_inc(v_stx_1242_);
v___x_1256_ = l_Lean_Syntax_isOfKind(v_stx_1242_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_dec_ref(v_dec_1243_);
lean_dec(v_stx_1242_);
v___x_1257_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_unsigned_to_nat(4u);
v___x_1260_ = l_Lean_Syntax_getArg(v_stx_1242_, v___x_1259_);
v___x_1261_ = l_Lean_Syntax_matchesNull(v___x_1260_, v___x_1258_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref(v_dec_1243_);
lean_dec(v_stx_1242_);
v___x_1262_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1262_;
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1263_ = lean_unsigned_to_nat(2u);
v___x_1264_ = lean_unsigned_to_nat(5u);
v___x_1265_ = l_Lean_Syntax_getArg(v_stx_1242_, v___x_1264_);
lean_inc(v___x_1265_);
v___x_1266_ = l_Lean_Syntax_matchesNull(v___x_1265_, v___x_1263_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v___x_1265_);
lean_dec_ref(v_dec_1243_);
lean_dec(v_stx_1242_);
v___x_1267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v_thenSeq_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_unsigned_to_nat(3u);
v_thenSeq_1269_ = l_Lean_Syntax_getArg(v_stx_1242_, v___x_1268_);
lean_inc(v_thenSeq_1269_);
v___x_1270_ = l_Lean_Elab_Do_inferControlInfoSeq(v_thenSeq_1269_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v_elseSeq_1273_; lean_object* v___x_1274_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v_elseSeq_1273_ = l_Lean_Syntax_getArg(v___x_1265_, v___x_1272_);
lean_dec(v___x_1265_);
lean_inc(v_elseSeq_1273_);
v___x_1274_ = l_Lean_Elab_Do_inferControlInfoSeq(v_elseSeq_1273_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v___f_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = l_Lean_Syntax_getArg(v_stx_1242_, v___x_1272_);
lean_dec(v_stx_1242_);
v___f_1277_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___lam__0___boxed), 18, 9);
lean_closure_set(v___f_1277_, 0, v___x_1252_);
lean_closure_set(v___f_1277_, 1, v___x_1253_);
lean_closure_set(v___f_1277_, 2, v___x_1254_);
lean_closure_set(v___f_1277_, 3, v___x_1276_);
lean_closure_set(v___f_1277_, 4, v___x_1258_);
lean_closure_set(v___f_1277_, 5, v___x_1263_);
lean_closure_set(v___f_1277_, 6, v___x_1272_);
lean_closure_set(v___f_1277_, 7, v_thenSeq_1269_);
lean_closure_set(v___f_1277_, 8, v_elseSeq_1273_);
v___x_1278_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1271_, v_a_1275_);
v___x_1279_ = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(v_dec_1243_, v___x_1278_, v___f_1277_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1279_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_elseSeq_1273_);
lean_dec(v_a_1271_);
lean_dec(v_thenSeq_1269_);
lean_dec_ref(v_dec_1243_);
lean_dec(v_stx_1242_);
v_a_1280_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1274_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1274_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_thenSeq_1269_);
lean_dec(v___x_1265_);
lean_dec_ref(v_dec_1243_);
lean_dec(v_stx_1242_);
v_a_1288_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1270_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1270_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___boxed(lean_object* v_stx_1296_, lean_object* v_dec_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Elab_Do_elabDoIf(v_stx_1296_, v_dec_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_a_1298_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1(){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1314_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_1316_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1));
v___x_1317_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___boxed), 10, 0);
v___x_1318_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1314_, v___x_1315_, v___x_1316_, v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___boxed(lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
return v_res_1320_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_If(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_If(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_If(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_If(builtin);
}
#ifdef __cplusplus
}
#endif
