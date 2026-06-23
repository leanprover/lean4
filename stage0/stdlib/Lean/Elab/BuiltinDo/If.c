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
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedAction"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value),LEAN_SCALAR_PTR_LITERAL(115, 27, 24, 243, 204, 49, 153, 202)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__41_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__41_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42_value;
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
uint8_t v___x_35242__boxed_11_; lean_object* v_res_12_; 
v___x_35242__boxed_11_ = lean_unbox(v___x_7_);
v_res_12_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_35242__boxed_11_, v_____do__lift_8_, v___y_9_, v___y_10_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(uint8_t v___x_113_, lean_object* v_as_114_, size_t v_sz_115_, size_t v_i_116_, lean_object* v_b_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_e_121_; lean_object* v___y_122_; uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_lt(v_i_116_, v_sz_115_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_b_117_);
lean_ctor_set(v___x_129_, 1, v___y_119_);
return v___x_129_;
}
else
{
lean_object* v_a_130_; lean_object* v_fst_131_; lean_object* v_snd_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_324_; 
v_a_130_ = lean_array_uget(v_as_114_, v_i_116_);
v_fst_131_ = lean_ctor_get(v_a_130_, 0);
v_snd_132_ = lean_ctor_get(v_a_130_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_a_130_);
if (v_isSharedCheck_324_ == 0)
{
v___x_134_ = v_a_130_;
v_isShared_135_ = v_isSharedCheck_324_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_snd_132_);
lean_inc(v_fst_131_);
lean_dec(v_a_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_324_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_323_; 
v_fst_136_ = lean_ctor_get(v_b_117_, 0);
v_snd_137_ = lean_ctor_get(v_b_117_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_b_117_);
if (v_isSharedCheck_323_ == 0)
{
v___x_139_ = v_b_117_;
v_isShared_140_ = v_isSharedCheck_323_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_137_);
lean_inc(v_fst_136_);
lean_dec(v_b_117_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_323_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_e_145_; lean_object* v___y_146_; lean_object* v___y_147_; uint8_t v___x_301_; 
v___x_141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_301_ = lean_unbox(v_snd_137_);
lean_dec(v_snd_137_);
if (v___x_301_ == 0)
{
lean_object* v_ref_302_; lean_object* v___x_303_; 
v_ref_302_ = lean_ctor_get(v___y_118_, 5);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_113_, v_ref_302_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc_n(v_a_304_, 4);
v_a_305_ = lean_ctor_get(v___x_303_, 1);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_303_, 2);
v___x_306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42));
v___x_309_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_310_, 0, v_a_304_);
lean_ctor_set(v___x_310_, 1, v___x_307_);
lean_ctor_set(v___x_310_, 2, v___x_309_);
v___x_311_ = l_Lean_Syntax_node2(v_a_304_, v___x_308_, v_fst_136_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node1(v_a_304_, v___x_307_, v___x_311_);
v___x_313_ = l_Lean_Syntax_node1(v_a_304_, v___x_306_, v___x_312_);
v_e_145_ = v___x_313_;
v___y_146_ = v___y_118_;
v___y_147_ = v_a_305_;
goto v___jp_144_;
}
else
{
lean_object* v_a_314_; lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_del_object(v___x_139_);
lean_dec(v_fst_136_);
lean_del_object(v___x_134_);
lean_dec(v_snd_132_);
lean_dec(v_fst_131_);
v_a_314_ = lean_ctor_get(v___x_303_, 0);
v_a_315_ = lean_ctor_get(v___x_303_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_303_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_inc(v_a_314_);
lean_dec(v___x_303_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_314_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
else
{
v_e_145_ = v_fst_136_;
v___y_146_ = v___y_118_;
v___y_147_ = v___y_119_;
goto v___jp_144_;
}
v___jp_144_:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(v_fst_131_);
v___x_149_ = l_Lean_Syntax_isOfKind(v_fst_131_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(v_fst_131_);
v___x_151_ = l_Lean_Syntax_isOfKind(v_fst_131_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec(v_e_145_);
lean_del_object(v___x_139_);
lean_del_object(v___x_134_);
lean_dec(v_snd_132_);
lean_dec(v_fst_131_);
v___x_152_ = l_Lean_Macro_throwUnsupported___redArg(v___y_147_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v_a_154_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
v_a_154_ = lean_ctor_get(v___x_152_, 1);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_152_, 2);
v_e_121_ = v_a_153_;
v___y_122_ = v_a_154_;
goto v___jp_120_;
}
else
{
lean_object* v_a_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_a_155_ = lean_ctor_get(v___x_152_, 0);
v_a_156_ = lean_ctor_get(v___x_152_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_152_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_inc(v_a_155_);
lean_dec(v___x_152_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_155_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_ref_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v_ref_164_ = lean_ctor_get(v___y_146_, 5);
v___x_165_ = l_Lean_SourceInfo_fromRef(v_ref_164_, v___x_113_);
v___x_166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(v___x_165_);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 2);
lean_ctor_set(v___x_139_, 1, v___x_166_);
lean_ctor_set(v___x_139_, 0, v___x_165_);
v___x_168_ = v___x_139_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_180_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(v___x_165_);
if (v_isShared_135_ == 0)
{
lean_ctor_set_tag(v___x_134_, 2);
lean_ctor_set(v___x_134_, 1, v___x_169_);
lean_ctor_set(v___x_134_, 0, v___x_165_);
v___x_171_ = v___x_134_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_179_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v___x_165_, 3);
v___x_174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_165_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_165_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Lean_Syntax_node2(v___x_165_, v___x_172_, v___x_176_, v_e_145_);
v___x_178_ = l_Lean_Syntax_node6(v___x_165_, v___x_141_, v___x_168_, v_fst_131_, v___x_171_, v_snd_132_, v___x_174_, v___x_177_);
v_e_121_ = v___x_178_;
v___y_122_ = v___y_147_;
goto v___jp_120_;
}
}
}
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_181_ = l_Lean_Syntax_getArg(v_fst_131_, v___x_142_);
v___x_182_ = l_Lean_Syntax_getArg(v_fst_131_, v___x_143_);
lean_dec(v_fst_131_);
v___x_183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(v___x_182_);
v___x_184_ = l_Lean_Syntax_isOfKind(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(v___x_182_);
v___x_186_ = l_Lean_Syntax_isOfKind(v___x_182_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec(v___x_182_);
lean_dec(v___x_181_);
lean_dec(v_e_145_);
lean_del_object(v___x_139_);
lean_del_object(v___x_134_);
lean_dec(v_snd_132_);
v___x_187_ = l_Lean_Macro_throwUnsupported___redArg(v___y_147_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v_a_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
v_a_189_ = lean_ctor_get(v___x_187_, 1);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_187_, 2);
v_e_121_ = v_a_188_;
v___y_122_ = v_a_189_;
goto v___jp_120_;
}
else
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
v_a_190_ = lean_ctor_get(v___x_187_, 0);
v_a_191_ = lean_ctor_get(v___x_187_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_187_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_inc(v_a_190_);
lean_dec(v___x_187_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_190_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_ref_199_; lean_object* v___x_200_; 
v_ref_199_ = lean_ctor_get(v___y_146_, 5);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_113_, v_ref_199_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_a_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_n(v_a_201_, 2);
v_a_202_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_200_, 2);
v___x_203_ = l_Lean_Syntax_getArg(v___x_182_, v___x_142_);
lean_dec(v___x_182_);
v___x_204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 2);
lean_ctor_set(v___x_139_, 1, v___x_205_);
lean_ctor_set(v___x_139_, 0, v_a_201_);
v___x_207_ = v___x_139_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_243_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_209_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_201_, 2);
v___x_210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_210_, 0, v_a_201_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_209_);
v___x_211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
v___x_212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
v___x_213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
if (v_isShared_135_ == 0)
{
lean_ctor_set_tag(v___x_134_, 2);
lean_ctor_set(v___x_134_, 1, v___x_213_);
lean_ctor_set(v___x_134_, 0, v_a_201_);
v___x_215_ = v___x_134_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_242_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28));
lean_inc_n(v_a_201_, 17);
v___x_217_ = l_Lean_Syntax_node1(v_a_201_, v___x_216_, v___x_203_);
v___x_218_ = l_Lean_Syntax_node2(v_a_201_, v___x_212_, v___x_215_, v___x_217_);
lean_inc_ref_n(v___x_210_, 3);
v___x_219_ = l_Lean_Syntax_node2(v_a_201_, v___x_211_, v___x_210_, v___x_218_);
v___x_220_ = l_Lean_Syntax_node1(v_a_201_, v___x_208_, v___x_219_);
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v_a_201_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v_a_201_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_Syntax_node1(v_a_201_, v___x_208_, v___x_181_);
v___x_228_ = l_Lean_Syntax_node1(v_a_201_, v___x_208_, v___x_227_);
v___x_229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_230_, 0, v_a_201_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
lean_inc_ref(v___x_230_);
lean_inc_ref(v___x_226_);
v___x_231_ = l_Lean_Syntax_node4(v_a_201_, v___x_224_, v___x_226_, v___x_228_, v___x_230_, v_snd_132_);
v___x_232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_234_, 0, v_a_201_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = l_Lean_Syntax_node1(v_a_201_, v___x_232_, v___x_234_);
v___x_236_ = l_Lean_Syntax_node1(v_a_201_, v___x_208_, v___x_235_);
v___x_237_ = l_Lean_Syntax_node1(v_a_201_, v___x_208_, v___x_236_);
v___x_238_ = l_Lean_Syntax_node4(v_a_201_, v___x_224_, v___x_226_, v___x_237_, v___x_230_, v_e_145_);
v___x_239_ = l_Lean_Syntax_node2(v_a_201_, v___x_208_, v___x_231_, v___x_238_);
v___x_240_ = l_Lean_Syntax_node1(v_a_201_, v___x_223_, v___x_239_);
v___x_241_ = l_Lean_Syntax_node7(v_a_201_, v___x_204_, v___x_207_, v___x_210_, v___x_210_, v___x_210_, v___x_220_, v___x_222_, v___x_240_);
v_e_121_ = v___x_241_;
v___y_122_ = v_a_202_;
goto v___jp_120_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v___x_182_);
lean_dec(v___x_181_);
lean_dec(v_e_145_);
lean_del_object(v___x_139_);
lean_del_object(v___x_134_);
lean_dec(v_snd_132_);
v_a_244_ = lean_ctor_get(v___x_200_, 0);
v_a_245_ = lean_ctor_get(v___x_200_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_200_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_inc(v_a_244_);
lean_dec(v___x_200_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_244_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
else
{
lean_object* v_ref_253_; lean_object* v___x_254_; 
v_ref_253_ = lean_ctor_get(v___y_146_, 5);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_113_, v_ref_253_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v_a_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_n(v_a_255_, 2);
v_a_256_ = lean_ctor_get(v___x_254_, 1);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_254_, 2);
v___x_257_ = l_Lean_Syntax_getArg(v___x_182_, v___x_142_);
lean_dec(v___x_182_);
v___x_258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 2);
lean_ctor_set(v___x_139_, 1, v___x_259_);
lean_ctor_set(v___x_139_, 0, v_a_255_);
v___x_261_ = v___x_139_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_255_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_291_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_263_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_255_, 4);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v_a_255_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_263_);
v___x_265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref(v___x_264_);
v___x_266_ = l_Lean_Syntax_node2(v_a_255_, v___x_265_, v___x_264_, v___x_257_);
v___x_267_ = l_Lean_Syntax_node1(v_a_255_, v___x_262_, v___x_266_);
v___x_268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
if (v_isShared_135_ == 0)
{
lean_ctor_set_tag(v___x_134_, 2);
lean_ctor_set(v___x_134_, 1, v___x_268_);
lean_ctor_set(v___x_134_, 0, v_a_255_);
v___x_270_ = v___x_134_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_255_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_290_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
lean_inc_n(v_a_255_, 12);
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_255_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Syntax_node1(v_a_255_, v___x_262_, v___x_181_);
v___x_276_ = l_Lean_Syntax_node1(v_a_255_, v___x_262_, v___x_275_);
v___x_277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_278_, 0, v_a_255_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
lean_inc_ref(v___x_278_);
lean_inc_ref(v___x_274_);
v___x_279_ = l_Lean_Syntax_node4(v_a_255_, v___x_272_, v___x_274_, v___x_276_, v___x_278_, v_snd_132_);
v___x_280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v_a_255_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_Syntax_node1(v_a_255_, v___x_280_, v___x_282_);
v___x_284_ = l_Lean_Syntax_node1(v_a_255_, v___x_262_, v___x_283_);
v___x_285_ = l_Lean_Syntax_node1(v_a_255_, v___x_262_, v___x_284_);
v___x_286_ = l_Lean_Syntax_node4(v_a_255_, v___x_272_, v___x_274_, v___x_285_, v___x_278_, v_e_145_);
v___x_287_ = l_Lean_Syntax_node2(v_a_255_, v___x_262_, v___x_279_, v___x_286_);
v___x_288_ = l_Lean_Syntax_node1(v_a_255_, v___x_271_, v___x_287_);
lean_inc_ref_n(v___x_264_, 2);
v___x_289_ = l_Lean_Syntax_node7(v_a_255_, v___x_258_, v___x_261_, v___x_264_, v___x_264_, v___x_264_, v___x_267_, v___x_270_, v___x_288_);
v_e_121_ = v___x_289_;
v___y_122_ = v_a_256_;
goto v___jp_120_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec(v___x_182_);
lean_dec(v___x_181_);
lean_dec(v_e_145_);
lean_del_object(v___x_139_);
lean_del_object(v___x_134_);
lean_dec(v_snd_132_);
v_a_292_ = lean_ctor_get(v___x_254_, 0);
v_a_293_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_254_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_inc(v_a_292_);
lean_dec(v___x_254_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_292_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
}
}
}
}
v___jp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; size_t v___x_125_; size_t v___x_126_; 
v___x_123_ = lean_box(v___x_113_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_e_121_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_add(v_i_116_, v___x_125_);
v_i_116_ = v___x_126_;
v_b_117_ = v___x_124_;
v___y_119_ = v___y_122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___boxed(lean_object* v___x_325_, lean_object* v_as_326_, lean_object* v_sz_327_, lean_object* v_i_328_, lean_object* v_b_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
uint8_t v___x_35505__boxed_332_; size_t v_sz_boxed_333_; size_t v_i_boxed_334_; lean_object* v_res_335_; 
v___x_35505__boxed_332_ = lean_unbox(v___x_325_);
v_sz_boxed_333_ = lean_unbox_usize(v_sz_327_);
lean_dec(v_sz_327_);
v_i_boxed_334_ = lean_unbox_usize(v_i_328_);
lean_dec(v_i_328_);
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_35505__boxed_332_, v_as_326_, v_sz_boxed_333_, v_i_boxed_334_, v_b_329_, v___y_330_, v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec_ref(v_as_326_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(lean_object* v_____do__lift_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = 0;
v___x_340_ = l_Lean_SourceInfo_fromRef(v_____do__lift_336_, v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___y_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0___boxed(lean_object* v_____do__lift_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_____do__lift_342_, v___y_343_, v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v_____do__lift_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(lean_object* v_as_346_, size_t v_sz_347_, size_t v_i_348_, lean_object* v_b_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_e_353_; lean_object* v___y_354_; uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_lt(v_i_348_, v_sz_347_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_b_349_);
lean_ctor_set(v___x_362_, 1, v___y_351_);
return v___x_362_;
}
else
{
lean_object* v_a_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_557_; 
v_a_363_ = lean_array_uget(v_as_346_, v_i_348_);
v_fst_364_ = lean_ctor_get(v_a_363_, 0);
v_snd_365_ = lean_ctor_get(v_a_363_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_a_363_);
if (v_isSharedCheck_557_ == 0)
{
v___x_367_ = v_a_363_;
v_isShared_368_ = v_isSharedCheck_557_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snd_365_);
lean_inc(v_fst_364_);
lean_dec(v_a_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_557_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_556_; 
v_fst_369_ = lean_ctor_get(v_b_349_, 0);
v_snd_370_ = lean_ctor_get(v_b_349_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_b_349_);
if (v_isSharedCheck_556_ == 0)
{
v___x_372_ = v_b_349_;
v_isShared_373_ = v_isSharedCheck_556_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snd_370_);
lean_inc(v_fst_369_);
lean_dec(v_b_349_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_556_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_e_378_; lean_object* v___y_379_; lean_object* v___y_380_; uint8_t v___x_534_; 
v___x_374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_unsigned_to_nat(2u);
v___x_534_ = lean_unbox(v_snd_370_);
lean_dec(v_snd_370_);
if (v___x_534_ == 0)
{
lean_object* v_ref_535_; lean_object* v___x_536_; 
v_ref_535_ = lean_ctor_get(v___y_350_, 5);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_535_, v___y_350_, v___y_351_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_a_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc_n(v_a_537_, 4);
v_a_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_536_, 2);
v___x_539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42));
v___x_542_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_543_, 0, v_a_537_);
lean_ctor_set(v___x_543_, 1, v___x_540_);
lean_ctor_set(v___x_543_, 2, v___x_542_);
v___x_544_ = l_Lean_Syntax_node2(v_a_537_, v___x_541_, v_fst_369_, v___x_543_);
v___x_545_ = l_Lean_Syntax_node1(v_a_537_, v___x_540_, v___x_544_);
v___x_546_ = l_Lean_Syntax_node1(v_a_537_, v___x_539_, v___x_545_);
v_e_378_ = v___x_546_;
v___y_379_ = v___y_350_;
v___y_380_ = v_a_538_;
goto v___jp_377_;
}
else
{
lean_object* v_a_547_; lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_del_object(v___x_372_);
lean_dec(v_fst_369_);
lean_del_object(v___x_367_);
lean_dec(v_snd_365_);
lean_dec(v_fst_364_);
v_a_547_ = lean_ctor_get(v___x_536_, 0);
v_a_548_ = lean_ctor_get(v___x_536_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_536_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_inc(v_a_547_);
lean_dec(v___x_536_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_547_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
v_e_378_ = v_fst_369_;
v___y_379_ = v___y_350_;
v___y_380_ = v___y_351_;
goto v___jp_377_;
}
v___jp_377_:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(v_fst_364_);
v___x_382_ = l_Lean_Syntax_isOfKind(v_fst_364_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(v_fst_364_);
v___x_384_ = l_Lean_Syntax_isOfKind(v_fst_364_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec(v_e_378_);
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_snd_365_);
lean_dec(v_fst_364_);
v___x_385_ = l_Lean_Macro_throwUnsupported___redArg(v___y_380_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_a_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
v_a_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_385_, 2);
v_e_353_ = v_a_386_;
v___y_354_ = v_a_387_;
goto v___jp_352_;
}
else
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
v_a_388_ = lean_ctor_get(v___x_385_, 0);
v_a_389_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_385_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_inc(v_a_388_);
lean_dec(v___x_385_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_388_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v_ref_397_ = lean_ctor_get(v___y_379_, 5);
v___x_398_ = l_Lean_SourceInfo_fromRef(v_ref_397_, v___x_382_);
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(v___x_398_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 2);
lean_ctor_set(v___x_372_, 1, v___x_399_);
lean_ctor_set(v___x_372_, 0, v___x_398_);
v___x_401_ = v___x_372_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_413_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(v___x_398_);
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 2);
lean_ctor_set(v___x_367_, 1, v___x_402_);
lean_ctor_set(v___x_367_, 0, v___x_398_);
v___x_404_ = v___x_367_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_402_);
v___x_404_ = v_reuseFailAlloc_412_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_406_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v___x_398_, 3);
v___x_407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_398_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
v___x_408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_398_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Lean_Syntax_node2(v___x_398_, v___x_405_, v___x_409_, v_e_378_);
v___x_411_ = l_Lean_Syntax_node6(v___x_398_, v___x_374_, v___x_401_, v_fst_364_, v___x_404_, v_snd_365_, v___x_407_, v___x_410_);
v_e_353_ = v___x_411_;
v___y_354_ = v___y_380_;
goto v___jp_352_;
}
}
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_414_ = l_Lean_Syntax_getArg(v_fst_364_, v___x_375_);
v___x_415_ = l_Lean_Syntax_getArg(v_fst_364_, v___x_376_);
lean_dec(v_fst_364_);
v___x_416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(v___x_415_);
v___x_417_ = l_Lean_Syntax_isOfKind(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(v___x_415_);
v___x_419_ = l_Lean_Syntax_isOfKind(v___x_415_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec(v___x_415_);
lean_dec(v___x_414_);
lean_dec(v_e_378_);
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_snd_365_);
v___x_420_ = l_Lean_Macro_throwUnsupported___redArg(v___y_380_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v_a_422_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
v_a_422_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_420_, 2);
v_e_353_ = v_a_421_;
v___y_354_ = v_a_422_;
goto v___jp_352_;
}
else
{
lean_object* v_a_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_423_ = lean_ctor_get(v___x_420_, 0);
v_a_424_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_420_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_inc(v_a_423_);
lean_dec(v___x_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_423_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_ref_432_; lean_object* v___x_433_; 
v_ref_432_ = lean_ctor_get(v___y_379_, 5);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_432_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_n(v_a_434_, 2);
v_a_435_ = lean_ctor_get(v___x_433_, 1);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_433_, 2);
v___x_436_ = l_Lean_Syntax_getArg(v___x_415_, v___x_375_);
lean_dec(v___x_415_);
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 2);
lean_ctor_set(v___x_372_, 1, v___x_438_);
lean_ctor_set(v___x_372_, 0, v_a_434_);
v___x_440_ = v___x_372_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_434_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_476_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_434_, 2);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v_a_434_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
v___x_446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 2);
lean_ctor_set(v___x_367_, 1, v___x_446_);
lean_ctor_set(v___x_367_, 0, v_a_434_);
v___x_448_ = v___x_367_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_434_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_475_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28));
lean_inc_n(v_a_434_, 17);
v___x_450_ = l_Lean_Syntax_node1(v_a_434_, v___x_449_, v___x_436_);
v___x_451_ = l_Lean_Syntax_node2(v_a_434_, v___x_445_, v___x_448_, v___x_450_);
lean_inc_ref_n(v___x_443_, 3);
v___x_452_ = l_Lean_Syntax_node2(v_a_434_, v___x_444_, v___x_443_, v___x_451_);
v___x_453_ = l_Lean_Syntax_node1(v_a_434_, v___x_441_, v___x_452_);
v___x_454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v_a_434_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
v___x_459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_459_, 0, v_a_434_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_Syntax_node1(v_a_434_, v___x_441_, v___x_414_);
v___x_461_ = l_Lean_Syntax_node1(v_a_434_, v___x_441_, v___x_460_);
v___x_462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_463_, 0, v_a_434_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_inc_ref(v___x_463_);
lean_inc_ref(v___x_459_);
v___x_464_ = l_Lean_Syntax_node4(v_a_434_, v___x_457_, v___x_459_, v___x_461_, v___x_463_, v_snd_365_);
v___x_465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_467_, 0, v_a_434_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_Syntax_node1(v_a_434_, v___x_465_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v_a_434_, v___x_441_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node1(v_a_434_, v___x_441_, v___x_469_);
v___x_471_ = l_Lean_Syntax_node4(v_a_434_, v___x_457_, v___x_459_, v___x_470_, v___x_463_, v_e_378_);
v___x_472_ = l_Lean_Syntax_node2(v_a_434_, v___x_441_, v___x_464_, v___x_471_);
v___x_473_ = l_Lean_Syntax_node1(v_a_434_, v___x_456_, v___x_472_);
v___x_474_ = l_Lean_Syntax_node7(v_a_434_, v___x_437_, v___x_440_, v___x_443_, v___x_443_, v___x_443_, v___x_453_, v___x_455_, v___x_473_);
v_e_353_ = v___x_474_;
v___y_354_ = v_a_435_;
goto v___jp_352_;
}
}
}
else
{
lean_object* v_a_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v___x_415_);
lean_dec(v___x_414_);
lean_dec(v_e_378_);
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_snd_365_);
v_a_477_ = lean_ctor_get(v___x_433_, 0);
v_a_478_ = lean_ctor_get(v___x_433_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_433_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_inc(v_a_477_);
lean_dec(v___x_433_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_477_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
else
{
lean_object* v_ref_486_; lean_object* v___x_487_; 
v_ref_486_ = lean_ctor_get(v___y_379_, 5);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_486_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc_n(v_a_488_, 2);
v_a_489_ = lean_ctor_get(v___x_487_, 1);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_487_, 2);
v___x_490_ = l_Lean_Syntax_getArg(v___x_415_, v___x_375_);
lean_dec(v___x_415_);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 2);
lean_ctor_set(v___x_372_, 1, v___x_492_);
lean_ctor_set(v___x_372_, 0, v_a_488_);
v___x_494_ = v___x_372_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_488_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_524_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc_n(v_a_488_, 4);
v___x_497_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_497_, 0, v_a_488_);
lean_ctor_set(v___x_497_, 1, v___x_495_);
lean_ctor_set(v___x_497_, 2, v___x_496_);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref(v___x_497_);
v___x_499_ = l_Lean_Syntax_node2(v_a_488_, v___x_498_, v___x_497_, v___x_490_);
v___x_500_ = l_Lean_Syntax_node1(v_a_488_, v___x_495_, v___x_499_);
v___x_501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 2);
lean_ctor_set(v___x_367_, 1, v___x_501_);
lean_ctor_set(v___x_367_, 0, v_a_488_);
v___x_503_ = v___x_367_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_488_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_523_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
lean_inc_n(v_a_488_, 12);
v___x_507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_507_, 0, v_a_488_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = l_Lean_Syntax_node1(v_a_488_, v___x_495_, v___x_414_);
v___x_509_ = l_Lean_Syntax_node1(v_a_488_, v___x_495_, v___x_508_);
v___x_510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_511_, 0, v_a_488_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
lean_inc_ref(v___x_511_);
lean_inc_ref(v___x_507_);
v___x_512_ = l_Lean_Syntax_node4(v_a_488_, v___x_505_, v___x_507_, v___x_509_, v___x_511_, v_snd_365_);
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_515_, 0, v_a_488_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l_Lean_Syntax_node1(v_a_488_, v___x_513_, v___x_515_);
v___x_517_ = l_Lean_Syntax_node1(v_a_488_, v___x_495_, v___x_516_);
v___x_518_ = l_Lean_Syntax_node1(v_a_488_, v___x_495_, v___x_517_);
v___x_519_ = l_Lean_Syntax_node4(v_a_488_, v___x_505_, v___x_507_, v___x_518_, v___x_511_, v_e_378_);
v___x_520_ = l_Lean_Syntax_node2(v_a_488_, v___x_495_, v___x_512_, v___x_519_);
v___x_521_ = l_Lean_Syntax_node1(v_a_488_, v___x_504_, v___x_520_);
lean_inc_ref_n(v___x_497_, 2);
v___x_522_ = l_Lean_Syntax_node7(v_a_488_, v___x_491_, v___x_494_, v___x_497_, v___x_497_, v___x_497_, v___x_500_, v___x_503_, v___x_521_);
v_e_353_ = v___x_522_;
v___y_354_ = v_a_489_;
goto v___jp_352_;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v___x_415_);
lean_dec(v___x_414_);
lean_dec(v_e_378_);
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_snd_365_);
v_a_525_ = lean_ctor_get(v___x_487_, 0);
v_a_526_ = lean_ctor_get(v___x_487_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_487_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_inc(v_a_525_);
lean_dec(v___x_487_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_525_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
}
}
}
v___jp_352_:
{
uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; size_t v___x_358_; size_t v___x_359_; 
v___x_355_ = 0;
v___x_356_ = lean_box(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_e_353_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_348_, v___x_358_);
v_i_348_ = v___x_359_;
v_b_349_ = v___x_357_;
v___y_351_ = v___y_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___boxed(lean_object* v_as_558_, lean_object* v_sz_559_, lean_object* v_i_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
size_t v_sz_boxed_564_; size_t v_i_boxed_565_; lean_object* v_res_566_; 
v_sz_boxed_564_ = lean_unbox_usize(v_sz_559_);
lean_dec(v_sz_559_);
v_i_boxed_565_ = lean_unbox_usize(v_i_560_);
lean_dec(v_i_560_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v_as_558_, v_sz_boxed_564_, v_i_boxed_565_, v_b_561_, v___y_562_, v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_as_558_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(size_t v_sz_570_, size_t v_i_571_, lean_object* v_bs_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_lt(v_i_571_, v_sz_570_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v_bs_572_);
return v___x_574_;
}
else
{
lean_object* v_v_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_v_575_ = lean_array_uget(v_bs_572_, v_i_571_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1));
lean_inc(v_v_575_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_v_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v_v_575_);
lean_dec_ref(v_bs_572_);
v___x_578_ = lean_box(0);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = l_Lean_Syntax_getArg(v_v_575_, v___x_579_);
lean_inc(v___x_580_);
v___x_581_ = l_Lean_Syntax_isOfKind(v___x_580_, v___x_576_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v___x_580_);
lean_dec(v_v_575_);
lean_dec_ref(v_bs_572_);
v___x_582_ = lean_box(0);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_bs_x27_585_; lean_object* v_tks_586_; lean_object* v_conds_587_; lean_object* v_ts_588_; lean_object* v___x_589_; lean_object* v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_unsigned_to_nat(3u);
v_bs_x27_585_ = lean_array_uset(v_bs_572_, v_i_571_, v___x_579_);
v_tks_586_ = l_Lean_Syntax_getArg(v___x_580_, v___x_583_);
lean_dec(v___x_580_);
v_conds_587_ = l_Lean_Syntax_getArg(v_v_575_, v___x_583_);
v_ts_588_ = l_Lean_Syntax_getArg(v_v_575_, v___x_584_);
lean_dec(v_v_575_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_conds_587_);
lean_ctor_set(v___x_589_, 1, v_ts_588_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_tks_586_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_add(v_i_571_, v___x_591_);
v___x_593_ = lean_array_uset(v_bs_x27_585_, v_i_571_, v___x_590_);
v_i_571_ = v___x_592_;
v_bs_572_ = v___x_593_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___boxed(lean_object* v_sz_595_, lean_object* v_i_596_, lean_object* v_bs_597_){
_start:
{
size_t v_sz_boxed_598_; size_t v_i_boxed_599_; lean_object* v_res_600_; 
v_sz_boxed_598_ = lean_unbox_usize(v_sz_595_);
lean_dec(v_sz_595_);
v_i_boxed_599_ = lean_unbox_usize(v_i_596_);
lean_dec(v_i_596_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_boxed_598_, v_i_boxed_599_, v_bs_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(size_t v_sz_601_, size_t v_i_602_, lean_object* v_bs_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_lt(v_i_602_, v_sz_601_);
if (v___x_604_ == 0)
{
return v_bs_603_;
}
else
{
lean_object* v_v_605_; lean_object* v_snd_606_; lean_object* v_fst_607_; lean_object* v___x_608_; lean_object* v_bs_x27_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; 
v_v_605_ = lean_array_uget_borrowed(v_bs_603_, v_i_602_);
v_snd_606_ = lean_ctor_get(v_v_605_, 1);
v_fst_607_ = lean_ctor_get(v_snd_606_, 0);
lean_inc(v_fst_607_);
v___x_608_ = lean_unsigned_to_nat(0u);
v_bs_x27_609_ = lean_array_uset(v_bs_603_, v_i_602_, v___x_608_);
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_add(v_i_602_, v___x_610_);
v___x_612_ = lean_array_uset(v_bs_x27_609_, v_i_602_, v_fst_607_);
v_i_602_ = v___x_611_;
v_bs_603_ = v___x_612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2___boxed(lean_object* v_sz_614_, lean_object* v_i_615_, lean_object* v_bs_616_){
_start:
{
size_t v_sz_boxed_617_; size_t v_i_boxed_618_; lean_object* v_res_619_; 
v_sz_boxed_617_ = lean_unbox_usize(v_sz_614_);
lean_dec(v_sz_614_);
v_i_boxed_618_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_boxed_617_, v_i_boxed_618_, v_bs_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(size_t v_sz_620_, size_t v_i_621_, lean_object* v_bs_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_623_ == 0)
{
return v_bs_622_;
}
else
{
lean_object* v_v_624_; lean_object* v_snd_625_; lean_object* v_snd_626_; lean_object* v___x_627_; lean_object* v_bs_x27_628_; size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v_v_624_ = lean_array_uget_borrowed(v_bs_622_, v_i_621_);
v_snd_625_ = lean_ctor_get(v_v_624_, 1);
v_snd_626_ = lean_ctor_get(v_snd_625_, 1);
lean_inc(v_snd_626_);
v___x_627_ = lean_unsigned_to_nat(0u);
v_bs_x27_628_ = lean_array_uset(v_bs_622_, v_i_621_, v___x_627_);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_621_, v___x_629_);
v___x_631_ = lean_array_uset(v_bs_x27_628_, v_i_621_, v_snd_626_);
v_i_621_ = v___x_630_;
v_bs_622_ = v___x_631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1___boxed(lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_bs_635_){
_start:
{
size_t v_sz_boxed_636_; size_t v_i_boxed_637_; lean_object* v_res_638_; 
v_sz_boxed_636_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_637_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_boxed_636_, v_i_boxed_637_, v_bs_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf(lean_object* v_stx_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_651_; uint8_t v_eIsSeq_652_; 
v___x_651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
lean_inc(v_stx_648_);
v_eIsSeq_652_ = l_Lean_Syntax_isOfKind(v_stx_648_, v___x_651_);
if (v_eIsSeq_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec(v_stx_648_);
v___x_653_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v_tk_655_; lean_object* v___x_656_; lean_object* v_cond_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v_tk_655_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(1u);
v_cond_657_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_656_);
v___x_658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(v_cond_657_);
v___x_659_ = l_Lean_Syntax_isOfKind(v_cond_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; size_t v_sz_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_660_ = lean_unsigned_to_nat(4u);
v___x_661_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_660_);
v___x_662_ = l_Lean_Syntax_getArgs(v___x_661_);
lean_dec(v___x_661_);
v_sz_663_ = lean_array_size(v___x_662_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_663_, v___x_664_, v___x_662_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; 
lean_dec(v_cond_657_);
lean_dec(v_tk_655_);
lean_dec(v_stx_648_);
v___x_666_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_666_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_668_; lean_object* v_t_669_; size_t v_sz_670_; lean_object* v_ts_671_; lean_object* v_conds_672_; lean_object* v___y_674_; lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_val_667_ = lean_ctor_get(v___x_665_, 0);
lean_inc_n(v_val_667_, 2);
lean_dec_ref_known(v___x_665_, 1);
v___x_668_ = lean_unsigned_to_nat(3u);
v_t_669_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_668_);
v_sz_670_ = lean_array_size(v_val_667_);
v_ts_671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_670_, v___x_664_, v_val_667_);
v_conds_672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_670_, v___x_664_, v_val_667_);
v___x_705_ = lean_unsigned_to_nat(5u);
v___x_706_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_705_);
lean_dec(v_stx_648_);
v___x_707_ = l_Lean_Syntax_isNone(v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; uint8_t v___x_709_; 
lean_dec(v_tk_655_);
v___x_708_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_706_);
v___x_709_ = l_Lean_Syntax_matchesNull(v___x_706_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_dec(v___x_706_);
lean_dec_ref(v_conds_672_);
lean_dec_ref(v_ts_671_);
lean_dec(v_t_669_);
lean_dec(v_cond_657_);
v___x_710_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_710_;
}
else
{
lean_object* v_e_x3f_711_; 
v_e_x3f_711_ = l_Lean_Syntax_getArg(v___x_706_, v___x_656_);
lean_dec(v___x_706_);
v___y_674_ = v_a_649_;
v_a_675_ = v_e_x3f_711_;
v_a_676_ = v_a_650_;
goto v___jp_673_;
}
}
else
{
lean_object* v_ref_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v___x_706_);
v_ref_712_ = lean_ctor_get(v_a_649_, 5);
v___x_713_ = l_Lean_SourceInfo_fromRef(v_ref_712_, v___x_659_);
v___x_714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42));
v___x_717_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__2));
v___x_718_ = l_Lean_SourceInfo_fromRef(v_tk_655_, v_eIsSeq_652_);
lean_dec(v_tk_655_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__3));
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_inc_n(v___x_713_, 4);
v___x_721_ = l_Lean_Syntax_node1(v___x_713_, v___x_717_, v___x_720_);
v___x_722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_723_, 0, v___x_713_);
lean_ctor_set(v___x_723_, 1, v___x_715_);
lean_ctor_set(v___x_723_, 2, v___x_722_);
v___x_724_ = l_Lean_Syntax_node2(v___x_713_, v___x_716_, v___x_721_, v___x_723_);
v___x_725_ = l_Lean_Syntax_node1(v___x_713_, v___x_715_, v___x_724_);
v___x_726_ = l_Lean_Syntax_node1(v___x_713_, v___x_714_, v___x_725_);
v___y_674_ = v_a_649_;
v_a_675_ = v___x_726_;
v_a_676_ = v_a_650_;
goto v___jp_673_;
}
v___jp_673_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; size_t v_sz_684_; lean_object* v___x_685_; 
v___x_677_ = l_Array_reverse___redArg(v_conds_672_);
v___x_678_ = lean_array_push(v___x_677_, v_cond_657_);
v___x_679_ = l_Array_reverse___redArg(v_ts_671_);
v___x_680_ = lean_array_push(v___x_679_, v_t_669_);
v___x_681_ = l_Array_zip___redArg(v___x_678_, v___x_680_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_678_);
v___x_682_ = lean_box(v_eIsSeq_652_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_a_675_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v_sz_684_ = lean_array_size(v___x_681_);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_659_, v___x_681_, v_sz_684_, v___x_664_, v___x_683_, v___y_674_, v_a_676_);
lean_dec_ref(v___x_681_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_a_687_ = lean_ctor_get(v___x_685_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v___x_685_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_fst_691_; lean_object* v___x_693_; 
v_fst_691_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_fst_691_);
lean_dec(v_a_686_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v_fst_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_fst_691_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_a_687_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_696_ = lean_ctor_get(v___x_685_, 0);
v_a_697_ = lean_ctor_get(v___x_685_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_685_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_inc(v_a_696_);
lean_dec(v___x_685_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_696_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_t_729_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v_a_734_; lean_object* v_a_735_; lean_object* v_conds_766_; lean_object* v_ts_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = lean_unsigned_to_nat(3u);
v_t_729_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_728_);
v___x_786_ = lean_unsigned_to_nat(4u);
v___x_787_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_786_);
lean_inc(v___x_787_);
v___x_788_ = l_Lean_Syntax_matchesNull(v___x_787_, v___x_654_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; size_t v_sz_790_; size_t v___x_791_; lean_object* v___x_792_; 
v___x_789_ = l_Lean_Syntax_getArgs(v___x_787_);
lean_dec(v___x_787_);
v_sz_790_ = lean_array_size(v___x_789_);
v___x_791_ = ((size_t)0ULL);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_790_, v___x_791_, v___x_789_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; 
lean_dec(v_t_729_);
lean_dec(v_cond_657_);
lean_dec(v_tk_655_);
lean_dec(v_stx_648_);
v___x_793_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_793_;
}
else
{
lean_object* v_val_794_; size_t v_sz_795_; lean_object* v_ts_796_; lean_object* v_conds_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_val_794_ = lean_ctor_get(v___x_792_, 0);
lean_inc_n(v_val_794_, 2);
lean_dec_ref_known(v___x_792_, 1);
v_sz_795_ = lean_array_size(v_val_794_);
v_ts_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_795_, v___x_791_, v_val_794_);
v_conds_797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_795_, v___x_791_, v_val_794_);
v___x_798_ = lean_unsigned_to_nat(5u);
v___x_799_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_798_);
lean_dec(v_stx_648_);
v___x_800_ = l_Lean_Syntax_isNone(v___x_799_);
if (v___x_800_ == 0)
{
uint8_t v___x_801_; 
lean_dec(v_tk_655_);
lean_inc(v___x_799_);
v___x_801_ = l_Lean_Syntax_matchesNull(v___x_799_, v___x_727_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v___x_799_);
lean_dec_ref(v_conds_797_);
lean_dec_ref(v_ts_796_);
lean_dec(v_t_729_);
lean_dec(v_cond_657_);
v___x_802_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_802_;
}
else
{
lean_object* v_e_x3f_803_; 
v_e_x3f_803_ = l_Lean_Syntax_getArg(v___x_799_, v___x_656_);
lean_dec(v___x_799_);
v___y_731_ = v_a_649_;
v___y_732_ = v_ts_796_;
v___y_733_ = v_conds_797_;
v_a_734_ = v_e_x3f_803_;
v_a_735_ = v_a_650_;
goto v___jp_730_;
}
}
else
{
lean_dec(v___x_799_);
v_conds_766_ = v_conds_797_;
v_ts_767_ = v_ts_796_;
v___y_768_ = v_a_649_;
v___y_769_ = v_a_650_;
goto v___jp_765_;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_unsigned_to_nat(5u);
v___x_805_ = l_Lean_Syntax_getArg(v_stx_648_, v___x_804_);
lean_dec(v_stx_648_);
lean_inc(v___x_805_);
v___x_806_ = l_Lean_Syntax_matchesNull(v___x_805_, v___x_727_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; size_t v_sz_808_; size_t v___x_809_; lean_object* v___x_810_; 
v___x_807_ = l_Lean_Syntax_getArgs(v___x_787_);
lean_dec(v___x_787_);
v_sz_808_ = lean_array_size(v___x_807_);
v___x_809_ = ((size_t)0ULL);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_808_, v___x_809_, v___x_807_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; 
lean_dec(v___x_805_);
lean_dec(v_t_729_);
lean_dec(v_cond_657_);
lean_dec(v_tk_655_);
v___x_811_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_811_;
}
else
{
lean_object* v_val_812_; size_t v_sz_813_; lean_object* v_ts_814_; lean_object* v_conds_815_; uint8_t v___x_816_; 
v_val_812_ = lean_ctor_get(v___x_810_, 0);
lean_inc_n(v_val_812_, 2);
lean_dec_ref_known(v___x_810_, 1);
v_sz_813_ = lean_array_size(v_val_812_);
v_ts_814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_813_, v___x_809_, v_val_812_);
v_conds_815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_813_, v___x_809_, v_val_812_);
v___x_816_ = l_Lean_Syntax_isNone(v___x_805_);
if (v___x_816_ == 0)
{
lean_dec(v_tk_655_);
if (v___x_806_ == 0)
{
lean_object* v___x_817_; 
lean_dec_ref(v_conds_815_);
lean_dec_ref(v_ts_814_);
lean_dec(v___x_805_);
lean_dec(v_t_729_);
lean_dec(v_cond_657_);
v___x_817_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_817_;
}
else
{
lean_object* v_e_x3f_818_; 
v_e_x3f_818_ = l_Lean_Syntax_getArg(v___x_805_, v___x_656_);
lean_dec(v___x_805_);
v___y_731_ = v_a_649_;
v___y_732_ = v_ts_814_;
v___y_733_ = v_conds_815_;
v_a_734_ = v_e_x3f_818_;
v_a_735_ = v_a_650_;
goto v___jp_730_;
}
}
else
{
lean_dec(v___x_805_);
v_conds_766_ = v_conds_815_;
v_ts_767_ = v_ts_814_;
v___y_768_ = v_a_649_;
v___y_769_ = v_a_650_;
goto v___jp_765_;
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v___x_805_);
lean_dec(v___x_787_);
lean_dec(v_t_729_);
lean_dec(v_cond_657_);
lean_dec(v_tk_655_);
v___x_819_ = l_Lean_Macro_throwUnsupported___redArg(v_a_650_);
return v___x_819_;
}
}
v___jp_730_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; size_t v_sz_743_; size_t v___x_744_; lean_object* v___x_745_; 
v___x_736_ = l_Array_reverse___redArg(v___y_733_);
v___x_737_ = lean_array_push(v___x_736_, v_cond_657_);
v___x_738_ = l_Array_reverse___redArg(v___y_732_);
v___x_739_ = lean_array_push(v___x_738_, v_t_729_);
v___x_740_ = l_Array_zip___redArg(v___x_737_, v___x_739_);
lean_dec_ref(v___x_739_);
lean_dec_ref(v___x_737_);
v___x_741_ = lean_box(v_eIsSeq_652_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_a_734_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v_sz_743_ = lean_array_size(v___x_740_);
v___x_744_ = ((size_t)0ULL);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v___x_740_, v_sz_743_, v___x_744_, v___x_742_, v___y_731_, v_a_735_);
lean_dec_ref(v___x_740_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_a_747_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_fst_751_; lean_object* v___x_753_; 
v_fst_751_ = lean_ctor_get(v_a_746_, 0);
lean_inc(v_fst_751_);
lean_dec(v_a_746_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v_fst_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_fst_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_a_747_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
v_a_756_ = lean_ctor_get(v___x_745_, 0);
v_a_757_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_745_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_inc(v_a_756_);
lean_dec(v___x_745_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
v___jp_765_:
{
lean_object* v_ref_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_ref_770_ = lean_ctor_get(v___y_768_, 5);
v___x_771_ = 0;
v___x_772_ = l_Lean_SourceInfo_fromRef(v_ref_770_, v___x_771_);
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42));
v___x_776_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__2));
v___x_777_ = l_Lean_SourceInfo_fromRef(v_tk_655_, v_eIsSeq_652_);
lean_dec(v_tk_655_);
v___x_778_ = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__3));
v___x_779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
lean_inc_n(v___x_772_, 4);
v___x_780_ = l_Lean_Syntax_node1(v___x_772_, v___x_776_, v___x_779_);
v___x_781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v___x_772_);
lean_ctor_set(v___x_782_, 1, v___x_774_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
v___x_783_ = l_Lean_Syntax_node2(v___x_772_, v___x_775_, v___x_780_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node1(v___x_772_, v___x_774_, v___x_783_);
v___x_785_ = l_Lean_Syntax_node1(v___x_772_, v___x_773_, v___x_784_);
v___y_731_ = v___y_768_;
v___y_732_ = v_ts_767_;
v___y_733_ = v_conds_766_;
v_a_734_ = v___x_785_;
v_a_735_ = v___y_769_;
goto v___jp_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___boxed(lean_object* v_stx_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Elab_Do_expandDoIf(v_stx_820_, v_a_821_, v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1(){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_833_ = l_Lean_Elab_macroAttribute;
v___x_834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_835_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3));
v___x_836_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoIf___boxed), 3, 0);
v___x_837_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_833_, v___x_834_, v___x_835_, v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___boxed(lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3(){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3));
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0));
v___x_844_ = l_Lean_addBuiltinDocString(v___x_842_, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___boxed(lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(lean_object* v_cond_850_, lean_object* v_then___851_, uint8_t v___x_852_, lean_object* v_else___853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_doBlockResultType_862_; lean_object* v___x_863_; 
v_doBlockResultType_862_ = lean_ctor_get(v___y_854_, 3);
lean_inc_ref(v_doBlockResultType_862_);
v___x_863_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_862_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_884_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_884_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_884_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_884_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_ref_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v_ref_868_ = lean_ctor_get(v___y_859_, 5);
v___x_869_ = 0;
v___x_870_ = l_Lean_SourceInfo_fromRef(v_ref_868_, v___x_869_);
v___x_871_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1));
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc_n(v___x_870_, 3);
v___x_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_870_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_870_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_870_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_Syntax_node6(v___x_870_, v___x_871_, v___x_873_, v_cond_850_, v___x_875_, v_then___851_, v___x_877_, v_else___853_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 1);
v___x_880_ = v___x_866_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_864_);
v___x_880_ = v_reuseFailAlloc_883_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_box(0);
v___x_882_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_878_, v___x_880_, v___x_852_, v___x_852_, v___x_881_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_882_;
}
}
}
else
{
lean_dec(v_else___853_);
lean_dec(v_then___851_);
lean_dec(v_cond_850_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed(lean_object* v_cond_885_, lean_object* v_then___886_, lean_object* v___x_887_, lean_object* v_else___888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v___x_3198__boxed_897_; lean_object* v_res_898_; 
v___x_3198__boxed_897_ = lean_unbox(v___x_887_);
v_res_898_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(v_cond_885_, v_then___886_, v___x_3198__boxed_897_, v_else___888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_898_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1));
v___x_903_ = l_Lean_MessageData_ofFormat(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(lean_object* v_cond_904_, uint8_t v___x_905_, lean_object* v_elseSeq_906_, lean_object* v_dec_907_, lean_object* v_then___908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_917_ = lean_box(v___x_905_);
v___f_918_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed), 12, 3);
lean_closure_set(v___f_918_, 0, v_cond_904_);
lean_closure_set(v___f_918_, 1, v_then___908_);
lean_closure_set(v___f_918_, 2, v___x_917_);
v___x_919_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
v___x_920_ = lean_box(v___x_905_);
v___x_921_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_921_, 0, v_elseSeq_906_);
lean_closure_set(v___x_921_, 1, v_dec_907_);
lean_closure_set(v___x_921_, 2, v___x_920_);
v___x_922_ = lean_box(0);
v___x_923_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_919_, v___x_921_, v___f_918_, v___x_922_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed(lean_object* v_cond_924_, lean_object* v___x_925_, lean_object* v_elseSeq_926_, lean_object* v_dec_927_, lean_object* v_then___928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v___x_3281__boxed_937_; lean_object* v_res_938_; 
v___x_3281__boxed_937_ = lean_unbox(v___x_925_);
v_res_938_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(v_cond_924_, v___x_3281__boxed_937_, v_elseSeq_926_, v_dec_927_, v_then___928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_938_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1));
v___x_943_ = l_Lean_MessageData_ofFormat(v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(lean_object* v_cond_944_, lean_object* v_thenSeq_945_, lean_object* v_elseSeq_946_, lean_object* v_dec_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___f_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_956_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
v___x_957_ = 1;
v___x_958_ = lean_box(v___x_957_);
lean_inc_ref(v_dec_947_);
v___f_959_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed), 13, 4);
lean_closure_set(v___f_959_, 0, v_cond_944_);
lean_closure_set(v___f_959_, 1, v___x_958_);
lean_closure_set(v___f_959_, 2, v_elseSeq_946_);
lean_closure_set(v___f_959_, 3, v_dec_947_);
v___x_960_ = lean_box(v___x_957_);
v___x_961_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_961_, 0, v_thenSeq_945_);
lean_closure_set(v___x_961_, 1, v_dec_947_);
lean_closure_set(v___x_961_, 2, v___x_960_);
v___x_962_ = lean_box(0);
v___x_963_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_956_, v___x_961_, v___f_959_, v___x_962_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___boxed(lean_object* v_cond_964_, lean_object* v_thenSeq_965_, lean_object* v_elseSeq_966_, lean_object* v_dec_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(v_cond_964_, v_thenSeq_965_, v_elseSeq_966_, v_dec_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec_ref(v_a_968_);
return v_res_976_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_box(0);
v___x_978_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg(){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___boxed(lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(lean_object* v_00_u03b1_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___boxed(lean_object* v_00_u03b1_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(v_00_u03b1_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(lean_object* v_elseSeq_1005_, lean_object* v_dec_1006_, lean_object* v_thenSeq_1007_, uint8_t v_then___1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = 1;
if (v_then___1008_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_thenSeq_1007_);
v___x_1018_ = l_Lean_Elab_Do_elabDoSeq(v_elseSeq_1005_, v_dec_1006_, v___x_1017_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; 
lean_dec(v_elseSeq_1005_);
v___x_1019_ = l_Lean_Elab_Do_elabDoSeq(v_thenSeq_1007_, v_dec_1006_, v___x_1017_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed(lean_object* v_elseSeq_1020_, lean_object* v_dec_1021_, lean_object* v_thenSeq_1022_, lean_object* v_then___1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
uint8_t v_then___00boxed_1032_; lean_object* v_res_1033_; 
v_then___00boxed_1032_ = lean_unbox(v_then___1023_);
v_res_1033_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(v_elseSeq_1020_, v_dec_1021_, v_thenSeq_1022_, v_then___00boxed_1032_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(lean_object* v_h_1045_, lean_object* v_cond_1046_, lean_object* v_then___1047_, uint8_t v___x_1048_, lean_object* v_else___1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_doBlockResultType_1058_; lean_object* v___x_1059_; 
v_doBlockResultType_1058_ = lean_ctor_get(v___y_1050_, 3);
lean_inc_ref(v_doBlockResultType_1058_);
v___x_1059_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1058_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1114_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1114_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1114_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
lean_inc(v_h_1045_);
v___x_1065_ = l_Lean_Syntax_isOfKind(v_h_1045_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1));
lean_inc(v_h_1045_);
v___x_1067_ = l_Lean_Syntax_isOfKind(v_h_1045_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_del_object(v___x_1062_);
lean_dec(v_a_1060_);
lean_dec(v_else___1049_);
lean_dec(v_then___1047_);
lean_dec(v_cond_1046_);
lean_dec(v_h_1045_);
v___x_1068_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1068_;
}
else
{
lean_object* v_ref_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v_ref_1069_ = lean_ctor_get(v___y_1055_, 5);
v___x_1070_ = l_Lean_SourceInfo_fromRef(v_ref_1069_, v___x_1065_);
v___x_1071_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
v___x_1072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc_n(v___x_1070_, 5);
v___x_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
v___x_1075_ = l_Lean_Syntax_node1(v___x_1070_, v___x_1074_, v_h_1045_);
v___x_1076_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
v___x_1077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1070_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_1079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1070_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_1081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1070_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_Syntax_node8(v___x_1070_, v___x_1071_, v___x_1073_, v___x_1075_, v___x_1077_, v_cond_1046_, v___x_1079_, v_then___1047_, v___x_1081_, v_else___1049_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
v___x_1084_ = v___x_1062_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1060_);
v___x_1084_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1082_, v___x_1084_, v___x_1048_, v___x_1048_, v___x_1085_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1086_;
}
}
}
else
{
lean_object* v_ref_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v_ref_1088_ = lean_ctor_get(v___y_1055_, 5);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = l_Lean_Syntax_getArg(v_h_1045_, v___x_1089_);
lean_dec(v_h_1045_);
v___x_1091_ = 0;
v___x_1092_ = l_Lean_SourceInfo_fromRef(v_ref_1088_, v___x_1091_);
v___x_1093_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
v___x_1094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc_n(v___x_1092_, 6);
v___x_1095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
v___x_1097_ = l_Lean_SourceInfo_fromRef(v___x_1090_, v___x_1048_);
lean_dec(v___x_1090_);
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_1099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_Syntax_node1(v___x_1092_, v___x_1064_, v___x_1099_);
v___x_1101_ = l_Lean_Syntax_node1(v___x_1092_, v___x_1096_, v___x_1100_);
v___x_1102_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
v___x_1103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1092_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_1105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1092_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
v___x_1107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1092_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l_Lean_Syntax_node8(v___x_1092_, v___x_1093_, v___x_1095_, v___x_1101_, v___x_1103_, v_cond_1046_, v___x_1105_, v_then___1047_, v___x_1107_, v_else___1049_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
v___x_1110_ = v___x_1062_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1060_);
v___x_1110_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1108_, v___x_1110_, v___x_1048_, v___x_1048_, v___x_1111_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1112_;
}
}
}
}
else
{
lean_dec(v_else___1049_);
lean_dec(v_then___1047_);
lean_dec(v_cond_1046_);
lean_dec(v_h_1045_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed(lean_object* v_h_1115_, lean_object* v_cond_1116_, lean_object* v_then___1117_, lean_object* v___x_1118_, lean_object* v_else___1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_7828__boxed_1128_; lean_object* v_res_1129_; 
v___x_7828__boxed_1128_ = lean_unbox(v___x_1118_);
v_res_1129_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(v_h_1115_, v_cond_1116_, v_then___1117_, v___x_7828__boxed_1128_, v_else___1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(lean_object* v_h_1130_, lean_object* v_cond_1131_, uint8_t v___x_1132_, lean_object* v_elabDiteBranch_1133_, lean_object* v_then___1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1143_ = lean_box(v___x_1132_);
v___f_1144_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1144_, 0, v_h_1130_);
lean_closure_set(v___f_1144_, 1, v_cond_1131_);
lean_closure_set(v___f_1144_, 2, v_then___1134_);
lean_closure_set(v___f_1144_, 3, v___x_1143_);
v___x_1145_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
v___x_1146_ = 0;
v___x_1147_ = lean_box(v___x_1146_);
v___x_1148_ = lean_apply_1(v_elabDiteBranch_1133_, v___x_1147_);
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_1145_, v___x_1148_, v___f_1144_, v___x_1149_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed(lean_object* v_h_1151_, lean_object* v_cond_1152_, lean_object* v___x_1153_, lean_object* v_elabDiteBranch_1154_, lean_object* v_then___1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_7980__boxed_1164_; lean_object* v_res_1165_; 
v___x_7980__boxed_1164_ = lean_unbox(v___x_1153_);
v_res_1165_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(v_h_1151_, v_cond_1152_, v___x_7980__boxed_1164_, v_elabDiteBranch_1154_, v_then___1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(lean_object* v_h_1166_, lean_object* v_cond_1167_, lean_object* v_thenSeq_1168_, lean_object* v_elseSeq_1169_, lean_object* v_dec_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_elabDiteBranch_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_inc(v_thenSeq_1168_);
lean_inc_ref(v_dec_1170_);
lean_inc(v_elseSeq_1169_);
v_elabDiteBranch_1179_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 3);
lean_closure_set(v_elabDiteBranch_1179_, 0, v_elseSeq_1169_);
lean_closure_set(v_elabDiteBranch_1179_, 1, v_dec_1170_);
lean_closure_set(v_elabDiteBranch_1179_, 2, v_thenSeq_1168_);
v___x_1180_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
v___x_1181_ = 1;
v___x_1182_ = lean_box(v___x_1181_);
v___f_1183_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed), 13, 4);
lean_closure_set(v___f_1183_, 0, v_h_1166_);
lean_closure_set(v___f_1183_, 1, v_cond_1167_);
lean_closure_set(v___f_1183_, 2, v___x_1182_);
lean_closure_set(v___f_1183_, 3, v_elabDiteBranch_1179_);
v___x_1184_ = lean_box(v___x_1181_);
v___x_1185_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 4);
lean_closure_set(v___x_1185_, 0, v_elseSeq_1169_);
lean_closure_set(v___x_1185_, 1, v_dec_1170_);
lean_closure_set(v___x_1185_, 2, v_thenSeq_1168_);
lean_closure_set(v___x_1185_, 3, v___x_1184_);
v___x_1186_ = lean_box(0);
v___x_1187_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_1180_, v___x_1185_, v___f_1183_, v___x_1186_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___boxed(lean_object* v_h_1188_, lean_object* v_cond_1189_, lean_object* v_thenSeq_1190_, lean_object* v_elseSeq_1191_, lean_object* v_dec_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(v_h_1188_, v_cond_1189_, v_thenSeq_1190_, v_elseSeq_1191_, v_dec_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec_ref(v_a_1193_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0(lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v_thenSeq_1209_, lean_object* v_elseSeq_1210_, lean_object* v_dec_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7));
v___x_1221_ = l_Lean_Name_mkStr4(v___x_1202_, v___x_1203_, v___x_1204_, v___x_1220_);
lean_inc(v___x_1205_);
v___x_1222_ = l_Lean_Syntax_isOfKind(v___x_1205_, v___x_1221_);
lean_dec(v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_dec_ref(v_dec_1211_);
lean_dec(v_elseSeq_1210_);
lean_dec(v_thenSeq_1209_);
lean_dec(v___x_1205_);
v___x_1223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = l_Lean_Syntax_getArg(v___x_1205_, v___x_1206_);
lean_inc(v___x_1224_);
v___x_1225_ = l_Lean_Syntax_matchesNull(v___x_1224_, v___x_1206_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
lean_inc(v___x_1224_);
v___x_1226_ = l_Lean_Syntax_matchesNull(v___x_1224_, v___x_1207_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; 
lean_dec(v___x_1224_);
lean_dec_ref(v_dec_1211_);
lean_dec(v_elseSeq_1210_);
lean_dec(v_thenSeq_1209_);
lean_dec(v___x_1205_);
v___x_1227_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = l_Lean_Syntax_getArg(v___x_1224_, v___x_1206_);
lean_dec(v___x_1224_);
v___x_1229_ = l_Lean_Syntax_getArg(v___x_1205_, v___x_1208_);
lean_dec(v___x_1205_);
v___x_1230_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(v___x_1228_, v___x_1229_, v_thenSeq_1209_, v_elseSeq_1210_, v_dec_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1230_;
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v___x_1224_);
v___x_1231_ = l_Lean_Syntax_getArg(v___x_1205_, v___x_1208_);
lean_dec(v___x_1205_);
v___x_1232_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(v___x_1231_, v_thenSeq_1209_, v_elseSeq_1210_, v_dec_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0___boxed(lean_object** _args){
lean_object* v___x_1233_ = _args[0];
lean_object* v___x_1234_ = _args[1];
lean_object* v___x_1235_ = _args[2];
lean_object* v___x_1236_ = _args[3];
lean_object* v___x_1237_ = _args[4];
lean_object* v___x_1238_ = _args[5];
lean_object* v___x_1239_ = _args[6];
lean_object* v_thenSeq_1240_ = _args[7];
lean_object* v_elseSeq_1241_ = _args[8];
lean_object* v_dec_1242_ = _args[9];
lean_object* v___y_1243_ = _args[10];
lean_object* v___y_1244_ = _args[11];
lean_object* v___y_1245_ = _args[12];
lean_object* v___y_1246_ = _args[13];
lean_object* v___y_1247_ = _args[14];
lean_object* v___y_1248_ = _args[15];
lean_object* v___y_1249_ = _args[16];
lean_object* v___y_1250_ = _args[17];
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Elab_Do_elabDoIf___lam__0(v___x_1233_, v___x_1234_, v___x_1235_, v___x_1236_, v___x_1237_, v___x_1238_, v___x_1239_, v_thenSeq_1240_, v_elseSeq_1241_, v_dec_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___x_1239_);
lean_dec(v___x_1238_);
lean_dec(v___x_1237_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf(lean_object* v_stx_1252_, lean_object* v_dec_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0));
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1));
v___x_1264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2));
v___x_1265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
lean_inc(v_stx_1252_);
v___x_1266_ = l_Lean_Syntax_isOfKind(v_stx_1252_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_dec_1253_);
lean_dec(v_stx_1252_);
v___x_1267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_unsigned_to_nat(4u);
v___x_1270_ = l_Lean_Syntax_getArg(v_stx_1252_, v___x_1269_);
v___x_1271_ = l_Lean_Syntax_matchesNull(v___x_1270_, v___x_1268_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_dec_ref(v_dec_1253_);
lean_dec(v_stx_1252_);
v___x_1272_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1273_ = lean_unsigned_to_nat(2u);
v___x_1274_ = lean_unsigned_to_nat(5u);
v___x_1275_ = l_Lean_Syntax_getArg(v_stx_1252_, v___x_1274_);
lean_inc(v___x_1275_);
v___x_1276_ = l_Lean_Syntax_matchesNull(v___x_1275_, v___x_1273_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
lean_dec(v___x_1275_);
lean_dec_ref(v_dec_1253_);
lean_dec(v_stx_1252_);
v___x_1277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; lean_object* v_thenSeq_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_unsigned_to_nat(3u);
v_thenSeq_1279_ = l_Lean_Syntax_getArg(v_stx_1252_, v___x_1278_);
lean_inc(v_thenSeq_1279_);
v___x_1280_ = l_Lean_Elab_Do_inferControlInfoSeq(v_thenSeq_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v_elseSeq_1283_; lean_object* v___x_1284_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_unsigned_to_nat(1u);
v_elseSeq_1283_ = l_Lean_Syntax_getArg(v___x_1275_, v___x_1282_);
lean_dec(v___x_1275_);
lean_inc(v_elseSeq_1283_);
v___x_1284_ = l_Lean_Elab_Do_inferControlInfoSeq(v_elseSeq_1283_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Lean_Syntax_getArg(v_stx_1252_, v___x_1282_);
lean_dec(v_stx_1252_);
v___f_1287_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___lam__0___boxed), 18, 9);
lean_closure_set(v___f_1287_, 0, v___x_1262_);
lean_closure_set(v___f_1287_, 1, v___x_1263_);
lean_closure_set(v___f_1287_, 2, v___x_1264_);
lean_closure_set(v___f_1287_, 3, v___x_1286_);
lean_closure_set(v___f_1287_, 4, v___x_1268_);
lean_closure_set(v___f_1287_, 5, v___x_1273_);
lean_closure_set(v___f_1287_, 6, v___x_1282_);
lean_closure_set(v___f_1287_, 7, v_thenSeq_1279_);
lean_closure_set(v___f_1287_, 8, v_elseSeq_1283_);
v___x_1288_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1281_, v_a_1285_);
v___x_1289_ = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(v_dec_1253_, v___x_1288_, v___f_1287_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
return v___x_1289_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_elseSeq_1283_);
lean_dec(v_a_1281_);
lean_dec(v_thenSeq_1279_);
lean_dec_ref(v_dec_1253_);
lean_dec(v_stx_1252_);
v_a_1290_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1284_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1284_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_thenSeq_1279_);
lean_dec(v___x_1275_);
lean_dec_ref(v_dec_1253_);
lean_dec(v_stx_1252_);
v_a_1298_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1280_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1280_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___boxed(lean_object* v_stx_1306_, lean_object* v_dec_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Elab_Do_elabDoIf(v_stx_1306_, v_dec_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec_ref(v_a_1308_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1(){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1324_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_1325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_1326_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1));
v___x_1327_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___boxed), 10, 0);
v___x_1328_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1324_, v___x_1325_, v___x_1326_, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___boxed(lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
return v_res_1330_;
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
