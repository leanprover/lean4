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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doIfLet"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value),LEAN_SCALAR_PTR_LITERAL(181, 227, 73, 225, 0, 143, 195, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = "If the given syntax is a `doIf`, return an equivalent `doIf` that has an `else` but no `else if`s or\n`if let`s."};
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(uint8_t v___x_1_, lean_object* v_____do__lift_2_, lean_object* v___y_3_, lean_object* v___y_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1_ = stack[0].m_num;
lean_object* v_____do__lift_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v_res_7_;
v_res_7_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_1_, v_____do__lift_2_, v___y_3_, v___y_4_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0___boxed(lean_object* v___x_8_, lean_object* v_____do__lift_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
uint8_t v___x_26843__boxed_12_; lean_object* v_res_13_; 
v___x_26843__boxed_12_ = lean_unbox(v___x_8_);
v_res_13_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_26843__boxed_12_, v_____do__lift_9_, v___y_10_, v___y_11_);
lean_dec_ref(v___y_10_);
lean_dec(v_____do__lift_9_);
return v_res_13_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Array_mkArray0___redArg();
return v___x_28_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(uint8_t v___x_114_, lean_object* v_as_115_, size_t v_sz_116_, size_t v_i_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_____x_122_; lean_object* v___y_123_; uint8_t v___x_129_; 
v___x_129_ = lean_usize_dec_lt(v_i_117_, v_sz_116_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_b_118_);
lean_ctor_set(v___x_130_, 1, v___y_120_);
return v___x_130_;
}
else
{
lean_object* v_a_131_; lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_322_; 
v_a_131_ = lean_array_uget(v_as_115_, v_i_117_);
v_fst_132_ = lean_ctor_get(v_a_131_, 0);
v_snd_133_ = lean_ctor_get(v_a_131_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_a_131_);
if (v_isSharedCheck_322_ == 0)
{
v___x_135_ = v_a_131_;
v_isShared_136_ = v_isSharedCheck_322_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snd_133_);
lean_inc(v_fst_132_);
lean_dec(v_a_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_322_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_321_; 
v_fst_137_ = lean_ctor_get(v_b_118_, 0);
v_snd_138_ = lean_ctor_get(v_b_118_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_b_118_);
if (v_isSharedCheck_321_ == 0)
{
v___x_140_ = v_b_118_;
v_isShared_141_ = v_isSharedCheck_321_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_snd_138_);
lean_inc(v_fst_137_);
lean_dec(v_b_118_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_321_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; uint8_t v___y_144_; lean_object* v___y_145_; lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_____x_168_; lean_object* v___y_169_; lean_object* v___y_170_; uint8_t v___x_299_; 
v___x_142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_unsigned_to_nat(2u);
v___x_299_ = lean_unbox(v_snd_138_);
lean_dec(v_snd_138_);
if (v___x_299_ == 0)
{
lean_object* v_ref_300_; lean_object* v___x_301_; 
v_ref_300_ = lean_ctor_get(v___y_119_, 5);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_114_, v_ref_300_, v___y_119_, v___y_120_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_a_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_n(v_a_302_, 4);
v_a_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_301_, 2);
v___x_304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42));
v___x_307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v_a_302_);
lean_ctor_set(v___x_308_, 1, v___x_305_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
v___x_309_ = l_Lean_Syntax_node2(v_a_302_, v___x_306_, v_fst_137_, v___x_308_);
v___x_310_ = l_Lean_Syntax_node1(v_a_302_, v___x_305_, v___x_309_);
v___x_311_ = l_Lean_Syntax_node1(v_a_302_, v___x_304_, v___x_310_);
v_____x_168_ = v___x_311_;
v___y_169_ = v___y_119_;
v___y_170_ = v_a_303_;
goto v___jp_167_;
}
else
{
lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_del_object(v___x_140_);
lean_dec(v_fst_137_);
lean_del_object(v___x_135_);
lean_dec(v_snd_133_);
lean_dec(v_fst_132_);
v_a_312_ = lean_ctor_get(v___x_301_, 0);
v_a_313_ = lean_ctor_get(v___x_301_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_301_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_inc(v_a_312_);
lean_dec(v___x_301_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
v_____x_168_ = v_fst_137_;
v___y_169_ = v___y_119_;
v___y_170_ = v___y_120_;
goto v___jp_167_;
}
v___jp_143_:
{
lean_object* v_ref_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v_ref_148_ = lean_ctor_get(v___y_145_, 5);
v___x_149_ = l_Lean_SourceInfo_fromRef(v_ref_148_, v___y_144_);
v___x_150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5));
lean_inc(v___x_149_);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 2);
lean_ctor_set(v___x_140_, 1, v___x_150_);
lean_ctor_set(v___x_140_, 0, v___x_149_);
v___x_152_ = v___x_140_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_164_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(v___x_149_);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 2);
lean_ctor_set(v___x_135_, 1, v___x_153_);
lean_ctor_set(v___x_135_, 0, v___x_149_);
v___x_155_ = v___x_135_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_163_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_157_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
lean_inc_n(v___x_149_, 3);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_149_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
v___x_159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_149_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Lean_Syntax_node2(v___x_149_, v___x_156_, v___x_160_, v___y_146_);
v___x_162_ = l_Lean_Syntax_node6(v___x_149_, v___x_142_, v___x_152_, v_fst_132_, v___x_155_, v_snd_133_, v___x_158_, v___x_161_);
v_____x_122_ = v___x_162_;
v___y_123_ = v___y_147_;
goto v___jp_121_;
}
}
}
v___jp_167_:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
lean_inc(v_fst_132_);
v___x_172_ = l_Lean_Syntax_isOfKind(v_fst_132_, v___x_171_);
if (v___x_172_ == 0)
{
if (v___x_172_ == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(v_fst_132_);
v___x_174_ = l_Lean_Syntax_isOfKind(v_fst_132_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v_____x_168_);
lean_del_object(v___x_140_);
lean_del_object(v___x_135_);
lean_dec(v_snd_133_);
lean_dec(v_fst_132_);
v___x_175_ = l_Lean_Macro_throwUnsupported___redArg(v___y_170_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v_a_177_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
v_a_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_175_, 2);
v_____x_122_ = v_a_176_;
v___y_123_ = v_a_177_;
goto v___jp_121_;
}
else
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_178_ = lean_ctor_get(v___x_175_, 0);
v_a_179_ = lean_ctor_get(v___x_175_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_175_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v___x_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
v___y_144_ = v___x_172_;
v___y_145_ = v___y_169_;
v___y_146_ = v_____x_168_;
v___y_147_ = v___y_170_;
goto v___jp_143_;
}
}
else
{
v___y_144_ = v___x_172_;
v___y_145_ = v___y_169_;
v___y_146_ = v_____x_168_;
v___y_147_ = v___y_170_;
goto v___jp_143_;
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
lean_del_object(v___x_140_);
lean_del_object(v___x_135_);
v___x_187_ = l_Lean_Syntax_getArg(v_fst_132_, v___x_165_);
v___x_188_ = l_Lean_Syntax_getArg(v_fst_132_, v___x_166_);
lean_dec(v_fst_132_);
v___x_189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(v___x_188_);
v___x_190_ = l_Lean_Syntax_isOfKind(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(v___x_188_);
v___x_192_ = l_Lean_Syntax_isOfKind(v___x_188_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_dec(v___x_188_);
lean_dec(v___x_187_);
lean_dec(v_____x_168_);
lean_dec(v_snd_133_);
v___x_193_ = l_Lean_Macro_throwUnsupported___redArg(v___y_170_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_a_195_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
v_a_195_ = lean_ctor_get(v___x_193_, 1);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_193_, 2);
v_____x_122_ = v_a_194_;
v___y_123_ = v_a_195_;
goto v___jp_121_;
}
else
{
lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_196_ = lean_ctor_get(v___x_193_, 0);
v_a_197_ = lean_ctor_get(v___x_193_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_193_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_inc(v_a_196_);
lean_dec(v___x_193_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_196_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_ref_205_; lean_object* v___x_206_; 
v_ref_205_ = lean_ctor_get(v___y_169_, 5);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_114_, v_ref_205_, v___y_169_, v___y_170_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc_n(v_a_207_, 21);
v_a_208_ = lean_ctor_get(v___x_206_, 1);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_206_, 2);
v___x_209_ = l_Lean_Syntax_getArg(v___x_188_, v___x_165_);
lean_dec(v___x_188_);
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
v___x_212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_212_, 0, v_a_207_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_214_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
v___x_215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_215_, 0, v_a_207_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
v___x_216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
v___x_217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
v___x_218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
v___x_219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_219_, 0, v_a_207_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28));
v___x_221_ = l_Lean_Syntax_node1(v_a_207_, v___x_220_, v___x_209_);
v___x_222_ = l_Lean_Syntax_node2(v_a_207_, v___x_217_, v___x_219_, v___x_221_);
lean_inc_ref_n(v___x_215_, 3);
v___x_223_ = l_Lean_Syntax_node2(v_a_207_, v___x_216_, v___x_215_, v___x_222_);
v___x_224_ = l_Lean_Syntax_node1(v_a_207_, v___x_213_, v___x_223_);
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v_a_207_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
v___x_230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_230_, 0, v_a_207_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_Syntax_node1(v_a_207_, v___x_213_, v___x_187_);
v___x_232_ = l_Lean_Syntax_node1(v_a_207_, v___x_213_, v___x_231_);
v___x_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_234_, 0, v_a_207_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
lean_inc_ref(v___x_234_);
lean_inc_ref(v___x_230_);
v___x_235_ = l_Lean_Syntax_node4(v_a_207_, v___x_228_, v___x_230_, v___x_232_, v___x_234_, v_snd_133_);
v___x_236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_238_, 0, v_a_207_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = l_Lean_Syntax_node1(v_a_207_, v___x_236_, v___x_238_);
v___x_240_ = l_Lean_Syntax_node1(v_a_207_, v___x_213_, v___x_239_);
v___x_241_ = l_Lean_Syntax_node1(v_a_207_, v___x_213_, v___x_240_);
v___x_242_ = l_Lean_Syntax_node4(v_a_207_, v___x_228_, v___x_230_, v___x_241_, v___x_234_, v_____x_168_);
v___x_243_ = l_Lean_Syntax_node2(v_a_207_, v___x_213_, v___x_235_, v___x_242_);
v___x_244_ = l_Lean_Syntax_node1(v_a_207_, v___x_227_, v___x_243_);
v___x_245_ = l_Lean_Syntax_node7(v_a_207_, v___x_210_, v___x_212_, v___x_215_, v___x_215_, v___x_215_, v___x_224_, v___x_226_, v___x_244_);
v_____x_122_ = v___x_245_;
v___y_123_ = v_a_208_;
goto v___jp_121_;
}
else
{
lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec(v___x_188_);
lean_dec(v___x_187_);
lean_dec(v_____x_168_);
lean_dec(v_snd_133_);
v_a_246_ = lean_ctor_get(v___x_206_, 0);
v_a_247_ = lean_ctor_get(v___x_206_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_206_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_inc(v_a_246_);
lean_dec(v___x_206_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_246_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
else
{
lean_object* v_ref_255_; lean_object* v___x_256_; 
v_ref_255_ = lean_ctor_get(v___y_169_, 5);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(v___x_114_, v_ref_255_, v___y_169_, v___y_170_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v_a_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_n(v_a_257_, 18);
v_a_258_ = lean_ctor_get(v___x_256_, 1);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_256_, 2);
v___x_259_ = l_Lean_Syntax_getArg(v___x_188_, v___x_165_);
lean_dec(v___x_188_);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
v___x_262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_262_, 0, v_a_257_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_264_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
v___x_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_265_, 0, v_a_257_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
lean_ctor_set(v___x_265_, 2, v___x_264_);
v___x_266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref_n(v___x_265_, 3);
v___x_267_ = l_Lean_Syntax_node2(v_a_257_, v___x_266_, v___x_265_, v___x_259_);
v___x_268_ = l_Lean_Syntax_node1(v_a_257_, v___x_263_, v___x_267_);
v___x_269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_270_, 0, v_a_257_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_257_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Syntax_node1(v_a_257_, v___x_263_, v___x_187_);
v___x_276_ = l_Lean_Syntax_node1(v_a_257_, v___x_263_, v___x_275_);
v___x_277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_278_, 0, v_a_257_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
lean_inc_ref(v___x_278_);
lean_inc_ref(v___x_274_);
v___x_279_ = l_Lean_Syntax_node4(v_a_257_, v___x_272_, v___x_274_, v___x_276_, v___x_278_, v_snd_133_);
v___x_280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v_a_257_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_Syntax_node1(v_a_257_, v___x_280_, v___x_282_);
v___x_284_ = l_Lean_Syntax_node1(v_a_257_, v___x_263_, v___x_283_);
v___x_285_ = l_Lean_Syntax_node1(v_a_257_, v___x_263_, v___x_284_);
v___x_286_ = l_Lean_Syntax_node4(v_a_257_, v___x_272_, v___x_274_, v___x_285_, v___x_278_, v_____x_168_);
v___x_287_ = l_Lean_Syntax_node2(v_a_257_, v___x_263_, v___x_279_, v___x_286_);
v___x_288_ = l_Lean_Syntax_node1(v_a_257_, v___x_271_, v___x_287_);
v___x_289_ = l_Lean_Syntax_node7(v_a_257_, v___x_260_, v___x_262_, v___x_265_, v___x_265_, v___x_265_, v___x_268_, v___x_270_, v___x_288_);
v_____x_122_ = v___x_289_;
v___y_123_ = v_a_258_;
goto v___jp_121_;
}
else
{
lean_object* v_a_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v___x_188_);
lean_dec(v___x_187_);
lean_dec(v_____x_168_);
lean_dec(v_snd_133_);
v_a_290_ = lean_ctor_get(v___x_256_, 0);
v_a_291_ = lean_ctor_get(v___x_256_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_256_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_inc(v_a_290_);
lean_dec(v___x_256_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_290_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
}
}
}
v___jp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; size_t v___x_126_; size_t v___x_127_; 
v___x_124_ = lean_box(v___x_114_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_____x_122_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_add(v_i_117_, v___x_126_);
v_i_117_ = v___x_127_;
v_b_118_ = v___x_125_;
v___y_120_ = v___y_123_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_114_ = stack[0].m_num;
lean_object* v_as_115_ = stack[1].m_obj;
size_t v_sz_116_ = stack[2].m_num;
size_t v_i_117_ = stack[3].m_num;
lean_object* v_b_118_ = stack[4].m_obj;
lean_object* v___y_119_ = stack[5].m_obj;
lean_object* v___y_120_ = stack[6].m_obj;
lean_object* v_res_323_;
v_res_323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_114_, v_as_115_, v_sz_116_, v_i_117_, v_b_118_, v___y_119_, v___y_120_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___boxed(lean_object* v___x_324_, lean_object* v_as_325_, lean_object* v_sz_326_, lean_object* v_i_327_, lean_object* v_b_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v___x_27116__boxed_331_; size_t v_sz_boxed_332_; size_t v_i_boxed_333_; lean_object* v_res_334_; 
v___x_27116__boxed_331_ = lean_unbox(v___x_324_);
v_sz_boxed_332_ = lean_unbox_usize(v_sz_326_);
lean_dec(v_sz_326_);
v_i_boxed_333_ = lean_unbox_usize(v_i_327_);
lean_dec(v_i_327_);
v_res_334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(v___x_27116__boxed_331_, v_as_325_, v_sz_boxed_332_, v_i_boxed_333_, v_b_328_, v___y_329_, v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec_ref(v_as_325_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(lean_object* v_____do__lift_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = 0;
v___x_339_ = l_Lean_SourceInfo_fromRef(v_____do__lift_335_, v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___y_337_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0___boxed(lean_object* v_____do__lift_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_____do__lift_341_, v___y_342_, v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v_____do__lift_341_);
return v_res_344_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(lean_object* v_as_345_, size_t v_sz_346_, size_t v_i_347_, lean_object* v_b_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_____x_352_; lean_object* v___y_353_; uint8_t v___x_360_; 
v___x_360_ = lean_usize_dec_lt(v_i_347_, v_sz_346_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_b_348_);
lean_ctor_set(v___x_361_, 1, v___y_350_);
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_553_; 
v_a_362_ = lean_array_uget(v_as_345_, v_i_347_);
v_fst_363_ = lean_ctor_get(v_a_362_, 0);
v_snd_364_ = lean_ctor_get(v_a_362_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_362_);
if (v_isSharedCheck_553_ == 0)
{
v___x_366_ = v_a_362_;
v_isShared_367_ = v_isSharedCheck_553_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snd_364_);
lean_inc(v_fst_363_);
lean_dec(v_a_362_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_553_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_552_; 
v_fst_368_ = lean_ctor_get(v_b_348_, 0);
v_snd_369_ = lean_ctor_get(v_b_348_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_b_348_);
if (v_isSharedCheck_552_ == 0)
{
v___x_371_ = v_b_348_;
v_isShared_372_ = v_isSharedCheck_552_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snd_369_);
lean_inc(v_fst_368_);
lean_dec(v_b_348_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_552_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; lean_object* v___y_378_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_____x_399_; lean_object* v___y_400_; lean_object* v___y_401_; uint8_t v___x_530_; 
v___x_373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_unsigned_to_nat(2u);
v___x_530_ = lean_unbox(v_snd_369_);
lean_dec(v_snd_369_);
if (v___x_530_ == 0)
{
lean_object* v_ref_531_; lean_object* v___x_532_; 
v_ref_531_ = lean_ctor_get(v___y_349_, 5);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_531_, v___y_349_, v___y_350_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v_a_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_n(v_a_533_, 4);
v_a_534_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_532_, 2);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
v___x_536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__42));
v___x_538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
v___x_539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_539_, 0, v_a_533_);
lean_ctor_set(v___x_539_, 1, v___x_536_);
lean_ctor_set(v___x_539_, 2, v___x_538_);
v___x_540_ = l_Lean_Syntax_node2(v_a_533_, v___x_537_, v_fst_368_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node1(v_a_533_, v___x_536_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node1(v_a_533_, v___x_535_, v___x_541_);
v_____x_399_ = v___x_542_;
v___y_400_ = v___y_349_;
v___y_401_ = v_a_534_;
goto v___jp_398_;
}
else
{
lean_object* v_a_543_; lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_del_object(v___x_371_);
lean_dec(v_fst_368_);
lean_del_object(v___x_366_);
lean_dec(v_snd_364_);
lean_dec(v_fst_363_);
v_a_543_ = lean_ctor_get(v___x_532_, 0);
v_a_544_ = lean_ctor_get(v___x_532_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_532_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_inc(v_a_543_);
lean_dec(v___x_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_543_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
v_____x_399_ = v_fst_368_;
v___y_400_ = v___y_349_;
v___y_401_ = v___y_350_;
goto v___jp_398_;
}
v___jp_374_:
{
lean_object* v_ref_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v_ref_379_ = lean_ctor_get(v___y_378_, 5);
v___x_380_ = l_Lean_SourceInfo_fromRef(v_ref_379_, v___y_377_);
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5));
lean_inc(v___x_380_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 2);
lean_ctor_set(v___x_371_, 1, v___x_381_);
lean_ctor_set(v___x_371_, 0, v___x_380_);
v___x_383_ = v___x_371_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_381_);
v___x_383_ = v_reuseFailAlloc_395_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(v___x_380_);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 2);
lean_ctor_set(v___x_366_, 1, v___x_384_);
lean_ctor_set(v___x_366_, 0, v___x_380_);
v___x_386_ = v___x_366_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_394_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_388_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
lean_inc_n(v___x_380_, 3);
v___x_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_389_, 0, v___x_380_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
v___x_390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_380_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_Syntax_node2(v___x_380_, v___x_387_, v___x_391_, v___y_375_);
v___x_393_ = l_Lean_Syntax_node6(v___x_380_, v___x_373_, v___x_383_, v_fst_363_, v___x_386_, v_snd_364_, v___x_389_, v___x_392_);
v_____x_352_ = v___x_393_;
v___y_353_ = v___y_376_;
goto v___jp_351_;
}
}
}
v___jp_398_:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
lean_inc(v_fst_363_);
v___x_403_ = l_Lean_Syntax_isOfKind(v_fst_363_, v___x_402_);
if (v___x_403_ == 0)
{
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(v_fst_363_);
v___x_405_ = l_Lean_Syntax_isOfKind(v_fst_363_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_____x_399_);
lean_del_object(v___x_371_);
lean_del_object(v___x_366_);
lean_dec(v_snd_364_);
lean_dec(v_fst_363_);
v___x_406_ = l_Lean_Macro_throwUnsupported___redArg(v___y_401_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v_a_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
v_a_408_ = lean_ctor_get(v___x_406_, 1);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_406_, 2);
v_____x_352_ = v_a_407_;
v___y_353_ = v_a_408_;
goto v___jp_351_;
}
else
{
lean_object* v_a_409_; lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
v_a_409_ = lean_ctor_get(v___x_406_, 0);
v_a_410_ = lean_ctor_get(v___x_406_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_406_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_inc(v_a_409_);
lean_dec(v___x_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_409_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
v___y_375_ = v_____x_399_;
v___y_376_ = v___y_401_;
v___y_377_ = v___x_403_;
v___y_378_ = v___y_400_;
goto v___jp_374_;
}
}
else
{
v___y_375_ = v_____x_399_;
v___y_376_ = v___y_401_;
v___y_377_ = v___x_403_;
v___y_378_ = v___y_400_;
goto v___jp_374_;
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
lean_del_object(v___x_371_);
lean_del_object(v___x_366_);
v___x_418_ = l_Lean_Syntax_getArg(v_fst_363_, v___x_396_);
v___x_419_ = l_Lean_Syntax_getArg(v_fst_363_, v___x_397_);
lean_dec(v_fst_363_);
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(v___x_419_);
v___x_421_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(v___x_419_);
v___x_423_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_dec(v___x_419_);
lean_dec(v___x_418_);
lean_dec(v_____x_399_);
lean_dec(v_snd_364_);
v___x_424_ = l_Lean_Macro_throwUnsupported___redArg(v___y_401_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v_a_426_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
v_a_426_ = lean_ctor_get(v___x_424_, 1);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_424_, 2);
v_____x_352_ = v_a_425_;
v___y_353_ = v_a_426_;
goto v___jp_351_;
}
else
{
lean_object* v_a_427_; lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_427_ = lean_ctor_get(v___x_424_, 0);
v_a_428_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_424_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_inc(v_a_427_);
lean_dec(v___x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_427_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_ref_436_; lean_object* v___x_437_; 
v_ref_436_ = lean_ctor_get(v___y_400_, 5);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_436_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_a_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc_n(v_a_438_, 21);
v_a_439_ = lean_ctor_get(v___x_437_, 1);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_437_, 2);
v___x_440_ = l_Lean_Syntax_getArg(v___x_419_, v___x_396_);
lean_dec(v___x_419_);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
v___x_443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_443_, 0, v_a_438_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
v___x_446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_446_, 0, v_a_438_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
v___x_450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_450_, 0, v_a_438_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28));
v___x_452_ = l_Lean_Syntax_node1(v_a_438_, v___x_451_, v___x_440_);
v___x_453_ = l_Lean_Syntax_node2(v_a_438_, v___x_448_, v___x_450_, v___x_452_);
lean_inc_ref_n(v___x_446_, 3);
v___x_454_ = l_Lean_Syntax_node2(v_a_438_, v___x_447_, v___x_446_, v___x_453_);
v___x_455_ = l_Lean_Syntax_node1(v_a_438_, v___x_444_, v___x_454_);
v___x_456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_457_, 0, v_a_438_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
v___x_461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_461_, 0, v_a_438_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_Syntax_node1(v_a_438_, v___x_444_, v___x_418_);
v___x_463_ = l_Lean_Syntax_node1(v_a_438_, v___x_444_, v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v_a_438_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
lean_inc_ref(v___x_465_);
lean_inc_ref(v___x_461_);
v___x_466_ = l_Lean_Syntax_node4(v_a_438_, v___x_459_, v___x_461_, v___x_463_, v___x_465_, v_snd_364_);
v___x_467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_469_, 0, v_a_438_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_Syntax_node1(v_a_438_, v___x_467_, v___x_469_);
v___x_471_ = l_Lean_Syntax_node1(v_a_438_, v___x_444_, v___x_470_);
v___x_472_ = l_Lean_Syntax_node1(v_a_438_, v___x_444_, v___x_471_);
v___x_473_ = l_Lean_Syntax_node4(v_a_438_, v___x_459_, v___x_461_, v___x_472_, v___x_465_, v_____x_399_);
v___x_474_ = l_Lean_Syntax_node2(v_a_438_, v___x_444_, v___x_466_, v___x_473_);
v___x_475_ = l_Lean_Syntax_node1(v_a_438_, v___x_458_, v___x_474_);
v___x_476_ = l_Lean_Syntax_node7(v_a_438_, v___x_441_, v___x_443_, v___x_446_, v___x_446_, v___x_446_, v___x_455_, v___x_457_, v___x_475_);
v_____x_352_ = v___x_476_;
v___y_353_ = v_a_439_;
goto v___jp_351_;
}
else
{
lean_object* v_a_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v___x_419_);
lean_dec(v___x_418_);
lean_dec(v_____x_399_);
lean_dec(v_snd_364_);
v_a_477_ = lean_ctor_get(v___x_437_, 0);
v_a_478_ = lean_ctor_get(v___x_437_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_437_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_inc(v_a_477_);
lean_dec(v___x_437_);
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
v_ref_486_ = lean_ctor_get(v___y_400_, 5);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(v_ref_486_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc_n(v_a_488_, 18);
v_a_489_ = lean_ctor_get(v___x_487_, 1);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_487_, 2);
v___x_490_ = l_Lean_Syntax_getArg(v___x_419_, v___x_396_);
lean_dec(v___x_419_);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v_a_488_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
v___x_495_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
v___x_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_496_, 0, v_a_488_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref_n(v___x_496_, 3);
v___x_498_ = l_Lean_Syntax_node2(v_a_488_, v___x_497_, v___x_496_, v___x_490_);
v___x_499_ = l_Lean_Syntax_node1(v_a_488_, v___x_494_, v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v_a_488_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34));
v___x_505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_505_, 0, v_a_488_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_Syntax_node1(v_a_488_, v___x_494_, v___x_418_);
v___x_507_ = l_Lean_Syntax_node1(v_a_488_, v___x_494_, v___x_506_);
v___x_508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
v___x_509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_509_, 0, v_a_488_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
lean_inc_ref(v___x_509_);
lean_inc_ref(v___x_505_);
v___x_510_ = l_Lean_Syntax_node4(v_a_488_, v___x_503_, v___x_505_, v___x_507_, v___x_509_, v_snd_364_);
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_513_, 0, v_a_488_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Lean_Syntax_node1(v_a_488_, v___x_511_, v___x_513_);
v___x_515_ = l_Lean_Syntax_node1(v_a_488_, v___x_494_, v___x_514_);
v___x_516_ = l_Lean_Syntax_node1(v_a_488_, v___x_494_, v___x_515_);
v___x_517_ = l_Lean_Syntax_node4(v_a_488_, v___x_503_, v___x_505_, v___x_516_, v___x_509_, v_____x_399_);
v___x_518_ = l_Lean_Syntax_node2(v_a_488_, v___x_494_, v___x_510_, v___x_517_);
v___x_519_ = l_Lean_Syntax_node1(v_a_488_, v___x_502_, v___x_518_);
v___x_520_ = l_Lean_Syntax_node7(v_a_488_, v___x_491_, v___x_493_, v___x_496_, v___x_496_, v___x_496_, v___x_499_, v___x_501_, v___x_519_);
v_____x_352_ = v___x_520_;
v___y_353_ = v_a_489_;
goto v___jp_351_;
}
else
{
lean_object* v_a_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v___x_419_);
lean_dec(v___x_418_);
lean_dec(v_____x_399_);
lean_dec(v_snd_364_);
v_a_521_ = lean_ctor_get(v___x_487_, 0);
v_a_522_ = lean_ctor_get(v___x_487_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_487_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_inc(v_a_521_);
lean_dec(v___x_487_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_521_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
}
}
}
v___jp_351_:
{
uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; size_t v___x_357_; size_t v___x_358_; 
v___x_354_ = 0;
v___x_355_ = lean_box(v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v_____x_352_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_347_, v___x_357_);
v_i_347_ = v___x_358_;
v_b_348_ = v___x_356_;
v___y_350_ = v___y_353_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_345_ = stack[0].m_obj;
size_t v_sz_346_ = stack[1].m_num;
size_t v_i_347_ = stack[2].m_num;
lean_object* v_b_348_ = stack[3].m_obj;
lean_object* v___y_349_ = stack[4].m_obj;
lean_object* v___y_350_ = stack[5].m_obj;
lean_object* v_res_554_;
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v_as_345_, v_sz_346_, v_i_347_, v_b_348_, v___y_349_, v___y_350_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___boxed(lean_object* v_as_555_, lean_object* v_sz_556_, lean_object* v_i_557_, lean_object* v_b_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_556_);
lean_dec(v_sz_556_);
v_i_boxed_562_ = lean_unbox_usize(v_i_557_);
lean_dec(v_i_557_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v_as_555_, v_sz_boxed_561_, v_i_boxed_562_, v_b_558_, v___y_559_, v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v_as_555_);
return v_res_563_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(size_t v_sz_567_, size_t v_i_568_, lean_object* v_bs_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_lt(v_i_568_, v_sz_567_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v_bs_569_);
return v___x_571_;
}
else
{
lean_object* v_v_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_v_572_ = lean_array_uget(v_bs_569_, v_i_568_);
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1));
lean_inc(v_v_572_);
v___x_574_ = l_Lean_Syntax_isOfKind(v_v_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v_v_572_);
lean_dec_ref(v_bs_569_);
v___x_575_ = lean_box(0);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = l_Lean_Syntax_getArg(v_v_572_, v___x_576_);
lean_inc(v___x_577_);
v___x_578_ = l_Lean_Syntax_isOfKind(v___x_577_, v___x_573_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec(v___x_577_);
lean_dec(v_v_572_);
lean_dec_ref(v_bs_569_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_bs_x27_582_; lean_object* v_tks_583_; lean_object* v_conds_584_; lean_object* v_ts_585_; lean_object* v___x_586_; lean_object* v___x_587_; size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_unsigned_to_nat(3u);
v_bs_x27_582_ = lean_array_uset(v_bs_569_, v_i_568_, v___x_576_);
v_tks_583_ = l_Lean_Syntax_getArg(v___x_577_, v___x_580_);
lean_dec(v___x_577_);
v_conds_584_ = l_Lean_Syntax_getArg(v_v_572_, v___x_580_);
v_ts_585_ = l_Lean_Syntax_getArg(v_v_572_, v___x_581_);
lean_dec(v_v_572_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_conds_584_);
lean_ctor_set(v___x_586_, 1, v_ts_585_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_tks_583_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_568_, v___x_588_);
v___x_590_ = lean_array_uset(v_bs_x27_582_, v_i_568_, v___x_587_);
v_i_568_ = v___x_589_;
v_bs_569_ = v___x_590_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_567_ = stack[0].m_num;
size_t v_i_568_ = stack[1].m_num;
lean_object* v_bs_569_ = stack[2].m_obj;
lean_object* v_res_592_;
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_567_, v_i_568_, v_bs_569_);
stack->m_obj
 = v_res_592_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___boxed(lean_object* v_sz_593_, lean_object* v_i_594_, lean_object* v_bs_595_){
_start:
{
size_t v_sz_boxed_596_; size_t v_i_boxed_597_; lean_object* v_res_598_; 
v_sz_boxed_596_ = lean_unbox_usize(v_sz_593_);
lean_dec(v_sz_593_);
v_i_boxed_597_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(v_sz_boxed_596_, v_i_boxed_597_, v_bs_595_);
return v_res_598_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(size_t v_sz_599_, size_t v_i_600_, lean_object* v_bs_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = lean_usize_dec_lt(v_i_600_, v_sz_599_);
if (v___x_602_ == 0)
{
return v_bs_601_;
}
else
{
lean_object* v_v_603_; lean_object* v_snd_604_; lean_object* v_fst_605_; lean_object* v___x_606_; lean_object* v_bs_x27_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v_v_603_ = lean_array_uget_borrowed(v_bs_601_, v_i_600_);
v_snd_604_ = lean_ctor_get(v_v_603_, 1);
v_fst_605_ = lean_ctor_get(v_snd_604_, 0);
lean_inc(v_fst_605_);
v___x_606_ = lean_unsigned_to_nat(0u);
v_bs_x27_607_ = lean_array_uset(v_bs_601_, v_i_600_, v___x_606_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_600_, v___x_608_);
v___x_610_ = lean_array_uset(v_bs_x27_607_, v_i_600_, v_fst_605_);
v_i_600_ = v___x_609_;
v_bs_601_ = v___x_610_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_599_ = stack[0].m_num;
size_t v_i_600_ = stack[1].m_num;
lean_object* v_bs_601_ = stack[2].m_obj;
lean_object* v_res_612_;
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_599_, v_i_600_, v_bs_601_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2___boxed(lean_object* v_sz_613_, lean_object* v_i_614_, lean_object* v_bs_615_){
_start:
{
size_t v_sz_boxed_616_; size_t v_i_boxed_617_; lean_object* v_res_618_; 
v_sz_boxed_616_ = lean_unbox_usize(v_sz_613_);
lean_dec(v_sz_613_);
v_i_boxed_617_ = lean_unbox_usize(v_i_614_);
lean_dec(v_i_614_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(v_sz_boxed_616_, v_i_boxed_617_, v_bs_615_);
return v_res_618_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(size_t v_sz_619_, size_t v_i_620_, lean_object* v_bs_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_622_ == 0)
{
return v_bs_621_;
}
else
{
lean_object* v_v_623_; lean_object* v_snd_624_; lean_object* v_snd_625_; lean_object* v___x_626_; lean_object* v_bs_x27_627_; size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v_v_623_ = lean_array_uget_borrowed(v_bs_621_, v_i_620_);
v_snd_624_ = lean_ctor_get(v_v_623_, 1);
v_snd_625_ = lean_ctor_get(v_snd_624_, 1);
lean_inc(v_snd_625_);
v___x_626_ = lean_unsigned_to_nat(0u);
v_bs_x27_627_ = lean_array_uset(v_bs_621_, v_i_620_, v___x_626_);
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_620_, v___x_628_);
v___x_630_ = lean_array_uset(v_bs_x27_627_, v_i_620_, v_snd_625_);
v_i_620_ = v___x_629_;
v_bs_621_ = v___x_630_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_619_ = stack[0].m_num;
size_t v_i_620_ = stack[1].m_num;
lean_object* v_bs_621_ = stack[2].m_obj;
lean_object* v_res_632_;
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(v_sz_619_, v_i_620_, v_bs_621_);
stack->m_obj
 = v_res_632_;
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
v___x_658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
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
v___x_715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
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
v___x_722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
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
v___y_731_ = v_ts_796_;
v___y_732_ = v_a_649_;
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
v___y_731_ = v_ts_814_;
v___y_732_ = v_a_649_;
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
v___x_738_ = l_Array_reverse___redArg(v___y_731_);
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
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(v___x_740_, v_sz_743_, v___x_744_, v___x_742_, v___y_732_, v_a_735_);
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
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
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
v___x_781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v___x_772_);
lean_ctor_set(v___x_782_, 1, v___x_774_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
v___x_783_ = l_Lean_Syntax_node2(v___x_772_, v___x_775_, v___x_780_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node1(v___x_772_, v___x_774_, v___x_783_);
v___x_785_ = l_Lean_Syntax_node1(v___x_772_, v___x_773_, v___x_784_);
v___y_731_ = v_ts_767_;
v___y_732_ = v___y_768_;
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
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1(){
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
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_838_;
v_res_838_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___boxed(lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
return v_res_840_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3(){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3));
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0));
v___x_845_ = l_Lean_addBuiltinDocString(v___x_843_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_846_;
v_res_846_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___boxed(lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
return v_res_848_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(lean_object* v_cond_852_, lean_object* v_then___853_, uint8_t v___x_854_, lean_object* v_else___855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_doBlockResultType_864_; lean_object* v___x_865_; 
v_doBlockResultType_864_ = lean_ctor_get(v___y_856_, 3);
lean_inc_ref(v_doBlockResultType_864_);
v___x_865_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_864_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_886_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_886_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_886_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_886_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_ref_870_; uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v_ref_870_ = lean_ctor_get(v___y_861_, 2);
v___x_871_ = 0;
v___x_872_ = l_Lean_SourceInfo_fromRef(v_ref_870_, v___x_871_);
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1));
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5));
lean_inc_n(v___x_872_, 3);
v___x_875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_872_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_872_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_872_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_Syntax_node6(v___x_872_, v___x_873_, v___x_875_, v_cond_852_, v___x_877_, v_then___853_, v___x_879_, v_else___855_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 1);
v___x_882_ = v___x_868_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_866_);
v___x_882_ = v_reuseFailAlloc_885_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_box(0);
v___x_884_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_880_, v___x_882_, v___x_854_, v___x_854_, v___x_883_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_884_;
}
}
}
else
{
lean_dec(v_else___855_);
lean_dec(v_then___853_);
lean_dec(v_cond_852_);
return v___x_865_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cond_852_ = stack[0].m_obj;
lean_object* v_then___853_ = stack[1].m_obj;
uint8_t v___x_854_ = stack[2].m_num;
lean_object* v_else___855_ = stack[3].m_obj;
lean_object* v___y_856_ = stack[4].m_obj;
lean_object* v___y_857_ = stack[5].m_obj;
lean_object* v___y_858_ = stack[6].m_obj;
lean_object* v___y_859_ = stack[7].m_obj;
lean_object* v___y_860_ = stack[8].m_obj;
lean_object* v___y_861_ = stack[9].m_obj;
lean_object* v___y_862_ = stack[10].m_obj;
lean_object* v_res_887_;
v_res_887_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(v_cond_852_, v_then___853_, v___x_854_, v_else___855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed(lean_object* v_cond_888_, lean_object* v_then___889_, lean_object* v___x_890_, lean_object* v_else___891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v___x_3212__boxed_900_; lean_object* v_res_901_; 
v___x_3212__boxed_900_ = lean_unbox(v___x_890_);
v_res_901_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(v_cond_888_, v_then___889_, v___x_3212__boxed_900_, v_else___891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_901_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1));
v___x_906_ = l_Lean_MessageData_ofFormat(v___x_905_);
return v___x_906_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(lean_object* v_cond_907_, uint8_t v___x_908_, lean_object* v_elseSeq_909_, lean_object* v_dec_910_, lean_object* v_then___911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_920_ = lean_box(v___x_908_);
v___f_921_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed), 12, 3);
lean_closure_set(v___f_921_, 0, v_cond_907_);
lean_closure_set(v___f_921_, 1, v_then___911_);
lean_closure_set(v___f_921_, 2, v___x_920_);
v___x_922_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
v___x_923_ = lean_box(v___x_908_);
v___x_924_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_924_, 0, v_elseSeq_909_);
lean_closure_set(v___x_924_, 1, v_dec_910_);
lean_closure_set(v___x_924_, 2, v___x_923_);
v___x_925_ = lean_box(0);
v___x_926_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_922_, v___x_924_, v___f_921_, v___x_925_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_926_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cond_907_ = stack[0].m_obj;
uint8_t v___x_908_ = stack[1].m_num;
lean_object* v_elseSeq_909_ = stack[2].m_obj;
lean_object* v_dec_910_ = stack[3].m_obj;
lean_object* v_then___911_ = stack[4].m_obj;
lean_object* v___y_912_ = stack[5].m_obj;
lean_object* v___y_913_ = stack[6].m_obj;
lean_object* v___y_914_ = stack[7].m_obj;
lean_object* v___y_915_ = stack[8].m_obj;
lean_object* v___y_916_ = stack[9].m_obj;
lean_object* v___y_917_ = stack[10].m_obj;
lean_object* v___y_918_ = stack[11].m_obj;
lean_object* v_res_927_;
v_res_927_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(v_cond_907_, v___x_908_, v_elseSeq_909_, v_dec_910_, v_then___911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed(lean_object* v_cond_928_, lean_object* v___x_929_, lean_object* v_elseSeq_930_, lean_object* v_dec_931_, lean_object* v_then___932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v___x_3337__boxed_941_; lean_object* v_res_942_; 
v___x_3337__boxed_941_ = lean_unbox(v___x_929_);
v_res_942_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(v_cond_928_, v___x_3337__boxed_941_, v_elseSeq_930_, v_dec_931_, v_then___932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_942_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1));
v___x_947_ = l_Lean_MessageData_ofFormat(v___x_946_);
return v___x_947_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(lean_object* v_cond_948_, lean_object* v_thenSeq_949_, lean_object* v_elseSeq_950_, lean_object* v_dec_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_960_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
v___x_961_ = 1;
v___x_962_ = lean_box(v___x_961_);
lean_inc_ref(v_dec_951_);
v___f_963_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed), 13, 4);
lean_closure_set(v___f_963_, 0, v_cond_948_);
lean_closure_set(v___f_963_, 1, v___x_962_);
lean_closure_set(v___f_963_, 2, v_elseSeq_950_);
lean_closure_set(v___f_963_, 3, v_dec_951_);
v___x_964_ = lean_box(v___x_961_);
v___x_965_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_965_, 0, v_thenSeq_949_);
lean_closure_set(v___x_965_, 1, v_dec_951_);
lean_closure_set(v___x_965_, 2, v___x_964_);
v___x_966_ = lean_box(0);
v___x_967_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_960_, v___x_965_, v___f_963_, v___x_966_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
return v___x_967_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_cond_948_ = stack[0].m_obj;
lean_object* v_thenSeq_949_ = stack[1].m_obj;
lean_object* v_elseSeq_950_ = stack[2].m_obj;
lean_object* v_dec_951_ = stack[3].m_obj;
lean_object* v_a_952_ = stack[4].m_obj;
lean_object* v_a_953_ = stack[5].m_obj;
lean_object* v_a_954_ = stack[6].m_obj;
lean_object* v_a_955_ = stack[7].m_obj;
lean_object* v_a_956_ = stack[8].m_obj;
lean_object* v_a_957_ = stack[9].m_obj;
lean_object* v_a_958_ = stack[10].m_obj;
lean_object* v_res_968_;
v_res_968_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(v_cond_948_, v_thenSeq_949_, v_elseSeq_950_, v_dec_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___boxed(lean_object* v_cond_969_, lean_object* v_thenSeq_970_, lean_object* v_elseSeq_971_, lean_object* v_dec_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(v_cond_969_, v_thenSeq_970_, v_elseSeq_971_, v_dec_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_981_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_982_);
return v___x_984_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg(){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_988_;
v_res_988_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___boxed(lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v_res_990_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(lean_object* v_00_u03b1_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1000_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_992_ = stack[1].m_obj;
lean_object* v___y_993_ = stack[2].m_obj;
lean_object* v___y_994_ = stack[3].m_obj;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v___y_996_ = stack[5].m_obj;
lean_object* v___y_997_ = stack[6].m_obj;
lean_object* v___y_998_ = stack[7].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(lean_box(0), v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___boxed(lean_object* v_00_u03b1_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(v_00_u03b1_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1011_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(lean_object* v_elseSeq_1012_, lean_object* v_dec_1013_, lean_object* v_thenSeq_1014_, uint8_t v_then___1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v___x_1024_; 
v___x_1024_ = 1;
if (v_then___1015_ == 0)
{
lean_object* v___x_1025_; 
lean_dec(v_thenSeq_1014_);
v___x_1025_ = l_Lean_Elab_Do_elabDoSeq(v_elseSeq_1012_, v_dec_1013_, v___x_1024_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; 
lean_dec(v_elseSeq_1012_);
v___x_1026_ = l_Lean_Elab_Do_elabDoSeq(v_thenSeq_1014_, v_dec_1013_, v___x_1024_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1026_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_elseSeq_1012_ = stack[0].m_obj;
lean_object* v_dec_1013_ = stack[1].m_obj;
lean_object* v_thenSeq_1014_ = stack[2].m_obj;
uint8_t v_then___1015_ = stack[3].m_num;
lean_object* v___y_1016_ = stack[4].m_obj;
lean_object* v___y_1017_ = stack[5].m_obj;
lean_object* v___y_1018_ = stack[6].m_obj;
lean_object* v___y_1019_ = stack[7].m_obj;
lean_object* v___y_1020_ = stack[8].m_obj;
lean_object* v___y_1021_ = stack[9].m_obj;
lean_object* v___y_1022_ = stack[10].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(v_elseSeq_1012_, v_dec_1013_, v_thenSeq_1014_, v_then___1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed(lean_object* v_elseSeq_1028_, lean_object* v_dec_1029_, lean_object* v_thenSeq_1030_, lean_object* v_then___1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_then___00boxed_1040_; lean_object* v_res_1041_; 
v_then___00boxed_1040_ = lean_unbox(v_then___1031_);
v_res_1041_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(v_elseSeq_1028_, v_dec_1029_, v_thenSeq_1030_, v_then___00boxed_1040_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1041_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(lean_object* v_h_1053_, lean_object* v_cond_1054_, lean_object* v_then___1055_, uint8_t v___x_1056_, lean_object* v_else___1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_doBlockResultType_1066_; lean_object* v___x_1067_; 
v_doBlockResultType_1066_ = lean_ctor_get(v___y_1058_, 3);
lean_inc_ref(v_doBlockResultType_1066_);
v___x_1067_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1066_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1122_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1122_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1122_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37));
lean_inc(v_h_1053_);
v___x_1073_ = l_Lean_Syntax_isOfKind(v_h_1053_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1));
lean_inc(v_h_1053_);
v___x_1075_ = l_Lean_Syntax_isOfKind(v_h_1053_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_del_object(v___x_1070_);
lean_dec(v_a_1068_);
lean_dec(v_else___1057_);
lean_dec(v_then___1055_);
lean_dec(v_cond_1054_);
lean_dec(v_h_1053_);
v___x_1076_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1076_;
}
else
{
lean_object* v_ref_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v_ref_1077_ = lean_ctor_get(v___y_1063_, 2);
v___x_1078_ = l_Lean_SourceInfo_fromRef(v_ref_1077_, v___x_1073_);
v___x_1079_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5));
lean_inc_n(v___x_1078_, 5);
v___x_1081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1078_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
v___x_1083_ = l_Lean_Syntax_node1(v___x_1078_, v___x_1082_, v_h_1053_);
v___x_1084_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
v___x_1085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1078_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
v___x_1087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1078_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1078_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_Syntax_node8(v___x_1078_, v___x_1079_, v___x_1081_, v___x_1083_, v___x_1085_, v_cond_1054_, v___x_1087_, v_then___1055_, v___x_1089_, v_else___1057_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
v___x_1092_ = v___x_1070_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1068_);
v___x_1092_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1090_, v___x_1092_, v___x_1056_, v___x_1056_, v___x_1093_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1094_;
}
}
}
else
{
lean_object* v_ref_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v_ref_1096_ = lean_ctor_get(v___y_1063_, 2);
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = l_Lean_Syntax_getArg(v_h_1053_, v___x_1097_);
lean_dec(v_h_1053_);
v___x_1099_ = 0;
v___x_1100_ = l_Lean_SourceInfo_fromRef(v_ref_1096_, v___x_1099_);
v___x_1101_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
v___x_1102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5));
lean_inc_n(v___x_1100_, 6);
v___x_1103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1100_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
v___x_1105_ = l_Lean_SourceInfo_fromRef(v___x_1098_, v___x_1056_);
lean_dec(v___x_1098_);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
v___x_1107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l_Lean_Syntax_node1(v___x_1100_, v___x_1072_, v___x_1107_);
v___x_1109_ = l_Lean_Syntax_node1(v___x_1100_, v___x_1104_, v___x_1108_);
v___x_1110_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
v___x_1111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1100_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
v___x_1113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1100_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
v___x_1115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1100_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node8(v___x_1100_, v___x_1101_, v___x_1103_, v___x_1109_, v___x_1111_, v_cond_1054_, v___x_1113_, v_then___1055_, v___x_1115_, v_else___1057_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
v___x_1118_ = v___x_1070_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1068_);
v___x_1118_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1116_, v___x_1118_, v___x_1056_, v___x_1056_, v___x_1119_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1120_;
}
}
}
}
else
{
lean_dec(v_else___1057_);
lean_dec(v_then___1055_);
lean_dec(v_cond_1054_);
lean_dec(v_h_1053_);
return v___x_1067_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1053_ = stack[0].m_obj;
lean_object* v_cond_1054_ = stack[1].m_obj;
lean_object* v_then___1055_ = stack[2].m_obj;
uint8_t v___x_1056_ = stack[3].m_num;
lean_object* v_else___1057_ = stack[4].m_obj;
lean_object* v___y_1058_ = stack[5].m_obj;
lean_object* v___y_1059_ = stack[6].m_obj;
lean_object* v___y_1060_ = stack[7].m_obj;
lean_object* v___y_1061_ = stack[8].m_obj;
lean_object* v___y_1062_ = stack[9].m_obj;
lean_object* v___y_1063_ = stack[10].m_obj;
lean_object* v___y_1064_ = stack[11].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(v_h_1053_, v_cond_1054_, v_then___1055_, v___x_1056_, v_else___1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
stack->m_obj
 = v_res_1123_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed(lean_object* v_h_1124_, lean_object* v_cond_1125_, lean_object* v_then___1126_, lean_object* v___x_1127_, lean_object* v_else___1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v___x_7457__boxed_1137_; lean_object* v_res_1138_; 
v___x_7457__boxed_1137_ = lean_unbox(v___x_1127_);
v_res_1138_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(v_h_1124_, v_cond_1125_, v_then___1126_, v___x_7457__boxed_1137_, v_else___1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1138_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(lean_object* v_h_1139_, lean_object* v_cond_1140_, uint8_t v___x_1141_, lean_object* v_elabDiteBranch_1142_, lean_object* v_then___1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1152_ = lean_box(v___x_1141_);
v___f_1153_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1153_, 0, v_h_1139_);
lean_closure_set(v___f_1153_, 1, v_cond_1140_);
lean_closure_set(v___f_1153_, 2, v_then___1143_);
lean_closure_set(v___f_1153_, 3, v___x_1152_);
v___x_1154_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
v___x_1155_ = 0;
v___x_1156_ = lean_box(v___x_1155_);
v___x_1157_ = lean_apply_1(v_elabDiteBranch_1142_, v___x_1156_);
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_1154_, v___x_1157_, v___f_1153_, v___x_1158_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1159_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1139_ = stack[0].m_obj;
lean_object* v_cond_1140_ = stack[1].m_obj;
uint8_t v___x_1141_ = stack[2].m_num;
lean_object* v_elabDiteBranch_1142_ = stack[3].m_obj;
lean_object* v_then___1143_ = stack[4].m_obj;
lean_object* v___y_1144_ = stack[5].m_obj;
lean_object* v___y_1145_ = stack[6].m_obj;
lean_object* v___y_1146_ = stack[7].m_obj;
lean_object* v___y_1147_ = stack[8].m_obj;
lean_object* v___y_1148_ = stack[9].m_obj;
lean_object* v___y_1149_ = stack[10].m_obj;
lean_object* v___y_1150_ = stack[11].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(v_h_1139_, v_cond_1140_, v___x_1141_, v_elabDiteBranch_1142_, v_then___1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed(lean_object* v_h_1161_, lean_object* v_cond_1162_, lean_object* v___x_1163_, lean_object* v_elabDiteBranch_1164_, lean_object* v_then___1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v___x_7692__boxed_1174_; lean_object* v_res_1175_; 
v___x_7692__boxed_1174_ = lean_unbox(v___x_1163_);
v_res_1175_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(v_h_1161_, v_cond_1162_, v___x_7692__boxed_1174_, v_elabDiteBranch_1164_, v_then___1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1175_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(lean_object* v_h_1176_, lean_object* v_cond_1177_, lean_object* v_thenSeq_1178_, lean_object* v_elseSeq_1179_, lean_object* v_dec_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_elabDiteBranch_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_inc(v_thenSeq_1178_);
lean_inc_ref(v_dec_1180_);
lean_inc(v_elseSeq_1179_);
v_elabDiteBranch_1189_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 3);
lean_closure_set(v_elabDiteBranch_1189_, 0, v_elseSeq_1179_);
lean_closure_set(v_elabDiteBranch_1189_, 1, v_dec_1180_);
lean_closure_set(v_elabDiteBranch_1189_, 2, v_thenSeq_1178_);
v___x_1190_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
v___x_1191_ = 1;
v___x_1192_ = lean_box(v___x_1191_);
v___f_1193_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed), 13, 4);
lean_closure_set(v___f_1193_, 0, v_h_1176_);
lean_closure_set(v___f_1193_, 1, v_cond_1177_);
lean_closure_set(v___f_1193_, 2, v___x_1192_);
lean_closure_set(v___f_1193_, 3, v_elabDiteBranch_1189_);
v___x_1194_ = lean_box(v___x_1191_);
v___x_1195_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 4);
lean_closure_set(v___x_1195_, 0, v_elseSeq_1179_);
lean_closure_set(v___x_1195_, 1, v_dec_1180_);
lean_closure_set(v___x_1195_, 2, v_thenSeq_1178_);
lean_closure_set(v___x_1195_, 3, v___x_1194_);
v___x_1196_ = lean_box(0);
v___x_1197_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_1190_, v___x_1195_, v___f_1193_, v___x_1196_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1197_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1176_ = stack[0].m_obj;
lean_object* v_cond_1177_ = stack[1].m_obj;
lean_object* v_thenSeq_1178_ = stack[2].m_obj;
lean_object* v_elseSeq_1179_ = stack[3].m_obj;
lean_object* v_dec_1180_ = stack[4].m_obj;
lean_object* v_a_1181_ = stack[5].m_obj;
lean_object* v_a_1182_ = stack[6].m_obj;
lean_object* v_a_1183_ = stack[7].m_obj;
lean_object* v_a_1184_ = stack[8].m_obj;
lean_object* v_a_1185_ = stack[9].m_obj;
lean_object* v_a_1186_ = stack[10].m_obj;
lean_object* v_a_1187_ = stack[11].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(v_h_1176_, v_cond_1177_, v_thenSeq_1178_, v_elseSeq_1179_, v_dec_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___boxed(lean_object* v_h_1199_, lean_object* v_cond_1200_, lean_object* v_thenSeq_1201_, lean_object* v_elseSeq_1202_, lean_object* v_dec_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(v_h_1199_, v_cond_1200_, v_thenSeq_1201_, v_elseSeq_1202_, v_dec_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec_ref(v_a_1204_);
return v_res_1212_;
}
}
lean_object* l_Lean_Elab_Do_elabDoIf___lam__0(lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v_thenSeq_1220_, lean_object* v_elseSeq_1221_, lean_object* v_dec_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13));
v___x_1232_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1231_);
lean_inc(v___x_1216_);
v___x_1233_ = l_Lean_Syntax_isOfKind(v___x_1216_, v___x_1232_);
lean_dec(v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref(v_dec_1222_);
lean_dec(v_elseSeq_1221_);
lean_dec(v_thenSeq_1220_);
lean_dec(v___x_1216_);
v___x_1234_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = l_Lean_Syntax_getArg(v___x_1216_, v___x_1217_);
lean_inc(v___x_1235_);
v___x_1236_ = l_Lean_Syntax_matchesNull(v___x_1235_, v___x_1217_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; 
lean_inc(v___x_1235_);
v___x_1237_ = l_Lean_Syntax_matchesNull(v___x_1235_, v___x_1218_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec(v___x_1235_);
lean_dec_ref(v_dec_1222_);
lean_dec(v_elseSeq_1221_);
lean_dec(v_thenSeq_1220_);
lean_dec(v___x_1216_);
v___x_1238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = l_Lean_Syntax_getArg(v___x_1235_, v___x_1217_);
lean_dec(v___x_1235_);
v___x_1240_ = l_Lean_Syntax_getArg(v___x_1216_, v___x_1219_);
lean_dec(v___x_1216_);
v___x_1241_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(v___x_1239_, v___x_1240_, v_thenSeq_1220_, v_elseSeq_1221_, v_dec_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1241_;
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v___x_1235_);
v___x_1242_ = l_Lean_Syntax_getArg(v___x_1216_, v___x_1219_);
lean_dec(v___x_1216_);
v___x_1243_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(v___x_1242_, v_thenSeq_1220_, v_elseSeq_1221_, v_dec_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoIf___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1213_ = stack[0].m_obj;
lean_object* v___x_1214_ = stack[1].m_obj;
lean_object* v___x_1215_ = stack[2].m_obj;
lean_object* v___x_1216_ = stack[3].m_obj;
lean_object* v___x_1217_ = stack[4].m_obj;
lean_object* v___x_1218_ = stack[5].m_obj;
lean_object* v___x_1219_ = stack[6].m_obj;
lean_object* v_thenSeq_1220_ = stack[7].m_obj;
lean_object* v_elseSeq_1221_ = stack[8].m_obj;
lean_object* v_dec_1222_ = stack[9].m_obj;
lean_object* v___y_1223_ = stack[10].m_obj;
lean_object* v___y_1224_ = stack[11].m_obj;
lean_object* v___y_1225_ = stack[12].m_obj;
lean_object* v___y_1226_ = stack[13].m_obj;
lean_object* v___y_1227_ = stack[14].m_obj;
lean_object* v___y_1228_ = stack[15].m_obj;
lean_object* v___y_1229_ = stack[16].m_obj;
lean_object* v_res_1244_;
v_res_1244_ = l_Lean_Elab_Do_elabDoIf___lam__0(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1216_, v___x_1217_, v___x_1218_, v___x_1219_, v_thenSeq_1220_, v_elseSeq_1221_, v_dec_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
stack->m_obj
 = v_res_1244_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0___boxed(lean_object** _args){
lean_object* v___x_1245_ = _args[0];
lean_object* v___x_1246_ = _args[1];
lean_object* v___x_1247_ = _args[2];
lean_object* v___x_1248_ = _args[3];
lean_object* v___x_1249_ = _args[4];
lean_object* v___x_1250_ = _args[5];
lean_object* v___x_1251_ = _args[6];
lean_object* v_thenSeq_1252_ = _args[7];
lean_object* v_elseSeq_1253_ = _args[8];
lean_object* v_dec_1254_ = _args[9];
lean_object* v___y_1255_ = _args[10];
lean_object* v___y_1256_ = _args[11];
lean_object* v___y_1257_ = _args[12];
lean_object* v___y_1258_ = _args[13];
lean_object* v___y_1259_ = _args[14];
lean_object* v___y_1260_ = _args[15];
lean_object* v___y_1261_ = _args[16];
lean_object* v___y_1262_ = _args[17];
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Elab_Do_elabDoIf___lam__0(v___x_1245_, v___x_1246_, v___x_1247_, v___x_1248_, v___x_1249_, v___x_1250_, v___x_1251_, v_thenSeq_1252_, v_elseSeq_1253_, v_dec_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___x_1251_);
lean_dec(v___x_1250_);
lean_dec(v___x_1249_);
return v_res_1263_;
}
}
lean_object* l_Lean_Elab_Do_elabDoIf(lean_object* v_stx_1264_, lean_object* v_dec_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0));
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1));
v___x_1276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2));
v___x_1277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
lean_inc(v_stx_1264_);
v___x_1278_ = l_Lean_Syntax_isOfKind(v_stx_1264_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec_ref(v_dec_1265_);
lean_dec(v_stx_1264_);
v___x_1279_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_unsigned_to_nat(4u);
v___x_1282_ = l_Lean_Syntax_getArg(v_stx_1264_, v___x_1281_);
v___x_1283_ = l_Lean_Syntax_matchesNull(v___x_1282_, v___x_1280_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec_ref(v_dec_1265_);
lean_dec(v_stx_1264_);
v___x_1284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1285_ = lean_unsigned_to_nat(2u);
v___x_1286_ = lean_unsigned_to_nat(5u);
v___x_1287_ = l_Lean_Syntax_getArg(v_stx_1264_, v___x_1286_);
lean_inc(v___x_1287_);
v___x_1288_ = l_Lean_Syntax_matchesNull(v___x_1287_, v___x_1285_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
lean_dec(v___x_1287_);
lean_dec_ref(v_dec_1265_);
lean_dec(v_stx_1264_);
v___x_1289_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_thenSeq_1293_; lean_object* v_elseSeq_1294_; lean_object* v___f_1295_; lean_object* v___x_1296_; 
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = l_Lean_Syntax_getArg(v_stx_1264_, v___x_1290_);
v___x_1292_ = lean_unsigned_to_nat(3u);
v_thenSeq_1293_ = l_Lean_Syntax_getArg(v_stx_1264_, v___x_1292_);
lean_dec(v_stx_1264_);
v_elseSeq_1294_ = l_Lean_Syntax_getArg(v___x_1287_, v___x_1290_);
lean_dec(v___x_1287_);
lean_inc(v_elseSeq_1294_);
lean_inc(v_thenSeq_1293_);
v___f_1295_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___lam__0___boxed), 18, 9);
lean_closure_set(v___f_1295_, 0, v___x_1274_);
lean_closure_set(v___f_1295_, 1, v___x_1275_);
lean_closure_set(v___f_1295_, 2, v___x_1276_);
lean_closure_set(v___f_1295_, 3, v___x_1291_);
lean_closure_set(v___f_1295_, 4, v___x_1280_);
lean_closure_set(v___f_1295_, 5, v___x_1285_);
lean_closure_set(v___f_1295_, 6, v___x_1290_);
lean_closure_set(v___f_1295_, 7, v_thenSeq_1293_);
lean_closure_set(v___f_1295_, 8, v_elseSeq_1294_);
v___x_1296_ = l_Lean_Elab_Do_inferControlInfoSeq(v_thenSeq_1293_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = l_Lean_Elab_Do_inferControlInfoSeq(v_elseSeq_1294_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1297_, v_a_1299_);
v___x_1301_ = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(v_dec_1265_, v___x_1300_, v___f_1295_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1301_;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_a_1297_);
lean_dec_ref(v___f_1295_);
lean_dec_ref(v_dec_1265_);
v_a_1302_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1298_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1298_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v___f_1295_);
lean_dec(v_elseSeq_1294_);
lean_dec_ref(v_dec_1265_);
v_a_1310_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1296_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1296_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoIf_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1264_ = stack[0].m_obj;
lean_object* v_dec_1265_ = stack[1].m_obj;
lean_object* v_a_1266_ = stack[2].m_obj;
lean_object* v_a_1267_ = stack[3].m_obj;
lean_object* v_a_1268_ = stack[4].m_obj;
lean_object* v_a_1269_ = stack[5].m_obj;
lean_object* v_a_1270_ = stack[6].m_obj;
lean_object* v_a_1271_ = stack[7].m_obj;
lean_object* v_a_1272_ = stack[8].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l_Lean_Elab_Do_elabDoIf(v_stx_1264_, v_dec_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
stack->m_obj
 = v_res_1318_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___boxed(lean_object* v_stx_1319_, lean_object* v_dec_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Elab_Do_elabDoIf(v_stx_1319_, v_dec_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec_ref(v_a_1321_);
return v_res_1329_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1(){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1337_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_1338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1));
v___x_1340_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___boxed), 10, 0);
v___x_1341_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1337_, v___x_1338_, v___x_1339_, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1342_;
v_res_1342_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___boxed(lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
return v_res_1344_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_If(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
