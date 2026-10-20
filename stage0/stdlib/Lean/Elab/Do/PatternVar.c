// Lean compiler output
// Module: Lean.Elab.Do.PatternVar
// Imports: public import Lean.Elab.Term meta import Lean.Parser.Do import Lean.Elab.PatternVar import Lean.Elab.Quotation
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_HygieneInfo_mkIdent(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternVarsEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternsVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternsVarsEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__3_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Not a letId: "};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value),LEAN_SCALAR_PTR_LITERAL(38, 116, 214, 236, 212, 160, 188, 150)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14_value;
static const lean_array_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetIdDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetPatDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_getLetDeclVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__0 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__1 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_getLetDeclVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Not a let declaration: "};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__2 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_getLetDeclVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__3;
static const lean_string_object l_Lean_Elab_Do_getLetDeclVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__4 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__5 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_getLetDeclVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__6 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__7 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_getLetDeclVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letEqnsDecl"};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__8 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetDeclVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 210, 72, 51, 179, 245, 26, 94)}};
static const lean_object* l_Lean_Elab_Do_getLetDeclVars___closed__9 = (const lean_object*)&l_Lean_Elab_Do_getLetDeclVars___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_getLetRecDeclsVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_getLetRecDeclsVars___closed__0 = (const lean_object*)&l_Lean_Elab_Do_getLetRecDeclsVars___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_getLetRecDeclsVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_getLetRecDeclsVars___closed__1 = (const lean_object*)&l_Lean_Elab_Do_getLetRecDeclsVars___closed__1_value;
static const lean_array_object l_Lean_Elab_Do_getLetRecDeclsVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_getLetRecDeclsVars___closed__2 = (const lean_object*)&l_Lean_Elab_Do_getLetRecDeclsVars___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetRecDeclsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetRecDeclsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object* v_pattern_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_saveState___redArg(v_a_5_, v_a_7_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v___x_9_, 1);
lean_inc(v_pattern_1_);
v___x_11_ = l_Lean_Elab_Term_Quotation_getPatternVars(v_pattern_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
lean_dec(v_a_10_);
lean_dec(v_pattern_1_);
v_a_12_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v___x_11_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_58_; 
v_a_20_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_58_ == 0)
{
v___x_22_ = v___x_11_;
v_isShared_23_ = v_isSharedCheck_58_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_11_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_58_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___x_24_; 
v___x_24_ = l_Lean_Exception_isInterrupt(v_a_20_);
if (v___x_24_ == 0)
{
uint8_t v___x_25_; 
lean_inc(v_a_20_);
v___x_25_ = l_Lean_Exception_isRuntime(v_a_20_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
lean_del_object(v___x_22_);
lean_dec(v_a_20_);
v___x_26_ = l_Lean_Meta_SavedState_restore___redArg(v_a_10_, v_a_5_, v_a_7_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v___x_27_; 
lean_dec_ref_known(v___x_26_, 1);
v___x_27_ = l_Lean_Elab_Term_getPatternVars(v_pattern_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_a_36_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_27_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_27_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
lean_dec(v_pattern_1_);
v_a_44_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_26_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_26_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
else
{
lean_object* v___x_53_; 
lean_dec(v_a_10_);
lean_dec(v_pattern_1_);
if (v_isShared_23_ == 0)
{
v___x_53_ = v___x_22_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_20_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
else
{
lean_object* v___x_56_; 
lean_dec(v_a_10_);
lean_dec(v_pattern_1_);
if (v_isShared_23_ == 0)
{
v___x_56_ = v___x_22_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_20_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
lean_dec(v_pattern_1_);
v_a_59_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_9_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_9_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternVarsEx___boxed(lean_object* v_pattern_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternsVarsEx(lean_object* v_patterns_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_saveState___redArg(v_a_80_, v_a_82_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v___x_84_, 1);
v___x_86_ = l_Lean_Elab_Term_Quotation_getPatternsVars(v_patterns_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_dec(v_a_85_);
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_133_; 
v_a_95_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_133_ == 0)
{
v___x_97_ = v___x_86_;
v_isShared_98_ = v_isSharedCheck_133_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_86_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_133_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_Exception_isInterrupt(v_a_95_);
if (v___x_99_ == 0)
{
uint8_t v___x_100_; 
lean_inc(v_a_95_);
v___x_100_ = l_Lean_Exception_isRuntime(v_a_95_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_del_object(v___x_97_);
lean_dec(v_a_95_);
v___x_101_ = l_Lean_Meta_SavedState_restore___redArg(v_a_85_, v_a_80_, v_a_82_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v___x_102_; 
lean_dec_ref_known(v___x_101_, 1);
v___x_102_ = l_Lean_Elab_Term_getPatternsVars(v_patterns_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_102_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_102_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_101_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_101_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
else
{
lean_object* v___x_128_; 
lean_dec(v_a_85_);
if (v_isShared_98_ == 0)
{
v___x_128_ = v___x_97_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_95_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v_a_85_);
if (v_isShared_98_ == 0)
{
v___x_131_ = v___x_97_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_95_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_84_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_84_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternsVarsEx___boxed(lean_object* v_patterns_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Do_getPatternsVarsEx(v_patterns_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec_ref(v_patterns_142_);
return v_res_150_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_box(1);
v___x_152_ = l_Lean_MessageData_ofFormat(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2));
v___x_157_ = l_Lean_MessageData_ofFormat(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3(lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
return v_x_158_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_183_; 
v_head_160_ = lean_ctor_get(v_x_159_, 0);
v_tail_161_ = lean_ctor_get(v_x_159_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_183_ == 0)
{
v___x_163_ = v_x_159_;
v_isShared_164_ = v_isSharedCheck_183_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_tail_161_);
lean_inc(v_head_160_);
lean_dec(v_x_159_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_183_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_before_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_181_; 
v_before_165_ = lean_ctor_get(v_head_160_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_head_160_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_head_160_, 1);
lean_dec(v_unused_182_);
v___x_167_ = v_head_160_;
v_isShared_168_ = v_isSharedCheck_181_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_before_165_);
lean_dec(v_head_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_181_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_168_ == 0)
{
lean_ctor_set_tag(v___x_167_, 7);
lean_ctor_set(v___x_167_, 1, v___x_169_);
lean_ctor_set(v___x_167_, 0, v_x_158_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_x_158_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_180_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 7);
lean_ctor_set(v___x_163_, 1, v___x_172_);
lean_ctor_set(v___x_163_, 0, v___x_171_);
v___x_174_ = v___x_163_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_179_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = l_Lean_MessageData_ofSyntax(v_before_165_);
v___x_176_ = l_Lean_indentD(v___x_175_);
v___x_177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_174_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v_x_158_ = v___x_177_;
v_x_159_ = v_tail_161_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(lean_object* v_opts_184_, lean_object* v_opt_185_){
_start:
{
lean_object* v_name_186_; lean_object* v_defValue_187_; lean_object* v_map_188_; lean_object* v___x_189_; 
v_name_186_ = lean_ctor_get(v_opt_185_, 0);
v_defValue_187_ = lean_ctor_get(v_opt_185_, 1);
v_map_188_ = lean_ctor_get(v_opts_184_, 0);
v___x_189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_188_, v_name_186_);
if (lean_obj_tag(v___x_189_) == 0)
{
uint8_t v___x_190_; 
v___x_190_ = lean_unbox(v_defValue_187_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; 
v_val_191_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v___x_189_, 1);
if (lean_obj_tag(v_val_191_) == 1)
{
uint8_t v_v_192_; 
v_v_192_ = lean_ctor_get_uint8(v_val_191_, 0);
lean_dec_ref_known(v_val_191_, 0);
return v_v_192_;
}
else
{
uint8_t v___x_193_; 
lean_dec(v_val_191_);
v___x_193_ = lean_unbox(v_defValue_187_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_194_, lean_object* v_opt_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(v_opts_194_, v_opt_195_);
lean_dec_ref(v_opt_195_);
lean_dec_ref(v_opts_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1));
v___x_202_ = l_Lean_MessageData_ofFormat(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(lean_object* v_msgData_203_, lean_object* v_macroStack_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_207_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_205_);
v___x_208_ = l_Lean_Elab_pp_macroStack;
v___x_209_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(v___x_207_, v___x_208_);
lean_dec_ref(v___x_207_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec(v_macroStack_204_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_msgData_203_);
return v___x_210_;
}
else
{
if (lean_obj_tag(v_macroStack_204_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v_msgData_203_);
return v___x_211_;
}
else
{
lean_object* v_head_212_; lean_object* v_after_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_228_; 
v_head_212_ = lean_ctor_get(v_macroStack_204_, 0);
lean_inc(v_head_212_);
v_after_213_ = lean_ctor_get(v_head_212_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_head_212_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v_head_212_, 0);
lean_dec(v_unused_229_);
v___x_215_ = v_head_212_;
v_isShared_216_ = v_isSharedCheck_228_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_after_213_);
lean_dec(v_head_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_228_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 7);
lean_ctor_set(v___x_215_, 1, v___x_217_);
lean_ctor_set(v___x_215_, 0, v_msgData_203_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_msgData_203_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_227_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_msgData_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_220_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = l_Lean_MessageData_ofSyntax(v_after_213_);
v___x_223_ = l_Lean_indentD(v___x_222_);
v_msgData_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_224_, 0, v___x_221_);
lean_ctor_set(v_msgData_224_, 1, v___x_223_);
v___x_225_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3(v_msgData_224_, v_macroStack_204_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_230_, lean_object* v_macroStack_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_msgData_230_, v_macroStack_231_, v___y_232_);
lean_dec_ref(v___y_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(lean_object* v_msgData_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; lean_object* v_env_242_; uint8_t v___x_243_; lean_object* v_env_244_; lean_object* v___x_245_; lean_object* v_toCold_246_; lean_object* v_mctx_247_; lean_object* v_lctx_248_; lean_object* v_options_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_241_ = lean_st_ref_get(v___y_239_);
v_env_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_env_242_);
lean_dec(v___x_241_);
v___x_243_ = 0;
v_env_244_ = l_Lean_Environment_setRecordingDeps(v_env_242_, v___x_243_);
v___x_245_ = lean_st_ref_get(v___y_237_);
v_toCold_246_ = lean_ctor_get(v___y_238_, 0);
v_mctx_247_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_mctx_247_);
lean_dec(v___x_245_);
v_lctx_248_ = lean_ctor_get(v___y_236_, 2);
v_options_249_ = lean_ctor_get(v_toCold_246_, 2);
lean_inc_ref(v_options_249_);
lean_inc_ref(v_lctx_248_);
v___x_250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_250_, 0, v_env_244_);
lean_ctor_set(v___x_250_, 1, v_mctx_247_);
lean_ctor_set(v___x_250_, 2, v_lctx_248_);
lean_ctor_set(v___x_250_, 3, v_options_249_);
v___x_251_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_msgData_235_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0___boxed(lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(v_msgData_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_ref_268_; lean_object* v_macroStack_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_a_272_; lean_object* v___x_273_; lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_ref_268_ = lean_ctor_get(v___y_265_, 2);
v_macroStack_269_ = lean_ctor_get(v___y_261_, 1);
v___x_270_ = l_Lean_Elab_getBetterRef(v_ref_268_, v_macroStack_269_);
v___x_271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(v_msg_260_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_271_);
lean_inc(v_macroStack_269_);
v___x_273_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_a_272_, v_macroStack_269_, v___y_265_);
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_270_);
lean_ctor_set(v___x_278_, 1, v_a_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set_tag(v___x_276_, 1);
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg___boxed(lean_object* v_msg_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v_msg_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_291_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(lean_object* v_letId_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4));
lean_inc(v_letId_321_);
v___x_330_ = l_Lean_Syntax_isOfKind(v_letId_321_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_obj_once(&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6, &l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once, _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6);
v___x_332_ = l_Lean_MessageData_ofSyntax(v_letId_321_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_333_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v_id_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v_id_336_ = l_Lean_Syntax_getArg(v_letId_321_, v___x_335_);
v___x_337_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8));
lean_inc(v_id_336_);
v___x_338_ = l_Lean_Syntax_isOfKind(v_id_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10));
lean_inc(v_id_336_);
v___x_340_ = l_Lean_Syntax_isOfKind(v_id_336_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12));
lean_inc(v_id_336_);
v___x_342_ = l_Lean_Syntax_isOfKind(v_id_336_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_id_336_);
v___x_343_ = lean_obj_once(&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6, &l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once, _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6);
v___x_344_ = l_Lean_MessageData_ofSyntax(v_letId_321_);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_345_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_letId_321_);
v___x_347_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14));
v___x_348_ = l_Lean_HygieneInfo_mkIdent(v_id_336_, v___x_347_, v___x_342_);
lean_dec(v_id_336_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_mk_empty_array_with_capacity(v___x_349_);
v___x_351_ = lean_array_push(v___x_350_, v___x_348_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_letId_321_);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
v___x_355_ = lean_array_push(v___x_354_, v_id_336_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_id_336_);
lean_dec(v_letId_321_);
v___x_357_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___boxed(lean_object* v_letId_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(v_letId_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0(lean_object* v_00_u03b1_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v_msg_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___boxed(lean_object* v_00_u03b1_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0(v_00_u03b1_378_, v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1(lean_object* v_msgData_388_, lean_object* v_macroStack_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_msgData_388_, v_macroStack_389_, v___y_394_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___boxed(lean_object* v_msgData_398_, lean_object* v_macroStack_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1(v_msgData_398_, v_macroStack_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object* v_letIdDecl_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = l_Lean_Syntax_getArg(v_letIdDecl_408_, v___x_416_);
v___x_418_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(v___x_417_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetIdDeclVars___boxed(lean_object* v_letIdDecl_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Elab_Do_getLetIdDeclVars(v_letIdDecl_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_letIdDecl_419_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object* v_letPatDecl_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = l_Lean_Syntax_getArg(v_letPatDecl_428_, v___x_436_);
v___x_438_ = l_Lean_Elab_Do_getPatternVarsEx(v___x_437_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetPatDeclVars___boxed(lean_object* v_letPatDecl_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Elab_Do_getLetPatDeclVars(v_letPatDecl_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_letPatDecl_439_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(lean_object* v_letEqnsDecl_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = l_Lean_Syntax_getArg(v_letEqnsDecl_448_, v___x_456_);
v___x_458_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(v___x_457_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars___boxed(lean_object* v_letEqnsDecl_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(v_letEqnsDecl_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_letEqnsDecl_459_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Elab_Do_getLetDeclVars___closed__3(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__2));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetDeclVars(lean_object* v_letDecl_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__1));
lean_inc(v_letDecl_495_);
v___x_504_ = l_Lean_Syntax_isOfKind(v_letDecl_495_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_505_ = lean_obj_once(&l_Lean_Elab_Do_getLetDeclVars___closed__3, &l_Lean_Elab_Do_getLetDeclVars___closed__3_once, _init_l_Lean_Elab_Do_getLetDeclVars___closed__3);
v___x_506_ = lean_box(0);
v___x_507_ = l_Lean_Syntax_formatStx(v_letDecl_495_, v___x_506_, v___x_504_);
v___x_508_ = l_Std_Format_defWidth;
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l_Std_Format_pretty(v___x_507_, v___x_508_, v___x_509_, v___x_509_);
v___x_511_ = l_Lean_stringToMessageData(v___x_510_);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_505_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_512_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v_letIdDecl_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v_letIdDecl_515_ = l_Lean_Syntax_getArg(v_letDecl_495_, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__5));
lean_inc(v_letIdDecl_515_);
v___x_517_ = l_Lean_Syntax_isOfKind(v_letIdDecl_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__7));
lean_inc(v_letIdDecl_515_);
v___x_519_ = l_Lean_Syntax_isOfKind(v_letIdDecl_515_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__9));
lean_inc(v_letIdDecl_515_);
v___x_521_ = l_Lean_Syntax_isOfKind(v_letIdDecl_515_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_letIdDecl_515_);
v___x_522_ = lean_obj_once(&l_Lean_Elab_Do_getLetDeclVars___closed__3, &l_Lean_Elab_Do_getLetDeclVars___closed__3_once, _init_l_Lean_Elab_Do_getLetDeclVars___closed__3);
v___x_523_ = lean_box(0);
v___x_524_ = l_Lean_Syntax_formatStx(v_letDecl_495_, v___x_523_, v___x_521_);
v___x_525_ = l_Std_Format_defWidth;
v___x_526_ = l_Std_Format_pretty(v___x_524_, v___x_525_, v___x_514_, v___x_514_);
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_522_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_528_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
lean_dec(v_letDecl_495_);
v___x_530_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(v_letIdDecl_515_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_letIdDecl_515_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; 
lean_dec(v_letDecl_495_);
v___x_531_ = l_Lean_Elab_Do_getLetPatDeclVars(v_letIdDecl_515_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_letIdDecl_515_);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; 
lean_dec(v_letDecl_495_);
v___x_532_ = l_Lean_Elab_Do_getLetIdDeclVars(v_letIdDecl_515_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_letIdDecl_515_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetDeclVars___boxed(lean_object* v_letDecl_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Elab_Do_getLetDeclVars(v_letDecl_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(lean_object* v_letRecDecl_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = l_Lean_Syntax_getArg(v_letRecDecl_542_, v___x_550_);
v___x_552_ = l_Lean_Elab_Do_getLetDeclVars(v___x_551_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars___boxed(lean_object* v_letRecDecl_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(v_letRecDecl_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_letRecDecl_553_);
return v_res_561_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg(){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___boxed(lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(lean_object* v_00_u03b1_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___boxed(lean_object* v_00_u03b1_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(v_00_u03b1_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(size_t v_sz_594_, size_t v_i_595_, lean_object* v_bs_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_lt(v_i_595_, v_sz_594_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_bs_596_);
return v___x_598_;
}
else
{
lean_object* v_v_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_v_599_ = lean_array_uget(v_bs_596_, v_i_595_);
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1));
lean_inc(v_v_599_);
v___x_601_ = l_Lean_Syntax_isOfKind(v_v_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v_v_599_);
lean_dec_ref(v_bs_596_);
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v_bs_x27_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v_bs_x27_604_ = lean_array_uset(v_bs_596_, v_i_595_, v___x_603_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_595_, v___x_605_);
v___x_607_ = lean_array_uset(v_bs_x27_604_, v_i_595_, v_v_599_);
v_i_595_ = v___x_606_;
v_bs_596_ = v___x_607_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___boxed(lean_object* v_sz_609_, lean_object* v_i_610_, lean_object* v_bs_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_609_);
lean_dec(v_sz_609_);
v_i_boxed_613_ = lean_unbox_usize(v_i_610_);
lean_dec(v_i_610_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(v_sz_boxed_612_, v_i_boxed_613_, v_bs_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(lean_object* v_as_615_, size_t v_sz_616_, size_t v_i_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_617_, v_sz_616_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_b_618_);
return v___x_627_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_629_; 
v_a_628_ = lean_array_uget_borrowed(v_as_615_, v_i_617_);
v___x_629_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(v_a_628_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; size_t v___x_632_; size_t v___x_633_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = l_Array_append___redArg(v_b_618_, v_a_630_);
lean_dec(v_a_630_);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_617_, v___x_632_);
v_i_617_ = v___x_633_;
v_b_618_ = v___x_631_;
goto _start;
}
else
{
lean_dec_ref(v_b_618_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2___boxed(lean_object* v_as_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_b_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
size_t v_sz_boxed_646_; size_t v_i_boxed_647_; lean_object* v_res_648_; 
v_sz_boxed_646_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_647_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(v_as_635_, v_sz_boxed_646_, v_i_boxed_647_, v_b_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v_as_635_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(uint8_t v___x_649_, lean_object* v_as_650_, size_t v_i_651_, size_t v_stop_652_, lean_object* v_b_653_){
_start:
{
lean_object* v___y_655_; uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_eq(v_i_651_, v_stop_652_);
if (v___x_659_ == 0)
{
lean_object* v_fst_660_; uint8_t v___x_661_; 
v_fst_660_ = lean_ctor_get(v_b_653_, 0);
v___x_661_ = lean_unbox(v_fst_660_);
if (v___x_661_ == 0)
{
lean_object* v_snd_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_snd_662_ = lean_ctor_get(v_b_653_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_b_653_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_b_653_, 0);
lean_dec(v_unused_671_);
v___x_664_ = v_b_653_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snd_662_);
lean_dec(v_b_653_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_box(v___x_649_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_662_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
v___y_655_ = v___x_668_;
goto v___jp_654_;
}
}
}
else
{
lean_object* v_snd_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_682_; 
v_snd_672_ = lean_ctor_get(v_b_653_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_b_653_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v_b_653_, 0);
lean_dec(v_unused_683_);
v___x_674_ = v_b_653_;
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snd_672_);
lean_dec(v_b_653_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_676_ = lean_array_uget_borrowed(v_as_650_, v_i_651_);
lean_inc(v___x_676_);
v___x_677_ = lean_array_push(v_snd_672_, v___x_676_);
v___x_678_ = lean_box(v___x_659_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_677_);
lean_ctor_set(v___x_674_, 0, v___x_678_);
v___x_680_ = v___x_674_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_677_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
v___y_655_ = v___x_680_;
goto v___jp_654_;
}
}
}
}
else
{
return v_b_653_;
}
v___jp_654_:
{
size_t v___x_656_; size_t v___x_657_; 
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_add(v_i_651_, v___x_656_);
v_i_651_ = v___x_657_;
v_b_653_ = v___y_655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3___boxed(lean_object* v___x_684_, lean_object* v_as_685_, lean_object* v_i_686_, lean_object* v_stop_687_, lean_object* v_b_688_){
_start:
{
uint8_t v___x_1616__boxed_689_; size_t v_i_boxed_690_; size_t v_stop_boxed_691_; lean_object* v_res_692_; 
v___x_1616__boxed_689_ = lean_unbox(v___x_684_);
v_i_boxed_690_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_stop_boxed_691_ = lean_unbox_usize(v_stop_687_);
lean_dec(v_stop_687_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(v___x_1616__boxed_689_, v_as_685_, v_i_boxed_690_, v_stop_boxed_691_, v_b_688_);
lean_dec_ref(v_as_685_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetRecDeclsVars(lean_object* v_letRecDecls_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___y_710_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lean_Elab_Do_getLetRecDeclsVars___closed__1));
lean_inc(v_letRecDecls_701_);
v___x_720_ = l_Lean_Syntax_isOfKind(v_letRecDecls_701_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec(v_letRecDecls_701_);
v___x_721_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = l_Lean_Syntax_getArg(v_letRecDecls_701_, v___x_722_);
lean_dec(v_letRecDecls_701_);
v___x_724_ = l_Lean_Syntax_getArgs(v___x_723_);
lean_dec(v___x_723_);
v___x_725_ = ((lean_object*)(l_Lean_Elab_Do_getLetRecDeclsVars___closed__2));
v___x_726_ = lean_array_get_size(v___x_724_);
v___x_727_ = lean_nat_dec_lt(v___x_722_, v___x_726_);
if (v___x_727_ == 0)
{
lean_dec_ref(v___x_724_);
v___y_710_ = v___x_725_;
goto v___jp_709_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; size_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; lean_object* v_snd_733_; 
v___x_728_ = lean_box(v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_725_);
v___x_730_ = ((size_t)0ULL);
v___x_731_ = lean_usize_of_nat(v___x_726_);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(v___x_720_, v___x_724_, v___x_730_, v___x_731_, v___x_729_);
lean_dec_ref(v___x_724_);
v_snd_733_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_snd_733_);
lean_dec_ref(v___x_732_);
v___y_710_ = v_snd_733_;
goto v___jp_709_;
}
}
v___jp_709_:
{
size_t v_sz_711_; size_t v___x_712_; lean_object* v___x_713_; 
v_sz_711_ = lean_array_size(v___y_710_);
v___x_712_ = ((size_t)0ULL);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(v_sz_711_, v___x_712_, v___y_710_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_714_;
}
else
{
lean_object* v_val_715_; lean_object* v_allVars_716_; size_t v_sz_717_; lean_object* v___x_718_; 
v_val_715_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_715_);
lean_dec_ref_known(v___x_713_, 1);
v_allVars_716_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v_sz_717_ = lean_array_size(v_val_715_);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(v_val_715_, v_sz_717_, v___x_712_, v_allVars_716_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_val_715_);
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetRecDeclsVars___boxed(lean_object* v_letRecDecls_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_letRecDecls_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(size_t v_sz_743_, size_t v_i_744_, lean_object* v_bs_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = lean_usize_dec_lt(v_i_744_, v_sz_743_);
if (v___x_746_ == 0)
{
return v_bs_745_;
}
else
{
lean_object* v_v_747_; lean_object* v___x_748_; lean_object* v_bs_x27_749_; size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v_v_747_ = lean_array_uget(v_bs_745_, v_i_744_);
v___x_748_ = lean_unsigned_to_nat(0u);
v_bs_x27_749_ = lean_array_uset(v_bs_745_, v_i_744_, v___x_748_);
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_744_, v___x_750_);
v___x_752_ = lean_array_uset(v_bs_x27_749_, v_i_744_, v_v_747_);
v_i_744_ = v___x_751_;
v_bs_745_ = v___x_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2___boxed(lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_bs_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_758_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(v_sz_boxed_757_, v_i_boxed_758_, v_bs_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(size_t v_sz_760_, size_t v_i_761_, lean_object* v_bs_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = lean_usize_dec_lt(v_i_761_, v_sz_760_);
if (v___x_763_ == 0)
{
return v_bs_762_;
}
else
{
lean_object* v_v_764_; lean_object* v___x_765_; lean_object* v_bs_x27_766_; size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v_v_764_ = lean_array_uget(v_bs_762_, v_i_761_);
v___x_765_ = lean_unsigned_to_nat(0u);
v_bs_x27_766_ = lean_array_uset(v_bs_762_, v_i_761_, v___x_765_);
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_761_, v___x_767_);
v___x_769_ = lean_array_uset(v_bs_x27_766_, v_i_761_, v_v_764_);
v_i_761_ = v___x_768_;
v_bs_762_ = v___x_769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0___boxed(lean_object* v_sz_771_, lean_object* v_i_772_, lean_object* v_bs_773_){
_start:
{
size_t v_sz_boxed_774_; size_t v_i_boxed_775_; lean_object* v_res_776_; 
v_sz_boxed_774_ = lean_unbox_usize(v_sz_771_);
lean_dec(v_sz_771_);
v_i_boxed_775_ = lean_unbox_usize(v_i_772_);
lean_dec(v_i_772_);
v_res_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_boxed_774_, v_i_boxed_775_, v_bs_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(lean_object* v_as_777_, size_t v_i_778_, size_t v_stop_779_, lean_object* v_b_780_){
_start:
{
lean_object* v___y_782_; uint8_t v___x_786_; 
v___x_786_ = lean_usize_dec_eq(v_i_778_, v_stop_779_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = lean_array_uget_borrowed(v_as_777_, v_i_778_);
v___x_788_ = l_Lean_Syntax_isIdent(v___x_787_);
if (v___x_788_ == 0)
{
v___y_782_ = v_b_780_;
goto v___jp_781_;
}
else
{
lean_object* v___x_789_; 
lean_inc(v___x_787_);
v___x_789_ = lean_array_push(v_b_780_, v___x_787_);
v___y_782_ = v___x_789_;
goto v___jp_781_;
}
}
else
{
return v_b_780_;
}
v___jp_781_:
{
size_t v___x_783_; size_t v___x_784_; 
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_778_, v___x_783_);
v_i_778_ = v___x_784_;
v_b_780_ = v___y_782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1___boxed(lean_object* v_as_790_, lean_object* v_i_791_, lean_object* v_stop_792_, lean_object* v_b_793_){
_start:
{
size_t v_i_boxed_794_; size_t v_stop_boxed_795_; lean_object* v_res_796_; 
v_i_boxed_794_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_stop_boxed_795_ = lean_unbox_usize(v_stop_792_);
lean_dec(v_stop_792_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_as_790_, v_i_boxed_794_, v_stop_boxed_795_, v_b_793_);
lean_dec_ref(v_as_790_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg(lean_object* v_exprPattern_803_){
_start:
{
lean_object* v___y_806_; size_t v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1));
lean_inc(v_exprPattern_803_);
v___x_820_ = l_Lean_Syntax_isOfKind(v_exprPattern_803_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v_exprPattern_803_);
v___x_821_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v_var_x3f_824_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_850_ = l_Lean_Syntax_getArg(v_exprPattern_803_, v___x_822_);
v___x_851_ = l_Lean_Syntax_isNone(v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_850_);
v___x_853_ = l_Lean_Syntax_matchesNull(v___x_850_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v___x_850_);
lean_dec(v_exprPattern_803_);
v___x_854_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_854_;
}
else
{
lean_object* v_var_x3f_855_; lean_object* v___x_856_; 
v_var_x3f_855_ = l_Lean_Syntax_getArg(v___x_850_, v___x_822_);
lean_dec(v___x_850_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_var_x3f_855_);
v_var_x3f_824_ = v___x_856_;
goto v___jp_823_;
}
}
else
{
lean_object* v___x_857_; 
lean_dec(v___x_850_);
v___x_857_ = lean_box(0);
v_var_x3f_824_ = v___x_857_;
goto v___jp_823_;
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = l_Lean_Syntax_getArg(v_exprPattern_803_, v___x_825_);
v___x_827_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10));
v___x_828_ = l_Lean_Syntax_isOfKind(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v_var_x3f_824_);
lean_dec(v_exprPattern_803_);
v___x_829_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_pvars_832_; 
v___x_830_ = lean_unsigned_to_nat(2u);
v___x_831_ = l_Lean_Syntax_getArg(v_exprPattern_803_, v___x_830_);
lean_dec(v_exprPattern_803_);
v_pvars_832_ = l_Lean_Syntax_getArgs(v___x_831_);
lean_dec(v___x_831_);
if (lean_obj_tag(v_var_x3f_824_) == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_array_get_size(v_pvars_832_);
v___x_834_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v___x_835_ = lean_nat_dec_lt(v___x_822_, v___x_833_);
if (v___x_835_ == 0)
{
lean_dec_ref(v_pvars_832_);
v___y_806_ = v___x_834_;
goto v___jp_805_;
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_833_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_832_, v___x_836_, v___x_837_, v___x_834_);
lean_dec_ref(v_pvars_832_);
v___y_806_ = v___x_838_;
goto v___jp_805_;
}
}
else
{
lean_object* v_val_839_; lean_object* v___x_840_; lean_object* v___x_841_; size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_val_839_ = lean_ctor_get(v_var_x3f_824_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v_var_x3f_824_, 1);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_825_);
v___x_841_ = lean_array_push(v___x_840_, v_val_839_);
v_sz_842_ = lean_array_size(v___x_841_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(v_sz_842_, v___x_843_, v___x_841_);
v___x_845_ = lean_array_get_size(v_pvars_832_);
v___x_846_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v___x_847_ = lean_nat_dec_lt(v___x_822_, v___x_845_);
if (v___x_847_ == 0)
{
lean_dec_ref(v_pvars_832_);
v___y_812_ = v___x_843_;
v___y_813_ = v___x_844_;
v___y_814_ = v___x_846_;
goto v___jp_811_;
}
else
{
size_t v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_usize_of_nat(v___x_845_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_832_, v___x_843_, v___x_848_, v___x_846_);
lean_dec_ref(v_pvars_832_);
v___y_812_ = v___x_843_;
v___y_813_ = v___x_844_;
v___y_814_ = v___x_849_;
goto v___jp_811_;
}
}
}
}
}
v___jp_805_:
{
size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_sz_807_ = lean_array_size(v___y_806_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_807_, v___x_808_, v___y_806_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
v___jp_811_:
{
lean_object* v___x_815_; size_t v_sz_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_815_ = l_Array_append___redArg(v___y_813_, v___y_814_);
lean_dec_ref(v___y_814_);
v_sz_816_ = lean_array_size(v___x_815_);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_816_, v___y_812_, v___x_815_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg___boxed(lean_object* v_exprPattern_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_exprPattern_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx(lean_object* v_exprPattern_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_exprPattern_861_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___boxed(lean_object* v_exprPattern_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Elab_Do_getExprPatternVarsEx(v_exprPattern_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
return v_res_878_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PatternVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Quotation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Quotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_PatternVar(uint8_t builtin);
lean_object* initialize_Lean_Elab_Quotation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_PatternVar(builtin);
}
#ifdef __cplusplus
}
#endif
