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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__7_value),LEAN_SCALAR_PTR_LITERAL(38, 116, 214, 236, 212, 160, 188, 150)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__9_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13 = (const lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__13_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
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
lean_object* v___y_10_; lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_saveState___redArg(v_a_5_, v_a_7_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_29_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
lean_dec_ref_known(v___x_27_, 1);
lean_inc(v_pattern_1_);
v___x_29_ = l_Lean_Elab_Term_Quotation_getPatternVars(v_pattern_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_dec(v_a_28_);
lean_dec(v_pattern_1_);
v___y_10_ = v___x_29_;
goto v___jp_9_;
}
else
{
lean_object* v_a_30_; uint8_t v___y_32_; uint8_t v___x_43_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v___x_43_ = l_Lean_Exception_isInterrupt(v_a_30_);
if (v___x_43_ == 0)
{
uint8_t v___x_44_; 
lean_inc(v_a_30_);
v___x_44_ = l_Lean_Exception_isRuntime(v_a_30_);
v___y_32_ = v___x_44_;
goto v___jp_31_;
}
else
{
v___y_32_ = v___x_43_;
goto v___jp_31_;
}
v___jp_31_:
{
if (v___y_32_ == 0)
{
lean_object* v___x_33_; 
lean_dec_ref_known(v___x_29_, 1);
v___x_33_ = l_Lean_Meta_SavedState_restore___redArg(v_a_28_, v_a_5_, v_a_7_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v___x_34_; 
lean_dec_ref_known(v___x_33_, 1);
v___x_34_ = l_Lean_Elab_Term_getPatternVars(v_pattern_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
v___y_10_ = v___x_34_;
goto v___jp_9_;
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
lean_dec(v_pattern_1_);
v_a_35_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
else
{
lean_dec(v_a_28_);
lean_dec(v_pattern_1_);
v___y_10_ = v___x_29_;
goto v___jp_9_;
}
}
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
lean_dec(v_pattern_1_);
v_a_45_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_27_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_27_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
v___jp_9_:
{
if (lean_obj_tag(v___y_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_a_11_ = lean_ctor_get(v___y_10_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___y_10_);
if (v_isSharedCheck_18_ == 0)
{
v___x_13_ = v___y_10_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_dec(v___y_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
if (v_isShared_14_ == 0)
{
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_a_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
else
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
v_a_19_ = lean_ctor_get(v___y_10_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___y_10_);
if (v_isSharedCheck_26_ == 0)
{
v___x_21_ = v___y_10_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___y_10_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_a_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternVarsEx___boxed(lean_object* v_pattern_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternsVarsEx(lean_object* v_patterns_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___y_71_; lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_saveState___redArg(v_a_66_, v_a_68_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_88_, 1);
v___x_90_ = l_Lean_Elab_Term_Quotation_getPatternsVars(v_patterns_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_dec(v_a_89_);
v___y_71_ = v___x_90_;
goto v___jp_70_;
}
else
{
lean_object* v_a_91_; uint8_t v___y_93_; uint8_t v___x_104_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v___x_104_ = l_Lean_Exception_isInterrupt(v_a_91_);
if (v___x_104_ == 0)
{
uint8_t v___x_105_; 
lean_inc(v_a_91_);
v___x_105_ = l_Lean_Exception_isRuntime(v_a_91_);
v___y_93_ = v___x_105_;
goto v___jp_92_;
}
else
{
v___y_93_ = v___x_104_;
goto v___jp_92_;
}
v___jp_92_:
{
if (v___y_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref_known(v___x_90_, 1);
v___x_94_ = l_Lean_Meta_SavedState_restore___redArg(v_a_89_, v_a_66_, v_a_68_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; 
lean_dec_ref_known(v___x_94_, 1);
v___x_95_ = l_Lean_Elab_Term_getPatternsVars(v_patterns_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
v___y_71_ = v___x_95_;
goto v___jp_70_;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_94_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_dec(v_a_89_);
v___y_71_ = v___x_90_;
goto v___jp_70_;
}
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_88_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_88_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
v___jp_70_:
{
if (lean_obj_tag(v___y_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_a_72_ = lean_ctor_get(v___y_71_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___y_71_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___y_71_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___y_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_a_80_ = lean_ctor_get(v___y_71_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___y_71_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___y_71_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___y_71_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getPatternsVarsEx___boxed(lean_object* v_patterns_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Elab_Do_getPatternsVarsEx(v_patterns_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec_ref(v_patterns_114_);
return v_res_122_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_box(1);
v___x_124_ = l_Lean_MessageData_ofFormat(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__2));
v___x_129_ = l_Lean_MessageData_ofFormat(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
return v_x_130_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_155_; 
v_head_132_ = lean_ctor_get(v_x_131_, 0);
v_tail_133_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_155_ == 0)
{
v___x_135_ = v_x_131_;
v_isShared_136_ = v_isSharedCheck_155_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_head_132_);
lean_dec(v_x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_155_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_before_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_153_; 
v_before_137_ = lean_ctor_get(v_head_132_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v_head_132_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v_head_132_, 1);
lean_dec(v_unused_154_);
v___x_139_ = v_head_132_;
v_isShared_140_ = v_isSharedCheck_153_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_before_137_);
lean_dec(v_head_132_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_153_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 7);
lean_ctor_set(v___x_139_, 1, v___x_141_);
lean_ctor_set(v___x_139_, 0, v_x_130_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_x_130_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_152_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 7);
lean_ctor_set(v___x_135_, 1, v___x_144_);
lean_ctor_set(v___x_135_, 0, v___x_143_);
v___x_146_ = v___x_135_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_151_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = l_Lean_MessageData_ofSyntax(v_before_137_);
v___x_148_ = l_Lean_indentD(v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_146_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v_x_130_ = v___x_149_;
v_x_131_ = v_tail_133_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(lean_object* v_opts_156_, lean_object* v_opt_157_){
_start:
{
lean_object* v_name_158_; lean_object* v_defValue_159_; lean_object* v_map_160_; lean_object* v___x_161_; 
v_name_158_ = lean_ctor_get(v_opt_157_, 0);
v_defValue_159_ = lean_ctor_get(v_opt_157_, 1);
v_map_160_ = lean_ctor_get(v_opts_156_, 0);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_160_, v_name_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
uint8_t v___x_162_; 
v___x_162_ = lean_unbox(v_defValue_159_);
return v___x_162_;
}
else
{
lean_object* v_val_163_; 
v_val_163_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v___x_161_, 1);
if (lean_obj_tag(v_val_163_) == 1)
{
uint8_t v_v_164_; 
v_v_164_ = lean_ctor_get_uint8(v_val_163_, 0);
lean_dec_ref_known(v_val_163_, 0);
return v_v_164_;
}
else
{
uint8_t v___x_165_; 
lean_dec(v_val_163_);
v___x_165_ = lean_unbox(v_defValue_159_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_166_, lean_object* v_opt_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(v_opts_166_, v_opt_167_);
lean_dec_ref(v_opt_167_);
lean_dec_ref(v_opts_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__1));
v___x_174_ = l_Lean_MessageData_ofFormat(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(lean_object* v_msgData_175_, lean_object* v_macroStack_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_177_);
v___x_180_ = l_Lean_Elab_pp_macroStack;
v___x_181_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__2(v___x_179_, v___x_180_);
lean_dec_ref(v___x_179_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v_macroStack_176_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_msgData_175_);
return v___x_182_;
}
else
{
if (lean_obj_tag(v_macroStack_176_) == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v_msgData_175_);
return v___x_183_;
}
else
{
lean_object* v_head_184_; lean_object* v_after_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_200_; 
v_head_184_ = lean_ctor_get(v_macroStack_176_, 0);
lean_inc(v_head_184_);
v_after_185_ = lean_ctor_get(v_head_184_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_head_184_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_head_184_, 0);
lean_dec(v_unused_201_);
v___x_187_ = v_head_184_;
v_isShared_188_ = v_isSharedCheck_200_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_after_185_);
lean_dec(v_head_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_200_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 7);
lean_ctor_set(v___x_187_, 1, v___x_189_);
lean_ctor_set(v___x_187_, 0, v_msgData_175_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_msgData_175_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_199_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_msgData_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___closed__2);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = l_Lean_MessageData_ofSyntax(v_after_185_);
v___x_195_ = l_Lean_indentD(v___x_194_);
v_msgData_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_196_, 0, v___x_193_);
lean_ctor_set(v_msgData_196_, 1, v___x_195_);
v___x_197_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1_spec__3(v_msgData_196_, v_macroStack_176_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_202_, lean_object* v_macroStack_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_msgData_202_, v_macroStack_203_, v___y_204_);
lean_dec_ref(v___y_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(lean_object* v_msgData_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_env_214_; uint8_t v___x_215_; lean_object* v_env_216_; lean_object* v___x_217_; lean_object* v_toCold_218_; lean_object* v_mctx_219_; lean_object* v_lctx_220_; lean_object* v_options_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_213_ = lean_st_ref_get(v___y_211_);
v_env_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc_ref(v_env_214_);
lean_dec(v___x_213_);
v___x_215_ = 0;
v_env_216_ = l_Lean_Environment_setRecordingDeps(v_env_214_, v___x_215_);
v___x_217_ = lean_st_ref_get(v___y_209_);
v_toCold_218_ = lean_ctor_get(v___y_210_, 0);
v_mctx_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc_ref(v_mctx_219_);
lean_dec(v___x_217_);
v_lctx_220_ = lean_ctor_get(v___y_208_, 2);
v_options_221_ = lean_ctor_get(v_toCold_218_, 2);
lean_inc_ref(v_options_221_);
lean_inc_ref(v_lctx_220_);
v___x_222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_222_, 0, v_env_216_);
lean_ctor_set(v___x_222_, 1, v_mctx_219_);
lean_ctor_set(v___x_222_, 2, v_lctx_220_);
lean_ctor_set(v___x_222_, 3, v_options_221_);
v___x_223_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_msgData_207_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0___boxed(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(v_msgData_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_ref_240_; lean_object* v_macroStack_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_a_244_; lean_object* v___x_245_; lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_ref_240_ = lean_ctor_get(v___y_237_, 2);
v_macroStack_241_ = lean_ctor_get(v___y_233_, 1);
v___x_242_ = l_Lean_Elab_getBetterRef(v_ref_240_, v_macroStack_241_);
v___x_243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__0(v_msg_232_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref(v___x_243_);
lean_inc(v_macroStack_241_);
v___x_245_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_a_244_, v_macroStack_241_, v___y_237_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_242_);
lean_ctor_set(v___x_250_, 1, v_a_246_);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg___boxed(lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v_msg_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_263_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__5));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(lean_object* v_letId_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__4));
lean_inc(v_letId_293_);
v___x_302_ = l_Lean_Syntax_isOfKind(v_letId_293_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6, &l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once, _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6);
v___x_304_ = l_Lean_MessageData_ofSyntax(v_letId_293_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_305_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v_s_308_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v_s_308_ = l_Lean_Syntax_getArg(v_letId_293_, v___x_307_);
v___x_321_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__10));
lean_inc(v_s_308_);
v___x_322_ = l_Lean_Syntax_isOfKind(v_s_308_, v___x_321_);
if (v___x_322_ == 0)
{
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12));
lean_inc(v_s_308_);
v___x_324_ = l_Lean_Syntax_isOfKind(v_s_308_, v___x_323_);
if (v___x_324_ == 0)
{
if (v___x_322_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__14));
lean_inc(v_s_308_);
v___x_326_ = l_Lean_Syntax_isOfKind(v_s_308_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_s_308_);
v___x_327_ = lean_obj_once(&l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6, &l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6_once, _init_l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__6);
v___x_328_ = l_Lean_MessageData_ofSyntax(v_letId_293_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_329_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
return v___x_330_;
}
else
{
lean_dec(v_letId_293_);
goto v___jp_309_;
}
}
else
{
lean_dec(v_letId_293_);
goto v___jp_309_;
}
}
else
{
lean_dec(v_letId_293_);
goto v___jp_316_;
}
}
else
{
lean_dec(v_letId_293_);
goto v___jp_316_;
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_s_308_);
lean_dec(v_letId_293_);
v___x_331_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
v___jp_309_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__8));
v___x_311_ = l_Lean_HygieneInfo_mkIdent(v_s_308_, v___x_310_, v___x_302_);
lean_dec(v_s_308_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_312_);
v___x_314_ = lean_array_push(v___x_313_, v___x_311_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
v___x_319_ = lean_array_push(v___x_318_, v_s_308_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___boxed(lean_object* v_letId_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(v_letId_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0(lean_object* v_00_u03b1_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v_msg_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___boxed(lean_object* v_00_u03b1_352_, lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0(v_00_u03b1_352_, v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1(lean_object* v_msgData_362_, lean_object* v_macroStack_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___redArg(v_msgData_362_, v_macroStack_363_, v___y_368_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1___boxed(lean_object* v_msgData_372_, lean_object* v_macroStack_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0_spec__1(v_msgData_372_, v_macroStack_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object* v_letIdDecl_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = l_Lean_Syntax_getArg(v_letIdDecl_382_, v___x_390_);
v___x_392_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(v___x_391_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetIdDeclVars___boxed(lean_object* v_letIdDecl_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Elab_Do_getLetIdDeclVars(v_letIdDecl_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_letIdDecl_393_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object* v_letPatDecl_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = l_Lean_Syntax_getArg(v_letPatDecl_402_, v___x_410_);
v___x_412_ = l_Lean_Elab_Do_getPatternVarsEx(v___x_411_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetPatDeclVars___boxed(lean_object* v_letPatDecl_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Elab_Do_getLetPatDeclVars(v_letPatDecl_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_letPatDecl_413_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(lean_object* v_letEqnsDecl_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = l_Lean_Syntax_getArg(v_letEqnsDecl_422_, v___x_430_);
v___x_432_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars(v___x_431_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars___boxed(lean_object* v_letEqnsDecl_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(v_letEqnsDecl_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_letEqnsDecl_433_);
return v_res_441_;
}
}
static lean_object* _init_l_Lean_Elab_Do_getLetDeclVars___closed__3(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__2));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetDeclVars(lean_object* v_letDecl_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__1));
lean_inc(v_letDecl_469_);
v___x_478_ = l_Lean_Syntax_isOfKind(v_letDecl_469_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_479_ = lean_obj_once(&l_Lean_Elab_Do_getLetDeclVars___closed__3, &l_Lean_Elab_Do_getLetDeclVars___closed__3_once, _init_l_Lean_Elab_Do_getLetDeclVars___closed__3);
v___x_480_ = lean_box(0);
v___x_481_ = l_Lean_Syntax_formatStx(v_letDecl_469_, v___x_480_, v___x_478_);
v___x_482_ = l_Std_Format_defWidth;
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = l_Std_Format_pretty(v___x_481_, v___x_482_, v___x_483_, v___x_483_);
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_479_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_486_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v_letIdDecl_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v_letIdDecl_489_ = l_Lean_Syntax_getArg(v_letDecl_469_, v___x_488_);
v___x_490_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__5));
lean_inc(v_letIdDecl_489_);
v___x_491_ = l_Lean_Syntax_isOfKind(v_letIdDecl_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__7));
lean_inc(v_letIdDecl_489_);
v___x_493_ = l_Lean_Syntax_isOfKind(v_letIdDecl_489_, v___x_492_);
if (v___x_493_ == 0)
{
if (v___x_493_ == 0)
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Elab_Do_getLetDeclVars___closed__9));
lean_inc(v_letIdDecl_489_);
v___x_495_ = l_Lean_Syntax_isOfKind(v_letIdDecl_489_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_letIdDecl_489_);
v___x_496_ = lean_obj_once(&l_Lean_Elab_Do_getLetDeclVars___closed__3, &l_Lean_Elab_Do_getLetDeclVars___closed__3_once, _init_l_Lean_Elab_Do_getLetDeclVars___closed__3);
v___x_497_ = lean_box(0);
v___x_498_ = l_Lean_Syntax_formatStx(v_letDecl_469_, v___x_497_, v___x_495_);
v___x_499_ = l_Std_Format_defWidth;
v___x_500_ = l_Std_Format_pretty(v___x_498_, v___x_499_, v___x_488_, v___x_488_);
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_496_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l_Lean_throwError___at___00__private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars_spec__0___redArg(v___x_502_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; 
lean_dec(v_letDecl_469_);
v___x_504_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetEqnsDeclVars(v_letIdDecl_489_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_letIdDecl_489_);
return v___x_504_;
}
}
else
{
lean_object* v___x_505_; 
lean_dec(v_letDecl_469_);
v___x_505_ = l_Lean_Elab_Do_getLetPatDeclVars(v_letIdDecl_489_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_letIdDecl_489_);
return v___x_505_;
}
}
else
{
lean_object* v___x_506_; 
lean_dec(v_letDecl_469_);
v___x_506_ = l_Lean_Elab_Do_getLetPatDeclVars(v_letIdDecl_489_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_letIdDecl_489_);
return v___x_506_;
}
}
else
{
lean_object* v___x_507_; 
lean_dec(v_letDecl_469_);
v___x_507_ = l_Lean_Elab_Do_getLetIdDeclVars(v_letIdDecl_489_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_letIdDecl_489_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetDeclVars___boxed(lean_object* v_letDecl_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Elab_Do_getLetDeclVars(v_letDecl_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(lean_object* v_letRecDecl_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = l_Lean_Syntax_getArg(v_letRecDecl_517_, v___x_525_);
v___x_527_ = l_Lean_Elab_Do_getLetDeclVars(v___x_526_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars___boxed(lean_object* v_letRecDecl_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(v_letRecDecl_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_letRecDecl_528_);
return v_res_536_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_box(0);
v___x_538_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___x_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg(){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___closed__0);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg___boxed(lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(lean_object* v_00_u03b1_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___boxed(lean_object* v_00_u03b1_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1(v_00_u03b1_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(size_t v_sz_569_, size_t v_i_570_, lean_object* v_bs_571_){
_start:
{
uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_lt(v_i_570_, v_sz_569_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_bs_571_);
return v___x_573_;
}
else
{
lean_object* v_v_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_v_574_ = lean_array_uget(v_bs_571_, v_i_570_);
v___x_575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___closed__1));
lean_inc(v_v_574_);
v___x_576_ = l_Lean_Syntax_isOfKind(v_v_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v_v_574_);
lean_dec_ref(v_bs_571_);
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v_bs_x27_579_; size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v_bs_x27_579_ = lean_array_uset(v_bs_571_, v_i_570_, v___x_578_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_570_, v___x_580_);
v___x_582_ = lean_array_uset(v_bs_x27_579_, v_i_570_, v_v_574_);
v_i_570_ = v___x_581_;
v_bs_571_ = v___x_582_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0___boxed(lean_object* v_sz_584_, lean_object* v_i_585_, lean_object* v_bs_586_){
_start:
{
size_t v_sz_boxed_587_; size_t v_i_boxed_588_; lean_object* v_res_589_; 
v_sz_boxed_587_ = lean_unbox_usize(v_sz_584_);
lean_dec(v_sz_584_);
v_i_boxed_588_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(v_sz_boxed_587_, v_i_boxed_588_, v_bs_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(lean_object* v_as_590_, size_t v_sz_591_, size_t v_i_592_, lean_object* v_b_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_lt(v_i_592_, v_sz_591_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_b_593_);
return v___x_602_;
}
else
{
lean_object* v_a_603_; lean_object* v___x_604_; 
v_a_603_ = lean_array_uget_borrowed(v_as_590_, v_i_592_);
v___x_604_ = l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetRecDeclVars(v_a_603_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; size_t v___x_607_; size_t v___x_608_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = l_Array_append___redArg(v_b_593_, v_a_605_);
lean_dec(v_a_605_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_592_, v___x_607_);
v_i_592_ = v___x_608_;
v_b_593_ = v___x_606_;
goto _start;
}
else
{
lean_dec_ref(v_b_593_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2___boxed(lean_object* v_as_610_, lean_object* v_sz_611_, lean_object* v_i_612_, lean_object* v_b_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
size_t v_sz_boxed_621_; size_t v_i_boxed_622_; lean_object* v_res_623_; 
v_sz_boxed_621_ = lean_unbox_usize(v_sz_611_);
lean_dec(v_sz_611_);
v_i_boxed_622_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_res_623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(v_as_610_, v_sz_boxed_621_, v_i_boxed_622_, v_b_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec_ref(v_as_610_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(uint8_t v___x_624_, lean_object* v_as_625_, size_t v_i_626_, size_t v_stop_627_, lean_object* v_b_628_){
_start:
{
lean_object* v___y_630_; uint8_t v___x_634_; 
v___x_634_ = lean_usize_dec_eq(v_i_626_, v_stop_627_);
if (v___x_634_ == 0)
{
lean_object* v_fst_635_; uint8_t v___x_636_; 
v_fst_635_ = lean_ctor_get(v_b_628_, 0);
v___x_636_ = lean_unbox(v_fst_635_);
if (v___x_636_ == 0)
{
lean_object* v_snd_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_snd_637_ = lean_ctor_get(v_b_628_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_b_628_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_b_628_, 0);
lean_dec(v_unused_646_);
v___x_639_ = v_b_628_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_snd_637_);
lean_dec(v_b_628_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_box(v___x_624_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_snd_637_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v___y_630_ = v___x_643_;
goto v___jp_629_;
}
}
}
else
{
lean_object* v_snd_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_657_; 
v_snd_647_ = lean_ctor_get(v_b_628_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_b_628_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_b_628_, 0);
lean_dec(v_unused_658_);
v___x_649_ = v_b_628_;
v_isShared_650_ = v_isSharedCheck_657_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_snd_647_);
lean_dec(v_b_628_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_657_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_651_ = lean_array_uget_borrowed(v_as_625_, v_i_626_);
lean_inc(v___x_651_);
v___x_652_ = lean_array_push(v_snd_647_, v___x_651_);
v___x_653_ = lean_box(v___x_634_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_652_);
lean_ctor_set(v___x_649_, 0, v___x_653_);
v___x_655_ = v___x_649_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_652_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
v___y_630_ = v___x_655_;
goto v___jp_629_;
}
}
}
}
else
{
return v_b_628_;
}
v___jp_629_:
{
size_t v___x_631_; size_t v___x_632_; 
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_626_, v___x_631_);
v_i_626_ = v___x_632_;
v_b_628_ = v___y_630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3___boxed(lean_object* v___x_659_, lean_object* v_as_660_, lean_object* v_i_661_, lean_object* v_stop_662_, lean_object* v_b_663_){
_start:
{
uint8_t v___x_1616__boxed_664_; size_t v_i_boxed_665_; size_t v_stop_boxed_666_; lean_object* v_res_667_; 
v___x_1616__boxed_664_ = lean_unbox(v___x_659_);
v_i_boxed_665_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_stop_boxed_666_ = lean_unbox_usize(v_stop_662_);
lean_dec(v_stop_662_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(v___x_1616__boxed_664_, v_as_660_, v_i_boxed_665_, v_stop_boxed_666_, v_b_663_);
lean_dec_ref(v_as_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetRecDeclsVars(lean_object* v_letRecDecls_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___y_685_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Elab_Do_getLetRecDeclsVars___closed__1));
lean_inc(v_letRecDecls_676_);
v___x_695_ = l_Lean_Syntax_isOfKind(v_letRecDecls_676_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec(v_letRecDecls_676_);
v___x_696_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l_Lean_Syntax_getArg(v_letRecDecls_676_, v___x_697_);
lean_dec(v_letRecDecls_676_);
v___x_699_ = l_Lean_Syntax_getArgs(v___x_698_);
lean_dec(v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Do_getLetRecDeclsVars___closed__2));
v___x_701_ = lean_array_get_size(v___x_699_);
v___x_702_ = lean_nat_dec_lt(v___x_697_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec_ref(v___x_699_);
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; lean_object* v_snd_708_; 
v___x_703_ = lean_box(v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_700_);
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_701_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__3(v___x_695_, v___x_699_, v___x_705_, v___x_706_, v___x_704_);
lean_dec_ref(v___x_699_);
v_snd_708_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_snd_708_);
lean_dec_ref(v___x_707_);
v___y_685_ = v_snd_708_;
goto v___jp_684_;
}
}
v___jp_684_:
{
size_t v_sz_686_; size_t v___x_687_; lean_object* v___x_688_; 
v_sz_686_ = lean_array_size(v___y_685_);
v___x_687_ = ((size_t)0ULL);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__0(v_sz_686_, v___x_687_, v___y_685_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_689_;
}
else
{
lean_object* v_val_690_; lean_object* v_allVars_691_; size_t v_sz_692_; lean_object* v___x_693_; 
v_val_690_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_688_, 1);
v_allVars_691_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v_sz_692_ = lean_array_size(v_val_690_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__2(v_val_690_, v_sz_692_, v___x_687_, v_allVars_691_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_val_690_);
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getLetRecDeclsVars___boxed(lean_object* v_letRecDecls_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_letRecDecls_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(size_t v_sz_718_, size_t v_i_719_, lean_object* v_bs_720_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_719_, v_sz_718_);
if (v___x_721_ == 0)
{
return v_bs_720_;
}
else
{
lean_object* v_v_722_; lean_object* v___x_723_; lean_object* v_bs_x27_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_v_722_ = lean_array_uget(v_bs_720_, v_i_719_);
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_720_, v_i_719_, v___x_723_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_719_, v___x_725_);
v___x_727_ = lean_array_uset(v_bs_x27_724_, v_i_719_, v_v_722_);
v_i_719_ = v___x_726_;
v_bs_720_ = v___x_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2___boxed(lean_object* v_sz_729_, lean_object* v_i_730_, lean_object* v_bs_731_){
_start:
{
size_t v_sz_boxed_732_; size_t v_i_boxed_733_; lean_object* v_res_734_; 
v_sz_boxed_732_ = lean_unbox_usize(v_sz_729_);
lean_dec(v_sz_729_);
v_i_boxed_733_ = lean_unbox_usize(v_i_730_);
lean_dec(v_i_730_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(v_sz_boxed_732_, v_i_boxed_733_, v_bs_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(size_t v_sz_735_, size_t v_i_736_, lean_object* v_bs_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_lt(v_i_736_, v_sz_735_);
if (v___x_738_ == 0)
{
return v_bs_737_;
}
else
{
lean_object* v_v_739_; lean_object* v___x_740_; lean_object* v_bs_x27_741_; size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
v_v_739_ = lean_array_uget(v_bs_737_, v_i_736_);
v___x_740_ = lean_unsigned_to_nat(0u);
v_bs_x27_741_ = lean_array_uset(v_bs_737_, v_i_736_, v___x_740_);
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_736_, v___x_742_);
v___x_744_ = lean_array_uset(v_bs_x27_741_, v_i_736_, v_v_739_);
v_i_736_ = v___x_743_;
v_bs_737_ = v___x_744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0___boxed(lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_bs_748_){
_start:
{
size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v_sz_boxed_749_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_750_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_boxed_749_, v_i_boxed_750_, v_bs_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(lean_object* v_as_752_, size_t v_i_753_, size_t v_stop_754_, lean_object* v_b_755_){
_start:
{
lean_object* v___y_757_; uint8_t v___x_761_; 
v___x_761_ = lean_usize_dec_eq(v_i_753_, v_stop_754_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_array_uget_borrowed(v_as_752_, v_i_753_);
v___x_763_ = l_Lean_Syntax_isIdent(v___x_762_);
if (v___x_763_ == 0)
{
v___y_757_ = v_b_755_;
goto v___jp_756_;
}
else
{
lean_object* v___x_764_; 
lean_inc(v___x_762_);
v___x_764_ = lean_array_push(v_b_755_, v___x_762_);
v___y_757_ = v___x_764_;
goto v___jp_756_;
}
}
else
{
return v_b_755_;
}
v___jp_756_:
{
size_t v___x_758_; size_t v___x_759_; 
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_753_, v___x_758_);
v_i_753_ = v___x_759_;
v_b_755_ = v___y_757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1___boxed(lean_object* v_as_765_, lean_object* v_i_766_, lean_object* v_stop_767_, lean_object* v_b_768_){
_start:
{
size_t v_i_boxed_769_; size_t v_stop_boxed_770_; lean_object* v_res_771_; 
v_i_boxed_769_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_stop_boxed_770_ = lean_unbox_usize(v_stop_767_);
lean_dec(v_stop_767_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_as_765_, v_i_boxed_769_, v_stop_boxed_770_, v_b_768_);
lean_dec_ref(v_as_765_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg(lean_object* v_exprPattern_778_){
_start:
{
lean_object* v___y_781_; lean_object* v___y_787_; size_t v___y_788_; lean_object* v___y_789_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Elab_Do_getExprPatternVarsEx___redArg___closed__1));
lean_inc(v_exprPattern_778_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_exprPattern_778_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v_exprPattern_778_);
v___x_796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v_var_x3f_799_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_832_ = l_Lean_Syntax_getArg(v_exprPattern_778_, v___x_797_);
v___x_833_ = l_Lean_Syntax_isNone(v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_832_);
v___x_835_ = l_Lean_Syntax_matchesNull(v___x_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v___x_832_);
lean_dec(v_exprPattern_778_);
v___x_836_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_836_;
}
else
{
lean_object* v_var_x3f_837_; lean_object* v___x_838_; 
v_var_x3f_837_ = l_Lean_Syntax_getArg(v___x_832_, v___x_797_);
lean_dec(v___x_832_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_var_x3f_837_);
v_var_x3f_799_ = v___x_838_;
goto v___jp_798_;
}
}
else
{
lean_object* v___x_839_; 
lean_dec(v___x_832_);
v___x_839_ = lean_box(0);
v_var_x3f_799_ = v___x_839_;
goto v___jp_798_;
}
v___jp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = l_Lean_Syntax_getArg(v_exprPattern_778_, v___x_800_);
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__12));
v___x_803_ = l_Lean_Syntax_isOfKind(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_var_x3f_799_);
lean_dec(v_exprPattern_778_);
v___x_804_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_getLetRecDeclsVars_spec__1___redArg();
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_pvars_807_; 
v___x_805_ = lean_unsigned_to_nat(2u);
v___x_806_ = l_Lean_Syntax_getArg(v_exprPattern_778_, v___x_805_);
lean_dec(v_exprPattern_778_);
v_pvars_807_ = l_Lean_Syntax_getArgs(v___x_806_);
lean_dec(v___x_806_);
if (lean_obj_tag(v_var_x3f_799_) == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_808_ = lean_array_get_size(v_pvars_807_);
v___x_809_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v___x_810_ = lean_nat_dec_lt(v___x_797_, v___x_808_);
if (v___x_810_ == 0)
{
lean_dec_ref(v_pvars_807_);
v___y_781_ = v___x_809_;
goto v___jp_780_;
}
else
{
uint8_t v___x_811_; 
v___x_811_ = lean_nat_dec_le(v___x_808_, v___x_808_);
if (v___x_811_ == 0)
{
if (v___x_810_ == 0)
{
lean_dec_ref(v_pvars_807_);
v___y_781_ = v___x_809_;
goto v___jp_780_;
}
else
{
size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
v___x_812_ = ((size_t)0ULL);
v___x_813_ = lean_usize_of_nat(v___x_808_);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_807_, v___x_812_, v___x_813_, v___x_809_);
lean_dec_ref(v_pvars_807_);
v___y_781_ = v___x_814_;
goto v___jp_780_;
}
}
else
{
size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; 
v___x_815_ = ((size_t)0ULL);
v___x_816_ = lean_usize_of_nat(v___x_808_);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_807_, v___x_815_, v___x_816_, v___x_809_);
lean_dec_ref(v_pvars_807_);
v___y_781_ = v___x_817_;
goto v___jp_780_;
}
}
}
else
{
lean_object* v_val_818_; lean_object* v___x_819_; lean_object* v___x_820_; size_t v_sz_821_; size_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_val_818_ = lean_ctor_get(v_var_x3f_799_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v_var_x3f_799_, 1);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_800_);
v___x_820_ = lean_array_push(v___x_819_, v_val_818_);
v_sz_821_ = lean_array_size(v___x_820_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__2(v_sz_821_, v___x_822_, v___x_820_);
v___x_824_ = lean_array_get_size(v_pvars_807_);
v___x_825_ = ((lean_object*)(l___private_Lean_Elab_Do_PatternVar_0__Lean_Elab_Do_getLetIdVars___closed__15));
v___x_826_ = lean_nat_dec_lt(v___x_797_, v___x_824_);
if (v___x_826_ == 0)
{
lean_dec_ref(v_pvars_807_);
v___y_787_ = v___x_823_;
v___y_788_ = v___x_822_;
v___y_789_ = v___x_825_;
goto v___jp_786_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_le(v___x_824_, v___x_824_);
if (v___x_827_ == 0)
{
if (v___x_826_ == 0)
{
lean_dec_ref(v_pvars_807_);
v___y_787_ = v___x_823_;
v___y_788_ = v___x_822_;
v___y_789_ = v___x_825_;
goto v___jp_786_;
}
else
{
size_t v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_usize_of_nat(v___x_824_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_807_, v___x_822_, v___x_828_, v___x_825_);
lean_dec_ref(v_pvars_807_);
v___y_787_ = v___x_823_;
v___y_788_ = v___x_822_;
v___y_789_ = v___x_829_;
goto v___jp_786_;
}
}
else
{
size_t v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_usize_of_nat(v___x_824_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__1(v_pvars_807_, v___x_822_, v___x_830_, v___x_825_);
lean_dec_ref(v_pvars_807_);
v___y_787_ = v___x_823_;
v___y_788_ = v___x_822_;
v___y_789_ = v___x_831_;
goto v___jp_786_;
}
}
}
}
}
}
v___jp_780_:
{
size_t v_sz_782_; size_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_sz_782_ = lean_array_size(v___y_781_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_782_, v___x_783_, v___y_781_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
v___jp_786_:
{
lean_object* v___x_790_; size_t v_sz_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_790_ = l_Array_append___redArg(v___y_787_, v___y_789_);
lean_dec_ref(v___y_789_);
v_sz_791_ = lean_array_size(v___x_790_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_getExprPatternVarsEx_spec__0(v_sz_791_, v___y_788_, v___x_790_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___redArg___boxed(lean_object* v_exprPattern_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_exprPattern_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx(lean_object* v_exprPattern_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_exprPattern_843_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getExprPatternVarsEx___boxed(lean_object* v_exprPattern_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Elab_Do_getExprPatternVarsEx(v_exprPattern_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_860_;
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
