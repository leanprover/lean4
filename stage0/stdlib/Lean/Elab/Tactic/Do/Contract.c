// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Contract
// Imports: public import Std.Tactic.Do.Syntax public import Std.WP public import Lean.Elab.Util public import Lean.Elab.Do.Basic import Lean.DocString.Extension meta import Lean.Parser.Command meta import Lean.Parser.Term meta import Lean.Parser.Do import Init.Syntax import Init.Grind.Interactive
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPUnit___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declValEqns"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(185, 66, 113, 88, 174, 230, 155, 36)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 105, 220, 149, 84, 64, 243, 129)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value),((lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "duplicate `spec` section"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 79, 35, 19, 21, 38, 89, 10)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 8, 226, 43, 107, 167, 95, 157)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__4_value),LEAN_SCALAR_PTR_LITERAL(55, 166, 237, 23, 37, 47, 5, 133)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Std.WP"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_expandDefContract___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Lean.Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_expandDefContract___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__11_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__12_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__15_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__17_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_expandDefContract___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__19;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__20_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__23_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__25_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__27_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__28_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__29_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__31 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__31_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__32 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__33 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__33_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__34 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__35 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__35_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__36 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__37 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__37_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tripleNotation"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__38 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__38_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__39 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__39_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__40 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__40_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__41 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__41_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__42 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__43 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__43_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__44 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__44_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__45 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__46 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__46_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__47 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__48 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__48_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__49 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__50 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__50_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__51 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__52 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__52_value),LEAN_SCALAR_PTR_LITERAL(75, 196, 10, 243, 239, 189, 222, 13)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__53 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__54 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__54_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__54_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__55 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__56 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__56_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__57 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__57_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__58 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__59 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__59_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "vcgenDischargeGrind"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__60 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value),LEAN_SCALAR_PTR_LITERAL(7, 199, 17, 154, 227, 108, 8, 170)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__61 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__62 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__63 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 107, 245, 63, 193, 1, 88)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__64 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__65 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__66 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__66_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__67 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__68 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__68_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__68_value),LEAN_SCALAR_PTR_LITERAL(35, 114, 22, 139, 17, 175, 241, 184)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__69 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__70 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__70_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__70_value),LEAN_SCALAR_PTR_LITERAL(197, 239, 5, 217, 230, 199, 187, 87)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__71 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindTry_"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__72 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value),LEAN_SCALAR_PTR_LITERAL(39, 12, 37, 83, 85, 34, 35, 178)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__73 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__74 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__74_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finish"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__75 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value),LEAN_SCALAR_PTR_LITERAL(1, 141, 128, 132, 58, 161, 38, 215)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__76 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__77 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__78 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__78_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__78_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__79 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__79_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__80 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__80_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__80_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__81 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__81_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__82 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__82_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__83 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__83_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__83_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__84 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__84_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fail"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__85 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__85_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__85_value),LEAN_SCALAR_PTR_LITERAL(251, 214, 242, 89, 226, 36, 213, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__86 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__86_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__87 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__87_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__88 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__88_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__87_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__88_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__89 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__89_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__90 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__90_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__90_value),LEAN_SCALAR_PTR_LITERAL(244, 42, 145, 170, 145, 147, 228, 105)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__91 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__91_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__92 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__92_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "unproved verification conditions for the contract of `"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__93 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__93_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "`; discharge them in a `where finally | spec => ...` section of the definition"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__94 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__94_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`; the `where finally | spec => ...` section does not discharge them"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__95 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__95_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ensuresClause"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__96 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__96_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__96_value),LEAN_SCALAR_PTR_LITERAL(80, 249, 216, 241, 199, 195, 198, 237)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__97 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__97_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__98 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__98_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__98_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__99 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__99_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__100 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__100_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__100_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__101 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__101_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__102 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__102_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__102_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__103 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__103_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__104 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__104_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__104_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__105 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__105_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__106 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__106_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__107 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__107_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term⊤"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__108 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__108_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__109_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__109_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__11_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__109_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__108_value),LEAN_SCALAR_PTR_LITERAL(137, 158, 127, 165, 41, 148, 243, 67)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__109 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__109_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊤"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__110 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__110_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "requiresClause"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__111 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__111_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__111_value),LEAN_SCALAR_PTR_LITERAL(132, 130, 91, 181, 57, 218, 183, 96)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__112 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__112_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 117, .m_capacity = 117, .m_length = 116, .m_data = "`requires`/`ensures` contracts elaborate to a `vcgen`-proved specification theorem; add `import Std.WP` to use them."};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__113 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__113_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__114 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__114_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__115 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__115_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__116 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__116_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__117_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__114_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__117_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__117_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__115_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__117_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__116_value),LEAN_SCALAR_PTR_LITERAL(202, 119, 227, 254, 29, 206, 25, 24)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__117 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__117_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "contractDeclVal"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__118 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__118_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__118_value),LEAN_SCALAR_PTR_LITERAL(192, 214, 40, 194, 192, 243, 241, 169)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__119 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__120 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__120_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__120_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__121 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__121_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "expandDefContract"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 255, 251, 159, 111, 208, 249)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 297, .m_capacity = 297, .m_length = 288, .m_data = "Expand a `def` carrying `requires`/`ensures` clauses into the plain `def` plus a spec theorem\n`@[spec] theorem f.spec : ⦃P⦄ f args ⦃fun b => Q⦄` proved by `vcgen`. A\n`where finally | spec => steps` section supplies `grind`-mode steps for the verification\nconditions `finish` leaves open. "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Gadget"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "assertGadget"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__114_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__115_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 124, 11, 88, 114, 168, 194, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "the `assert` element elaborates to a `vcgen` gadget; add `import Std.WP` to use it."};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabDoAssertion"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 130, 201, 151, 146, 48, 207, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___y_6_; uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_12_ = l_Lean_Syntax_isIdent(v___x_11_);
if (v___x_12_ == 0)
{
v___y_6_ = v_b_4_;
goto v___jp_5_;
}
else
{
lean_object* v___x_13_; 
lean_inc(v___x_11_);
v___x_13_ = lean_array_push(v_b_4_, v___x_11_);
v___y_6_ = v___x_13_;
goto v___jp_5_;
}
}
else
{
return v_b_4_;
}
v___jp_5_:
{
size_t v___x_7_; size_t v___x_8_; 
v___x_7_ = ((size_t)1ULL);
v___x_8_ = lean_usize_add(v_i_2_, v___x_7_);
v_i_2_ = v___x_8_;
v_b_4_ = v___y_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0___boxed(lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_, lean_object* v_b_17_){
_start:
{
size_t v_i_boxed_18_; size_t v_stop_boxed_19_; lean_object* v_res_20_; 
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_19_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_14_, v_i_boxed_18_, v_stop_boxed_19_, v_b_17_);
lean_dec_ref(v_as_14_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(lean_object* v_as_23_, lean_object* v_start_24_, lean_object* v_stop_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
v___x_27_ = lean_nat_dec_lt(v_start_24_, v_stop_25_);
if (v___x_27_ == 0)
{
return v___x_26_;
}
else
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_array_get_size(v_as_23_);
v___x_29_ = lean_nat_dec_le(v_stop_25_, v___x_28_);
if (v___x_29_ == 0)
{
uint8_t v___x_30_; 
v___x_30_ = lean_nat_dec_lt(v_start_24_, v___x_28_);
if (v___x_30_ == 0)
{
return v___x_26_;
}
else
{
size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_usize_of_nat(v_start_24_);
v___x_32_ = lean_usize_of_nat(v___x_28_);
v___x_33_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_23_, v___x_31_, v___x_32_, v___x_26_);
return v___x_33_;
}
}
else
{
size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_usize_of_nat(v_start_24_);
v___x_35_ = lean_usize_of_nat(v_stop_25_);
v___x_36_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_23_, v___x_34_, v___x_35_, v___x_26_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___boxed(lean_object* v_as_37_, lean_object* v_start_38_, lean_object* v_stop_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(v_as_37_, v_start_38_, v_stop_39_);
lean_dec(v_stop_39_);
lean_dec(v_start_38_);
lean_dec_ref(v_as_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents(lean_object* v_binder_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4));
lean_inc(v_binder_50_);
v___x_52_ = l_Lean_Syntax_isOfKind(v_binder_50_, v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
v___x_53_ = l_Lean_Syntax_isIdent(v_binder_50_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec(v_binder_50_);
v___x_54_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_55_);
v___x_57_ = lean_array_push(v___x_56_, v_binder_50_);
return v___x_57_;
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = l_Lean_Syntax_getArg(v_binder_50_, v___x_59_);
v___x_65_ = lean_unsigned_to_nat(2u);
v___x_66_ = l_Lean_Syntax_getArg(v_binder_50_, v___x_65_);
v___x_67_ = l_Lean_Syntax_isNone(v___x_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = l_Lean_Syntax_matchesNull(v___x_66_, v___x_65_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
lean_dec(v___x_60_);
v___x_69_ = l_Lean_Syntax_isIdent(v_binder_50_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec(v_binder_50_);
v___x_70_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_72_ = lean_array_push(v___x_71_, v_binder_50_);
return v___x_72_;
}
}
else
{
lean_dec(v_binder_50_);
goto v___jp_61_;
}
}
else
{
lean_dec(v___x_66_);
lean_dec(v_binder_50_);
goto v___jp_61_;
}
v___jp_61_:
{
lean_object* v_ids_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_ids_62_ = l_Lean_Syntax_getArgs(v___x_60_);
lean_dec(v___x_60_);
v___x_63_ = lean_array_get_size(v_ids_62_);
v___x_64_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(v_ids_62_, v___x_58_, v___x_63_);
lean_dec_ref(v_ids_62_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(lean_object* v_v_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2));
lean_inc(v_v_107_);
v___x_109_ = l_Lean_Syntax_isOfKind(v_v_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4));
lean_inc(v_v_107_);
v___x_111_ = l_Lean_Syntax_isOfKind(v_v_107_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6));
v___x_113_ = l_Lean_Syntax_isOfKind(v_v_107_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9));
return v___x_115_;
}
}
else
{
lean_object* v___x_116_; 
lean_dec(v_v_107_);
v___x_116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10));
return v___x_116_;
}
}
else
{
lean_object* v___x_117_; 
lean_dec(v_v_107_);
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12));
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(lean_object* v_s_118_, lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
return v_s_118_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_122_; 
v_head_120_ = lean_ctor_get(v_x_119_, 0);
v_tail_121_ = lean_ctor_get(v_x_119_, 1);
v___x_122_ = l_Lean_Syntax_getArg(v_s_118_, v_head_120_);
lean_dec(v_s_118_);
v_s_118_ = v___x_122_;
v_x_119_ = v_tail_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath___boxed(lean_object* v_s_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(v_s_124_, v_x_125_);
lean_dec(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(lean_object* v_s_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_dec(v_s_127_);
lean_inc(v_x_129_);
return v_x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_head_130_ = lean_ctor_get(v_x_128_, 0);
v_tail_131_ = lean_ctor_get(v_x_128_, 1);
v___x_132_ = l_Lean_Syntax_getArg(v_s_127_, v_head_130_);
v___x_133_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v___x_132_, v_tail_131_, v_x_129_);
v___x_134_ = l_Lean_Syntax_setArg(v_s_127_, v_head_130_, v___x_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath___boxed(lean_object* v_s_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v_s_135_, v_x_136_, v_x_137_);
lean_dec(v_x_137_);
lean_dec(v_x_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(lean_object* v_as_142_, size_t v_sz_143_, size_t v_i_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_a_147_; uint8_t v___x_151_; 
v___x_151_ = lean_usize_dec_lt(v_i_144_, v_sz_143_);
if (v___x_151_ == 0)
{
return v_b_145_;
}
else
{
lean_object* v_fst_152_; lean_object* v_snd_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_172_; 
v_fst_152_ = lean_ctor_get(v_b_145_, 0);
v_snd_153_ = lean_ctor_get(v_b_145_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_b_145_);
if (v_isSharedCheck_172_ == 0)
{
v___x_155_ = v_b_145_;
v_isShared_156_ = v_isSharedCheck_172_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_snd_153_);
lean_inc(v_fst_152_);
lean_dec(v_b_145_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_172_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_a_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_a_157_ = lean_array_uget_borrowed(v_as_142_, v_i_144_);
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = l_Lean_Syntax_getArg(v_a_157_, v___x_158_);
v___x_160_ = l_Lean_Syntax_getId(v___x_159_);
lean_dec(v___x_159_);
v___x_161_ = l_Lean_Name_eraseMacroScopes(v___x_160_);
lean_dec(v___x_160_);
v___x_162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
v___x_163_ = lean_name_eq(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_inc(v_a_157_);
v___x_164_ = lean_array_push(v_snd_153_, v_a_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_164_);
v___x_166_ = v___x_155_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_fst_152_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v_a_147_ = v___x_166_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_inc(v_a_157_);
v___x_168_ = lean_array_push(v_fst_152_, v_a_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_168_);
v___x_170_ = v___x_155_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_snd_153_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
v_a_147_ = v___x_170_;
goto v___jp_146_;
}
}
}
}
v___jp_146_:
{
size_t v___x_148_; size_t v___x_149_; 
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_144_, v___x_148_);
v_i_144_ = v___x_149_;
v_b_145_ = v_a_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___boxed(lean_object* v_as_173_, lean_object* v_sz_174_, lean_object* v_i_175_, lean_object* v_b_176_){
_start:
{
size_t v_sz_boxed_177_; size_t v_i_boxed_178_; lean_object* v_res_179_; 
v_sz_boxed_177_ = lean_unbox_usize(v_sz_174_);
lean_dec(v_sz_174_);
v_i_boxed_178_ = lean_unbox_usize(v_i_175_);
lean_dec(v_i_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(v_as_173_, v_sz_boxed_177_, v_i_boxed_178_, v_b_176_);
lean_dec_ref(v_as_173_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(lean_object* v_v_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; 
lean_inc(v_v_186_);
v___x_189_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(v_v_186_);
if (lean_obj_tag(v___x_189_) == 1)
{
lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_265_; 
v_val_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_265_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_265_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_265_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_optWd_194_; uint8_t v___x_195_; 
lean_inc(v_v_186_);
v_optWd_194_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(v_v_186_, v_val_190_);
v___x_195_ = l_Lean_Syntax_isNone(v_optWd_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v_wd_197_; lean_object* v___x_198_; lean_object* v_optWf_199_; uint8_t v___x_200_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v_wd_197_ = l_Lean_Syntax_getArg(v_optWd_194_, v___x_196_);
lean_dec(v_optWd_194_);
v___x_198_ = lean_unsigned_to_nat(2u);
v_optWf_199_ = l_Lean_Syntax_getArg(v_wd_197_, v___x_198_);
v___x_200_ = l_Lean_Syntax_isNone(v_optWf_199_);
if (v___x_200_ == 0)
{
lean_object* v_wf_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; size_t v_sz_205_; size_t v___x_206_; lean_object* v___x_207_; lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_258_; 
v_wf_201_ = l_Lean_Syntax_getArg(v_optWf_199_, v___x_196_);
lean_dec(v_optWf_199_);
v___x_202_ = l_Lean_Syntax_getArg(v_wf_201_, v___x_198_);
v___x_203_ = l_Lean_Syntax_getArgs(v___x_202_);
lean_dec(v___x_202_);
v___x_204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0));
v_sz_205_ = lean_array_size(v___x_203_);
v___x_206_ = ((size_t)0ULL);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(v___x_203_, v_sz_205_, v___x_206_, v___x_204_);
lean_dec_ref(v___x_203_);
v_fst_208_ = lean_ctor_get(v___x_207_, 0);
v_snd_209_ = lean_ctor_get(v___x_207_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_258_ == 0)
{
v___x_211_ = v___x_207_;
v_isShared_212_ = v_isSharedCheck_258_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_snd_209_);
lean_inc(v_fst_208_);
lean_dec(v___x_207_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_258_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___y_214_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_array_get_size(v_fst_208_);
v___x_239_ = lean_nat_dec_eq(v___x_238_, v___x_196_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_dec_lt(v___x_240_, v___x_238_);
if (v___x_241_ == 0)
{
v___y_214_ = v_a_188_;
goto v___jp_213_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_array_fget_borrowed(v_fst_208_, v___x_240_);
v___x_243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3));
v___x_244_ = l_Lean_Macro_throwErrorAt___redArg(v___x_242_, v___x_243_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; 
v_a_245_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 2);
v___y_214_ = v_a_245_;
goto v___jp_213_;
}
else
{
lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_del_object(v___x_211_);
lean_dec(v_snd_209_);
lean_dec(v_fst_208_);
lean_dec(v_wf_201_);
lean_dec(v_wd_197_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
lean_dec(v_v_186_);
v_a_246_ = lean_ctor_get(v___x_244_, 0);
v_a_247_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_244_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_inc(v_a_246_);
lean_dec(v___x_244_);
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
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_del_object(v___x_211_);
lean_dec(v_snd_209_);
lean_dec(v_fst_208_);
lean_dec(v_wf_201_);
lean_dec(v_wd_197_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_v_186_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_a_188_);
return v___x_257_;
}
v___jp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_wf_x27_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_216_ = lean_box(2);
v___x_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
lean_ctor_set(v___x_217_, 2, v_snd_209_);
v_wf_x27_218_ = l_Lean_Syntax_setArg(v_wf_201_, v___x_198_, v___x_217_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_array_get(v___x_219_, v_fst_208_, v___x_196_);
lean_dec(v_fst_208_);
v___x_221_ = lean_unsigned_to_nat(3u);
v___x_222_ = l_Lean_Syntax_getArg(v___x_220_, v___x_221_);
lean_dec(v___x_220_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_222_);
v___x_224_ = v___x_192_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_237_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_mk_empty_array_with_capacity(v___x_225_);
lean_inc_ref(v___x_226_);
v___x_227_ = lean_array_push(v___x_226_, v_wf_x27_218_);
v___x_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_228_, 0, v___x_216_);
lean_ctor_set(v___x_228_, 1, v___x_215_);
lean_ctor_set(v___x_228_, 2, v___x_227_);
v___x_229_ = l_Lean_Syntax_setArg(v_wd_197_, v___x_198_, v___x_228_);
v___x_230_ = lean_array_push(v___x_226_, v___x_229_);
v___x_231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_216_);
lean_ctor_set(v___x_231_, 1, v___x_215_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
v___x_232_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v_v_186_, v_val_190_, v___x_231_);
lean_dec_ref_known(v___x_231_, 3);
lean_dec(v_val_190_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___x_232_);
lean_ctor_set(v___x_211_, 0, v___x_224_);
v___x_234_ = v___x_211_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_232_);
v___x_234_ = v_reuseFailAlloc_236_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___y_214_);
return v___x_235_;
}
}
}
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_optWf_199_);
lean_dec(v_wd_197_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_v_186_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_188_);
return v___x_261_;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v_optWd_194_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_v_186_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_a_188_);
return v___x_264_;
}
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___x_189_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_v_186_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_188_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___boxed(lean_object* v_v_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v_v_269_, v_a_270_, v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(size_t v_sz_273_, size_t v_i_274_, lean_object* v_bs_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_lt(v_i_274_, v_sz_273_);
if (v___x_276_ == 0)
{
return v_bs_275_;
}
else
{
lean_object* v_v_277_; lean_object* v___x_278_; lean_object* v_bs_x27_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v_v_277_ = lean_array_uget(v_bs_275_, v_i_274_);
v___x_278_ = lean_unsigned_to_nat(0u);
v_bs_x27_279_ = lean_array_uset(v_bs_275_, v_i_274_, v___x_278_);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_274_, v___x_280_);
v___x_282_ = lean_array_uset(v_bs_x27_279_, v_i_274_, v_v_277_);
v_i_274_ = v___x_281_;
v_bs_275_ = v___x_282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0___boxed(lean_object* v_sz_284_, lean_object* v_i_285_, lean_object* v_bs_286_){
_start:
{
size_t v_sz_boxed_287_; size_t v_i_boxed_288_; lean_object* v_res_289_; 
v_sz_boxed_287_ = lean_unbox_usize(v_sz_284_);
lean_dec(v_sz_284_);
v_i_boxed_288_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_res_289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_boxed_287_, v_i_boxed_288_, v_bs_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(lean_object* v_as_290_, size_t v_i_291_, size_t v_stop_292_, lean_object* v_b_293_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_eq(v_i_291_, v_stop_292_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; size_t v___x_298_; size_t v___x_299_; 
v___x_295_ = lean_array_uget_borrowed(v_as_290_, v_i_291_);
lean_inc(v___x_295_);
v___x_296_ = l_Lean_Elab_Tactic_Do_contractBinderIdents(v___x_295_);
v___x_297_ = l_Array_append___redArg(v_b_293_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_add(v_i_291_, v___x_298_);
v_i_291_ = v___x_299_;
v_b_293_ = v___x_297_;
goto _start;
}
else
{
return v_b_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___boxed(lean_object* v_as_301_, lean_object* v_i_302_, lean_object* v_stop_303_, lean_object* v_b_304_){
_start:
{
size_t v_i_boxed_305_; size_t v_stop_boxed_306_; lean_object* v_res_307_; 
v_i_boxed_305_ = lean_unbox_usize(v_i_302_);
lean_dec(v_i_302_);
v_stop_boxed_306_ = lean_unbox_usize(v_stop_303_);
lean_dec(v_stop_303_);
v_res_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v_as_301_, v_i_boxed_305_, v_stop_boxed_306_, v_b_304_);
lean_dec_ref(v_as_301_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(size_t v_sz_308_, size_t v_i_309_, lean_object* v_bs_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_lt(v_i_309_, v_sz_308_);
if (v___x_311_ == 0)
{
return v_bs_310_;
}
else
{
lean_object* v_v_312_; lean_object* v___x_313_; lean_object* v_bs_x27_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v_v_312_ = lean_array_uget(v_bs_310_, v_i_309_);
v___x_313_ = lean_unsigned_to_nat(0u);
v_bs_x27_314_ = lean_array_uset(v_bs_310_, v_i_309_, v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_309_, v___x_315_);
v___x_317_ = lean_array_uset(v_bs_x27_314_, v_i_309_, v_v_312_);
v_i_309_ = v___x_316_;
v_bs_310_ = v___x_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1___boxed(lean_object* v_sz_319_, lean_object* v_i_320_, lean_object* v_bs_321_){
_start:
{
size_t v_sz_boxed_322_; size_t v_i_boxed_323_; lean_object* v_res_324_; 
v_sz_boxed_322_ = lean_unbox_usize(v_sz_319_);
lean_dec(v_sz_319_);
v_i_boxed_323_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_boxed_322_, v_i_boxed_323_, v_bs_321_);
return v_res_324_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__8(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__7));
v___x_346_ = l_String_toRawSubstring_x27(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__10(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__9));
v___x_349_ = l_String_toRawSubstring_x27(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__19(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Array_mkArray0(lean_box(0));
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract(lean_object* v_stx_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; uint8_t v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; size_t v___y_645_; lean_object* v___y_646_; lean_object* v_specTac_647_; lean_object* v_quotContext_648_; lean_object* v_currMacroScope_649_; lean_object* v_ref_650_; lean_object* v___y_651_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; uint8_t v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; size_t v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; uint8_t v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; size_t v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v_post_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___x_892_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; uint8_t v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; size_t v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v_pre_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; uint8_t v___y_983_; lean_object* v___y_984_; uint8_t v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; size_t v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v_decl_1029_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; lean_object* v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; uint8_t v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; uint8_t v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_892_ = lean_unsigned_to_nat(1u);
v_decl_1029_ = l_Lean_Syntax_getArg(v_stx_627_, v___x_892_);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__121));
lean_inc(v_decl_1029_);
v___x_1168_ = l_Lean_Syntax_isOfKind(v_decl_1029_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Macro_throwUnsupported___redArg(v_a_629_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 1);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 2);
v___y_1150_ = v_a_628_;
v___y_1151_ = v_a_1170_;
goto v___jp_1149_;
}
else
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_decl_1029_);
lean_dec(v_stx_627_);
v_a_1171_ = lean_ctor_get(v___x_1169_, 0);
v_a_1172_ = lean_ctor_get(v___x_1169_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1169_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1171_);
lean_dec(v___x_1169_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
v___y_1150_ = v_a_628_;
v___y_1151_ = v_a_629_;
goto v___jp_1149_;
}
v___jp_630_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; size_t v_sz_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_652_ = l_Lean_SourceInfo_fromRef(v_ref_650_, v___y_635_);
v___x_653_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0));
v___x_654_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1));
v___x_655_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
v___x_656_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__2));
v___x_658_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
lean_inc_n(v___x_652_, 81);
v___x_659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_652_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
v___x_660_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__5));
v___x_661_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__6));
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_652_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_664_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__8, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__8_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__8);
lean_inc_ref_n(v___y_637_, 2);
lean_inc_ref_n(v___y_634_, 2);
v___x_665_ = l_Lean_Name_mkStr2(v___y_634_, v___y_637_);
lean_inc_n(v_currMacroScope_649_, 2);
lean_inc(v___x_665_);
lean_inc_n(v_quotContext_648_, 2);
v___x_666_ = l_Lean_addMacroScope(v_quotContext_648_, v___x_665_, v_currMacroScope_649_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_670_, 0, v___x_652_);
lean_ctor_set(v___x_670_, 1, v___x_664_);
lean_ctor_set(v___x_670_, 2, v___x_666_);
lean_ctor_set(v___x_670_, 3, v___x_669_);
v___x_671_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__10, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__10_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__10);
v___x_672_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__12));
v___x_673_ = l_Lean_addMacroScope(v_quotContext_648_, v___x_672_, v_currMacroScope_649_);
v___x_674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__14));
v___x_675_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_675_, 0, v___x_652_);
lean_ctor_set(v___x_675_, 1, v___x_671_);
lean_ctor_set(v___x_675_, 2, v___x_673_);
lean_ctor_set(v___x_675_, 3, v___x_674_);
v___x_676_ = l_Lean_Syntax_node2(v___x_652_, v___x_663_, v___x_670_, v___x_675_);
v___x_677_ = l_Lean_Syntax_node2(v___x_652_, v___x_660_, v___x_662_, v___x_676_);
v___x_678_ = l_Lean_Syntax_node2(v___x_652_, v___x_658_, v___x_659_, v___x_677_);
v___x_679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_652_);
lean_ctor_set(v___x_679_, 1, v___x_655_);
v___x_680_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_681_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__18));
v___x_682_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__19, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__19_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__19);
v___x_683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_683_, 0, v___x_652_);
lean_ctor_set(v___x_683_, 1, v___x_663_);
lean_ctor_set(v___x_683_, 2, v___x_682_);
v___x_684_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__21));
v___x_685_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__22));
v___x_686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_652_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__24));
v___x_688_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__26));
lean_inc_ref_n(v___x_683_, 25);
v___x_689_ = l_Lean_Syntax_node1(v___x_652_, v___x_688_, v___x_683_);
v___x_690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__27));
lean_inc_ref_n(v___y_646_, 2);
v___x_691_ = l_Lean_Name_mkStr4(v___x_653_, v___x_654_, v___x_690_, v___y_646_);
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_652_);
lean_ctor_set(v___x_692_, 1, v___y_646_);
v___x_693_ = l_Lean_Syntax_node2(v___x_652_, v___x_691_, v___x_692_, v___x_683_);
v___x_694_ = l_Lean_Syntax_node2(v___x_652_, v___x_687_, v___x_689_, v___x_693_);
v___x_695_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___x_694_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__28));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_652_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
lean_inc_ref(v___x_697_);
v___x_698_ = l_Lean_Syntax_node3(v___x_652_, v___x_684_, v___x_686_, v___x_695_, v___x_697_);
v___x_699_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___x_698_);
v___x_700_ = l_Lean_Syntax_node7(v___x_652_, v___x_681_, v___x_683_, v___x_699_, v___x_683_, v___x_683_, v___x_683_, v___x_683_, v___x_683_);
v___x_701_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__29));
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__30));
v___x_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_652_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__32));
v___x_705_ = lean_mk_empty_array_with_capacity(v___y_639_);
lean_inc_n(v___y_638_, 2);
v___x_706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_706_, 0, v___y_638_);
lean_ctor_set(v___x_706_, 1, v___x_663_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
v___x_707_ = lean_mk_empty_array_with_capacity(v___y_636_);
lean_inc_ref(v___x_707_);
v___x_708_ = lean_array_push(v___x_707_, v___y_643_);
v___x_709_ = lean_array_push(v___x_708_, v___x_706_);
v___x_710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_710_, 0, v___y_638_);
lean_ctor_set(v___x_710_, 1, v___x_704_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__34));
v___x_712_ = l_Array_append___redArg(v___x_682_, v___y_641_);
lean_dec_ref(v___y_641_);
v___x_713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_713_, 0, v___x_652_);
lean_ctor_set(v___x_713_, 1, v___x_663_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__36));
v___x_715_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__37));
v___x_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_652_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__38));
v___x_718_ = l_Lean_Name_mkStr3(v___y_634_, v___y_637_, v___x_717_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__39));
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_652_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__40));
v___x_722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_652_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v_sz_724_ = lean_array_size(v___y_633_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_724_, v___y_645_, v___y_633_);
v___x_726_ = l_Array_append___redArg(v___x_682_, v___x_725_);
lean_dec_ref(v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_727_, 0, v___x_652_);
lean_ctor_set(v___x_727_, 1, v___x_663_);
lean_ctor_set(v___x_727_, 2, v___x_726_);
lean_inc(v___y_642_);
v___x_728_ = l_Lean_Syntax_node2(v___x_652_, v___x_723_, v___y_642_, v___x_727_);
lean_inc_ref(v___x_722_);
lean_inc_ref(v___x_720_);
v___x_729_ = l_Lean_Syntax_node8(v___x_652_, v___x_718_, v___x_720_, v___y_640_, v___x_722_, v___x_683_, v___x_728_, v___x_720_, v___y_644_, v___x_722_);
v___x_730_ = l_Lean_Syntax_node2(v___x_652_, v___x_714_, v___x_716_, v___x_729_);
v___x_731_ = l_Lean_Syntax_node2(v___x_652_, v___x_711_, v___x_713_, v___x_730_);
v___x_732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2));
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__43));
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_652_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__45));
v___x_736_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__46));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_652_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__49));
v___x_739_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__51));
v___x_740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__52));
v___x_741_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__53));
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_652_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_744_ = l_Lean_Syntax_node1(v___x_652_, v___x_743_, v___x_683_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__56));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_652_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__58));
v___x_748_ = l_Lean_Syntax_node3(v___x_652_, v___x_747_, v___x_683_, v___x_683_, v___y_642_);
v___x_749_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___x_748_);
v___x_750_ = l_Lean_Syntax_node3(v___x_652_, v___x_663_, v___x_746_, v___x_749_, v___x_697_);
v___x_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__59));
v___x_752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_652_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__61));
v___x_754_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__64));
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__65));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_652_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__67));
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_759_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__71));
v___x_760_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__73));
v___x_761_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__74));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_652_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__75));
v___x_764_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__76));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_652_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
v___x_766_ = l_Lean_Syntax_node4(v___x_652_, v___x_764_, v___x_765_, v___x_683_, v___x_683_, v___x_683_);
v___x_767_ = l_Lean_Syntax_node2(v___x_652_, v___x_759_, v___x_766_, v___x_683_);
v___x_768_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___x_767_);
v___x_769_ = l_Lean_Syntax_node1(v___x_652_, v___x_758_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v___x_652_, v___x_757_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node2(v___x_652_, v___x_760_, v___x_762_, v___x_770_);
v___x_772_ = l_Lean_Syntax_node2(v___x_652_, v___x_759_, v___x_771_, v___x_683_);
v___x_773_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node1(v___x_652_, v___x_758_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node1(v___x_652_, v___x_757_, v___x_774_);
v___x_776_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__77));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_652_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_Syntax_node3(v___x_652_, v___x_754_, v___x_756_, v___x_775_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v___x_652_, v___x_753_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node2(v___x_652_, v___x_663_, v___x_752_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node8(v___x_652_, v___x_741_, v___x_742_, v___x_744_, v___x_750_, v___x_683_, v___x_683_, v___x_683_, v___x_683_, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__78));
v___x_783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__79));
v___x_784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_652_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
v___x_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__81));
v___x_786_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__82));
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_652_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__83));
v___x_789_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__84));
v___x_790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_652_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
v___x_791_ = l_Lean_Syntax_node1(v___x_652_, v___x_789_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v___x_652_, v___x_739_, v___x_792_);
v___x_794_ = l_Lean_Syntax_node1(v___x_652_, v___x_738_, v___x_793_);
lean_inc_ref(v___x_787_);
v___x_795_ = l_Lean_Syntax_node2(v___x_652_, v___x_785_, v___x_787_, v___x_794_);
v___x_796_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__85));
v___x_797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__86));
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_652_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
v___x_799_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___y_632_);
v___x_800_ = l_Lean_Syntax_node2(v___x_652_, v___x_797_, v___x_798_, v___x_799_);
v___x_801_ = l_Lean_Syntax_node1(v___x_652_, v___x_663_, v___x_800_);
v___x_802_ = l_Lean_Syntax_node1(v___x_652_, v___x_739_, v___x_801_);
v___x_803_ = l_Lean_Syntax_node1(v___x_652_, v___x_738_, v___x_802_);
v___x_804_ = l_Lean_Syntax_node2(v___x_652_, v___x_785_, v___x_787_, v___x_803_);
v___x_805_ = l_Lean_Syntax_node2(v___x_652_, v___x_663_, v___x_795_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node2(v___x_652_, v___x_783_, v___x_784_, v___x_805_);
v___x_807_ = l_Lean_Syntax_node5(v___x_652_, v___x_663_, v___x_781_, v___x_683_, v_specTac_647_, v___x_683_, v___x_806_);
v___x_808_ = l_Lean_Syntax_node1(v___x_652_, v___x_739_, v___x_807_);
v___x_809_ = l_Lean_Syntax_node1(v___x_652_, v___x_738_, v___x_808_);
v___x_810_ = l_Lean_Syntax_node2(v___x_652_, v___x_735_, v___x_737_, v___x_809_);
v___x_811_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__89));
v___x_812_ = l_Lean_Syntax_node2(v___x_652_, v___x_811_, v___x_683_, v___x_683_);
v___x_813_ = l_Lean_Syntax_node4(v___x_652_, v___x_732_, v___x_734_, v___x_810_, v___x_812_, v___x_683_);
v___x_814_ = l_Lean_Syntax_node4(v___x_652_, v___x_702_, v___x_703_, v___x_710_, v___x_731_, v___x_813_);
v___x_815_ = l_Lean_Syntax_node2(v___x_652_, v___x_680_, v___x_700_, v___x_814_);
v___x_816_ = l_Lean_Syntax_node3(v___x_652_, v___x_656_, v___x_678_, v___x_679_, v___x_815_);
v___x_817_ = lean_array_push(v___x_707_, v___y_631_);
v___x_818_ = lean_array_push(v___x_817_, v___x_816_);
v___x_819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_819_, 0, v___y_638_);
lean_ctor_set(v___x_819_, 1, v___x_663_);
lean_ctor_set(v___x_819_, 2, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___y_651_);
return v___x_820_;
}
v___jp_821_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_box(2);
v___x_841_ = l_Lean_Syntax_mkStrLit(v___y_839_, v___x_840_);
if (lean_obj_tag(v___y_837_) == 0)
{
lean_object* v_quotContext_842_; lean_object* v_currMacroScope_843_; lean_object* v_ref_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_quotContext_842_ = lean_ctor_get(v___y_823_, 1);
v_currMacroScope_843_ = lean_ctor_get(v___y_823_, 2);
v_ref_844_ = lean_ctor_get(v___y_823_, 5);
v___x_845_ = l_Lean_SourceInfo_fromRef(v_ref_844_, v___y_826_);
v___x_846_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__90));
v___x_847_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__91));
lean_inc(v___x_845_);
v___x_848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_845_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
v___x_849_ = l_Lean_Syntax_node1(v___x_845_, v___x_847_, v___x_848_);
v___y_631_ = v___y_822_;
v___y_632_ = v___x_841_;
v___y_633_ = v___y_824_;
v___y_634_ = v___y_825_;
v___y_635_ = v___y_826_;
v___y_636_ = v___y_827_;
v___y_637_ = v___y_828_;
v___y_638_ = v___x_840_;
v___y_639_ = v___y_829_;
v___y_640_ = v___y_831_;
v___y_641_ = v___y_832_;
v___y_642_ = v___y_833_;
v___y_643_ = v___y_834_;
v___y_644_ = v___y_835_;
v___y_645_ = v___y_836_;
v___y_646_ = v___y_838_;
v_specTac_647_ = v___x_849_;
v_quotContext_648_ = v_quotContext_842_;
v_currMacroScope_649_ = v_currMacroScope_843_;
v_ref_650_ = v_ref_844_;
v___y_651_ = v___y_830_;
goto v___jp_630_;
}
else
{
lean_object* v_val_850_; lean_object* v_quotContext_851_; lean_object* v_currMacroScope_852_; lean_object* v_ref_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_val_850_ = lean_ctor_get(v___y_837_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v___y_837_, 1);
v_quotContext_851_ = lean_ctor_get(v___y_823_, 1);
v_currMacroScope_852_ = lean_ctor_get(v___y_823_, 2);
v_ref_853_ = lean_ctor_get(v___y_823_, 5);
v___x_854_ = l_Lean_SourceInfo_fromRef(v_ref_853_, v___y_826_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__92));
v___x_856_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__65));
lean_inc_n(v___x_854_, 2);
v___x_857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_854_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__77));
v___x_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_854_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = l_Lean_Syntax_node3(v___x_854_, v___x_855_, v___x_857_, v_val_850_, v___x_859_);
v___y_631_ = v___y_822_;
v___y_632_ = v___x_841_;
v___y_633_ = v___y_824_;
v___y_634_ = v___y_825_;
v___y_635_ = v___y_826_;
v___y_636_ = v___y_827_;
v___y_637_ = v___y_828_;
v___y_638_ = v___x_840_;
v___y_639_ = v___y_829_;
v___y_640_ = v___y_831_;
v___y_641_ = v___y_832_;
v___y_642_ = v___y_833_;
v___y_643_ = v___y_834_;
v___y_644_ = v___y_835_;
v___y_645_ = v___y_836_;
v___y_646_ = v___y_838_;
v_specTac_647_ = v___x_860_;
v_quotContext_648_ = v_quotContext_851_;
v_currMacroScope_649_ = v_currMacroScope_852_;
v_ref_650_ = v_ref_853_;
v___y_651_ = v___y_830_;
goto v___jp_630_;
}
}
v___jp_861_:
{
if (lean_obj_tag(v___y_876_) == 0)
{
lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__93));
v___x_881_ = 1;
v___x_882_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_867_, v___x_881_);
v___x_883_ = lean_string_append(v___x_880_, v___x_882_);
lean_dec_ref(v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__94));
v___x_885_ = lean_string_append(v___x_883_, v___x_884_);
v___y_822_ = v___y_862_;
v___y_823_ = v___y_878_;
v___y_824_ = v___y_863_;
v___y_825_ = v___y_864_;
v___y_826_ = v___y_865_;
v___y_827_ = v___y_866_;
v___y_828_ = v___y_868_;
v___y_829_ = v___y_869_;
v___y_830_ = v___y_879_;
v___y_831_ = v___y_870_;
v___y_832_ = v___y_871_;
v___y_833_ = v___y_872_;
v___y_834_ = v___y_873_;
v___y_835_ = v_post_877_;
v___y_836_ = v___y_874_;
v___y_837_ = v___y_876_;
v___y_838_ = v___y_875_;
v___y_839_ = v___x_885_;
goto v___jp_821_;
}
else
{
lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__93));
v___x_887_ = 1;
v___x_888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_867_, v___x_887_);
v___x_889_ = lean_string_append(v___x_886_, v___x_888_);
lean_dec_ref(v___x_888_);
v___x_890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__95));
v___x_891_ = lean_string_append(v___x_889_, v___x_890_);
v___y_822_ = v___y_862_;
v___y_823_ = v___y_878_;
v___y_824_ = v___y_863_;
v___y_825_ = v___y_864_;
v___y_826_ = v___y_865_;
v___y_827_ = v___y_866_;
v___y_828_ = v___y_868_;
v___y_829_ = v___y_869_;
v___y_830_ = v___y_879_;
v___y_831_ = v___y_870_;
v___y_832_ = v___y_871_;
v___y_833_ = v___y_872_;
v___y_834_ = v___y_873_;
v___y_835_ = v_post_877_;
v___y_836_ = v___y_874_;
v___y_837_ = v___y_876_;
v___y_838_ = v___y_875_;
v___y_839_ = v___x_891_;
goto v___jp_821_;
}
}
v___jp_893_:
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_Syntax_isNone(v___y_902_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = l_Lean_Syntax_getArg(v___y_902_, v___y_901_);
lean_dec(v___y_902_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__97));
lean_inc(v___x_913_);
v___x_915_ = l_Lean_Syntax_isOfKind(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec(v___x_913_);
v___x_916_ = l_Lean_Macro_throwUnsupported___redArg(v___y_911_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v_a_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
v_a_918_ = lean_ctor_get(v___x_916_, 1);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_916_, 2);
v___y_862_ = v___y_894_;
v___y_863_ = v___y_895_;
v___y_864_ = v___y_896_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
v___y_867_ = v___y_899_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
v___y_870_ = v_pre_909_;
v___y_871_ = v___y_903_;
v___y_872_ = v___y_904_;
v___y_873_ = v___y_905_;
v___y_874_ = v___y_906_;
v___y_875_ = v___y_908_;
v___y_876_ = v___y_907_;
v_post_877_ = v_a_917_;
v___y_878_ = v___y_910_;
v___y_879_ = v_a_918_;
goto v___jp_861_;
}
else
{
lean_object* v_a_919_; lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_pre_909_);
lean_dec(v___y_907_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
v_a_919_ = lean_ctor_get(v___x_916_, 0);
v_a_920_ = lean_ctor_get(v___x_916_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_916_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_inc(v_a_919_);
lean_dec(v___x_916_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_919_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = l_Lean_Syntax_getArg(v___x_913_, v___x_892_);
lean_dec(v___x_913_);
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
lean_inc(v___x_928_);
v___x_930_ = l_Lean_Syntax_isOfKind(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__101));
lean_inc(v___x_928_);
v___x_932_ = l_Lean_Syntax_isOfKind(v___x_928_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec(v___x_928_);
v___x_933_ = l_Lean_Macro_throwUnsupported___redArg(v___y_911_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_a_935_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
v_a_935_ = lean_ctor_get(v___x_933_, 1);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_933_, 2);
v___y_862_ = v___y_894_;
v___y_863_ = v___y_895_;
v___y_864_ = v___y_896_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
v___y_867_ = v___y_899_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
v___y_870_ = v_pre_909_;
v___y_871_ = v___y_903_;
v___y_872_ = v___y_904_;
v___y_873_ = v___y_905_;
v___y_874_ = v___y_906_;
v___y_875_ = v___y_908_;
v___y_876_ = v___y_907_;
v_post_877_ = v_a_934_;
v___y_878_ = v___y_910_;
v___y_879_ = v_a_935_;
goto v___jp_861_;
}
else
{
lean_object* v_a_936_; lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_pre_909_);
lean_dec(v___y_907_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
v_a_936_ = lean_ctor_get(v___x_933_, 0);
v_a_937_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_inc(v_a_936_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_936_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_ref_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_ref_945_ = lean_ctor_get(v___y_910_, 5);
v___x_946_ = l_Lean_SourceInfo_fromRef(v_ref_945_, v___x_930_);
v___x_947_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_946_);
v___x_949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_946_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
v___x_950_ = l_Lean_Syntax_node2(v___x_946_, v___x_948_, v___x_949_, v___x_928_);
v___y_862_ = v___y_894_;
v___y_863_ = v___y_895_;
v___y_864_ = v___y_896_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
v___y_867_ = v___y_899_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
v___y_870_ = v_pre_909_;
v___y_871_ = v___y_903_;
v___y_872_ = v___y_904_;
v___y_873_ = v___y_905_;
v___y_874_ = v___y_906_;
v___y_875_ = v___y_908_;
v___y_876_ = v___y_907_;
v_post_877_ = v___x_950_;
v___y_878_ = v___y_910_;
v___y_879_ = v___y_911_;
goto v___jp_861_;
}
}
else
{
lean_object* v_ref_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_ref_951_ = lean_ctor_get(v___y_910_, 5);
v___x_952_ = l_Lean_SourceInfo_fromRef(v_ref_951_, v___x_912_);
v___x_953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_952_);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_952_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
v___x_956_ = l_Lean_Syntax_node2(v___x_952_, v___x_954_, v___x_955_, v___x_928_);
v___y_862_ = v___y_894_;
v___y_863_ = v___y_895_;
v___y_864_ = v___y_896_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
v___y_867_ = v___y_899_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
v___y_870_ = v_pre_909_;
v___y_871_ = v___y_903_;
v___y_872_ = v___y_904_;
v___y_873_ = v___y_905_;
v___y_874_ = v___y_906_;
v___y_875_ = v___y_908_;
v___y_876_ = v___y_907_;
v_post_877_ = v___x_956_;
v___y_878_ = v___y_910_;
v___y_879_ = v___y_911_;
goto v___jp_861_;
}
}
}
else
{
lean_object* v_ref_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v___y_902_);
v_ref_957_ = lean_ctor_get(v___y_910_, 5);
v___x_958_ = l_Lean_SourceInfo_fromRef(v_ref_957_, v___y_897_);
v___x_959_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_960_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc_n(v___x_958_, 9);
v___x_961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_958_);
lean_ctor_set(v___x_961_, 1, v___x_959_);
v___x_962_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_964_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__105));
v___x_965_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__106));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_958_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_Syntax_node1(v___x_958_, v___x_964_, v___x_966_);
v___x_968_ = l_Lean_Syntax_node1(v___x_958_, v___x_963_, v___x_967_);
v___x_969_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__19, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__19_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__19);
v___x_970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_970_, 0, v___x_958_);
lean_ctor_set(v___x_970_, 1, v___x_963_);
lean_ctor_set(v___x_970_, 2, v___x_969_);
v___x_971_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__107));
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_958_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__109));
v___x_974_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__110));
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_958_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_Syntax_node1(v___x_958_, v___x_973_, v___x_975_);
v___x_977_ = l_Lean_Syntax_node4(v___x_958_, v___x_962_, v___x_968_, v___x_970_, v___x_972_, v___x_976_);
v___x_978_ = l_Lean_Syntax_node2(v___x_958_, v___x_960_, v___x_961_, v___x_977_);
v___y_862_ = v___y_894_;
v___y_863_ = v___y_895_;
v___y_864_ = v___y_896_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
v___y_867_ = v___y_899_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
v___y_870_ = v_pre_909_;
v___y_871_ = v___y_903_;
v___y_872_ = v___y_904_;
v___y_873_ = v___y_905_;
v___y_874_ = v___y_906_;
v___y_875_ = v___y_908_;
v___y_876_ = v___y_907_;
v_post_877_ = v___x_978_;
v___y_878_ = v___y_910_;
v___y_879_ = v___y_911_;
goto v___jp_861_;
}
}
v___jp_979_:
{
if (v___y_983_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = l_Lean_Syntax_getArg(v___y_980_, v___y_989_);
lean_dec(v___y_980_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__112));
lean_inc(v___x_999_);
v___x_1001_ = l_Lean_Syntax_isOfKind(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
lean_dec(v___x_999_);
v___x_1002_ = l_Lean_Macro_throwUnsupported___redArg(v___y_997_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v_a_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
v_a_1004_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1002_, 2);
v___y_894_ = v___y_982_;
v___y_895_ = v___y_998_;
v___y_896_ = v___y_984_;
v___y_897_ = v___y_985_;
v___y_898_ = v___y_986_;
v___y_899_ = v___y_987_;
v___y_900_ = v___y_988_;
v___y_901_ = v___y_989_;
v___y_902_ = v___y_990_;
v___y_903_ = v___y_991_;
v___y_904_ = v___y_992_;
v___y_905_ = v___y_993_;
v___y_906_ = v___y_994_;
v___y_907_ = v___y_996_;
v___y_908_ = v___y_995_;
v_pre_909_ = v_a_1003_;
v___y_910_ = v___y_981_;
v___y_911_ = v_a_1004_;
goto v___jp_893_;
}
else
{
lean_object* v_a_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v___y_998_);
lean_dec(v___y_996_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_987_);
lean_dec(v___y_982_);
v_a_1005_ = lean_ctor_get(v___x_1002_, 0);
v_a_1006_ = lean_ctor_get(v___x_1002_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1002_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_inc(v_a_1005_);
lean_dec(v___x_1002_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1005_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1014_ = l_Lean_Syntax_getArg(v___x_999_, v___x_892_);
lean_dec(v___x_999_);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
lean_inc(v___x_1014_);
v___x_1016_ = l_Lean_Syntax_isOfKind(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
v___y_894_ = v___y_982_;
v___y_895_ = v___y_998_;
v___y_896_ = v___y_984_;
v___y_897_ = v___y_985_;
v___y_898_ = v___y_986_;
v___y_899_ = v___y_987_;
v___y_900_ = v___y_988_;
v___y_901_ = v___y_989_;
v___y_902_ = v___y_990_;
v___y_903_ = v___y_991_;
v___y_904_ = v___y_992_;
v___y_905_ = v___y_993_;
v___y_906_ = v___y_994_;
v___y_907_ = v___y_996_;
v___y_908_ = v___y_995_;
v_pre_909_ = v___x_1014_;
v___y_910_ = v___y_981_;
v___y_911_ = v___y_997_;
goto v___jp_893_;
}
else
{
lean_object* v_ref_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_ref_1017_ = lean_ctor_get(v___y_981_, 5);
v___x_1018_ = l_Lean_SourceInfo_fromRef(v_ref_1017_, v___y_983_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_1018_);
v___x_1021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1018_);
lean_ctor_set(v___x_1021_, 1, v___x_1019_);
v___x_1022_ = l_Lean_Syntax_node2(v___x_1018_, v___x_1020_, v___x_1021_, v___x_1014_);
v___y_894_ = v___y_982_;
v___y_895_ = v___y_998_;
v___y_896_ = v___y_984_;
v___y_897_ = v___y_985_;
v___y_898_ = v___y_986_;
v___y_899_ = v___y_987_;
v___y_900_ = v___y_988_;
v___y_901_ = v___y_989_;
v___y_902_ = v___y_990_;
v___y_903_ = v___y_991_;
v___y_904_ = v___y_992_;
v___y_905_ = v___y_993_;
v___y_906_ = v___y_994_;
v___y_907_ = v___y_996_;
v___y_908_ = v___y_995_;
v_pre_909_ = v___x_1022_;
v___y_910_ = v___y_981_;
v___y_911_ = v___y_997_;
goto v___jp_893_;
}
}
}
else
{
lean_object* v_ref_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v___y_980_);
v_ref_1023_ = lean_ctor_get(v___y_981_, 5);
v___x_1024_ = l_Lean_SourceInfo_fromRef(v_ref_1023_, v___y_985_);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__109));
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__110));
lean_inc(v___x_1024_);
v___x_1027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1024_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node1(v___x_1024_, v___x_1025_, v___x_1027_);
v___y_894_ = v___y_982_;
v___y_895_ = v___y_998_;
v___y_896_ = v___y_984_;
v___y_897_ = v___y_985_;
v___y_898_ = v___y_986_;
v___y_899_ = v___y_987_;
v___y_900_ = v___y_988_;
v___y_901_ = v___y_989_;
v___y_902_ = v___y_990_;
v___y_903_ = v___y_991_;
v___y_904_ = v___y_992_;
v___y_905_ = v___y_993_;
v___y_906_ = v___y_994_;
v___y_907_ = v___y_996_;
v___y_908_ = v___y_995_;
v_pre_909_ = v___x_1028_;
v___y_910_ = v___y_981_;
v___y_911_ = v___y_997_;
goto v___jp_893_;
}
}
v___jp_1030_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; size_t v_sz_1053_; size_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1043_ = l_Lean_Syntax_getArg(v_decl_1029_, v___y_1038_);
v___x_1044_ = l_Lean_Syntax_getArg(v_decl_1029_, v___x_892_);
lean_dec(v_decl_1029_);
v___x_1045_ = l_Lean_Syntax_getArg(v___x_1044_, v___y_1033_);
lean_dec(v___x_1044_);
v___x_1046_ = l_Lean_TSyntax_getId(v___x_1045_);
v___x_1047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0));
v___x_1048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
lean_inc(v___x_1046_);
v___x_1049_ = l_Lean_Name_append(v___x_1046_, v___x_1048_);
v___x_1050_ = l_Lean_mkIdentFrom(v___x_1045_, v___x_1049_, v___y_1037_);
v___x_1051_ = l_Lean_Syntax_getArg(v___x_1043_, v___y_1033_);
lean_dec(v___x_1043_);
v___x_1052_ = l_Lean_Syntax_getArgs(v___x_1051_);
lean_dec(v___x_1051_);
v_sz_1053_ = lean_array_size(v___x_1052_);
v___x_1054_ = ((size_t)0ULL);
lean_inc_ref(v___x_1052_);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_1053_, v___x_1054_, v___x_1052_);
v___x_1056_ = lean_mk_empty_array_with_capacity(v___y_1033_);
v___x_1057_ = lean_array_get_size(v___x_1052_);
v___x_1058_ = lean_nat_dec_lt(v___y_1033_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v___x_1052_);
v___y_980_ = v___y_1031_;
v___y_981_ = v___y_1041_;
v___y_982_ = v___y_1032_;
v___y_983_ = v___y_1035_;
v___y_984_ = v___y_1034_;
v___y_985_ = v___y_1037_;
v___y_986_ = v___y_1038_;
v___y_987_ = v___x_1046_;
v___y_988_ = v___y_1040_;
v___y_989_ = v___y_1033_;
v___y_990_ = v___y_1036_;
v___y_991_ = v___x_1055_;
v___y_992_ = v___x_1045_;
v___y_993_ = v___x_1050_;
v___y_994_ = v___x_1054_;
v___y_995_ = v___x_1047_;
v___y_996_ = v___y_1039_;
v___y_997_ = v___y_1042_;
v___y_998_ = v___x_1056_;
goto v___jp_979_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_le(v___x_1057_, v___x_1057_);
if (v___x_1059_ == 0)
{
if (v___x_1058_ == 0)
{
lean_dec_ref(v___x_1052_);
v___y_980_ = v___y_1031_;
v___y_981_ = v___y_1041_;
v___y_982_ = v___y_1032_;
v___y_983_ = v___y_1035_;
v___y_984_ = v___y_1034_;
v___y_985_ = v___y_1037_;
v___y_986_ = v___y_1038_;
v___y_987_ = v___x_1046_;
v___y_988_ = v___y_1040_;
v___y_989_ = v___y_1033_;
v___y_990_ = v___y_1036_;
v___y_991_ = v___x_1055_;
v___y_992_ = v___x_1045_;
v___y_993_ = v___x_1050_;
v___y_994_ = v___x_1054_;
v___y_995_ = v___x_1047_;
v___y_996_ = v___y_1039_;
v___y_997_ = v___y_1042_;
v___y_998_ = v___x_1056_;
goto v___jp_979_;
}
else
{
size_t v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_usize_of_nat(v___x_1057_);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___x_1052_, v___x_1054_, v___x_1060_, v___x_1056_);
lean_dec_ref(v___x_1052_);
v___y_980_ = v___y_1031_;
v___y_981_ = v___y_1041_;
v___y_982_ = v___y_1032_;
v___y_983_ = v___y_1035_;
v___y_984_ = v___y_1034_;
v___y_985_ = v___y_1037_;
v___y_986_ = v___y_1038_;
v___y_987_ = v___x_1046_;
v___y_988_ = v___y_1040_;
v___y_989_ = v___y_1033_;
v___y_990_ = v___y_1036_;
v___y_991_ = v___x_1055_;
v___y_992_ = v___x_1045_;
v___y_993_ = v___x_1050_;
v___y_994_ = v___x_1054_;
v___y_995_ = v___x_1047_;
v___y_996_ = v___y_1039_;
v___y_997_ = v___y_1042_;
v___y_998_ = v___x_1061_;
goto v___jp_979_;
}
}
else
{
size_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_usize_of_nat(v___x_1057_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___x_1052_, v___x_1054_, v___x_1062_, v___x_1056_);
lean_dec_ref(v___x_1052_);
v___y_980_ = v___y_1031_;
v___y_981_ = v___y_1041_;
v___y_982_ = v___y_1032_;
v___y_983_ = v___y_1035_;
v___y_984_ = v___y_1034_;
v___y_985_ = v___y_1037_;
v___y_986_ = v___y_1038_;
v___y_987_ = v___x_1046_;
v___y_988_ = v___y_1040_;
v___y_989_ = v___y_1033_;
v___y_990_ = v___y_1036_;
v___y_991_ = v___x_1055_;
v___y_992_ = v___x_1045_;
v___y_993_ = v___x_1050_;
v___y_994_ = v___x_1054_;
v___y_995_ = v___x_1047_;
v___y_996_ = v___y_1039_;
v___y_997_ = v___y_1042_;
v___y_998_ = v___x_1063_;
goto v___jp_979_;
}
}
}
v___jp_1064_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__113));
v___x_1079_ = l_Lean_Macro_throwErrorAt___redArg(v___y_1077_, v___x_1078_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1077_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 1);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 2);
v___y_1031_ = v___y_1065_;
v___y_1032_ = v___y_1066_;
v___y_1033_ = v___y_1067_;
v___y_1034_ = v___y_1069_;
v___y_1035_ = v___y_1068_;
v___y_1036_ = v___y_1070_;
v___y_1037_ = v___y_1071_;
v___y_1038_ = v___y_1072_;
v___y_1039_ = v___y_1073_;
v___y_1040_ = v___y_1074_;
v___y_1041_ = v___y_1075_;
v___y_1042_ = v_a_1080_;
goto v___jp_1030_;
}
else
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v___y_1073_);
lean_dec(v___y_1070_);
lean_dec(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec(v_decl_1029_);
v_a_1081_ = lean_ctor_get(v___x_1079_, 0);
v_a_1082_ = lean_ctor_get(v___x_1079_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1079_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_inc(v_a_1081_);
lean_dec(v___x_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
v___jp_1090_:
{
if (v___y_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_unsigned_to_nat(2u);
v___x_1101_ = l_Lean_Syntax_getArg(v___y_1098_, v___x_1100_);
lean_dec(v___y_1098_);
v___x_1102_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v___x_1101_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v_a_1104_; lean_object* v_fst_1105_; lean_object* v_snd_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
v_a_1104_ = lean_ctor_get(v___x_1102_, 1);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1102_, 2);
v_fst_1105_ = lean_ctor_get(v_a_1103_, 0);
lean_inc(v_fst_1105_);
v_snd_1106_ = lean_ctor_get(v_a_1103_, 1);
lean_inc(v_snd_1106_);
lean_dec(v_a_1103_);
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__114));
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__115));
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__117));
v___x_1110_ = l_Lean_Macro_hasDecl(v___x_1109_, v___y_1096_, v_a_1104_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
v_a_1112_ = lean_ctor_get(v___x_1110_, 1);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1110_, 2);
lean_inc(v_decl_1029_);
v___x_1113_ = l_Lean_Syntax_setArg(v_decl_1029_, v___y_1093_, v_snd_1106_);
v___x_1114_ = l_Lean_Syntax_setArg(v_stx_627_, v___x_892_, v___x_1113_);
v___x_1115_ = lean_unbox(v_a_1111_);
lean_dec(v_a_1111_);
if (v___x_1115_ == 0)
{
if (v___y_1094_ == 0)
{
lean_inc(v___y_1091_);
v___y_1065_ = v___y_1091_;
v___y_1066_ = v___x_1114_;
v___y_1067_ = v___y_1092_;
v___y_1068_ = v___y_1094_;
v___y_1069_ = v___x_1107_;
v___y_1070_ = v___y_1095_;
v___y_1071_ = v___y_1099_;
v___y_1072_ = v___x_1100_;
v___y_1073_ = v_fst_1105_;
v___y_1074_ = v___x_1108_;
v___y_1075_ = v___y_1096_;
v___y_1076_ = v_a_1112_;
v___y_1077_ = v___y_1091_;
goto v___jp_1064_;
}
else
{
lean_inc(v___y_1095_);
v___y_1065_ = v___y_1091_;
v___y_1066_ = v___x_1114_;
v___y_1067_ = v___y_1092_;
v___y_1068_ = v___y_1094_;
v___y_1069_ = v___x_1107_;
v___y_1070_ = v___y_1095_;
v___y_1071_ = v___y_1099_;
v___y_1072_ = v___x_1100_;
v___y_1073_ = v_fst_1105_;
v___y_1074_ = v___x_1108_;
v___y_1075_ = v___y_1096_;
v___y_1076_ = v_a_1112_;
v___y_1077_ = v___y_1095_;
goto v___jp_1064_;
}
}
else
{
v___y_1031_ = v___y_1091_;
v___y_1032_ = v___x_1114_;
v___y_1033_ = v___y_1092_;
v___y_1034_ = v___x_1107_;
v___y_1035_ = v___y_1094_;
v___y_1036_ = v___y_1095_;
v___y_1037_ = v___y_1099_;
v___y_1038_ = v___x_1100_;
v___y_1039_ = v_fst_1105_;
v___y_1040_ = v___x_1108_;
v___y_1041_ = v___y_1096_;
v___y_1042_ = v_a_1112_;
goto v___jp_1030_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_snd_1106_);
lean_dec(v_fst_1105_);
lean_dec(v___y_1095_);
lean_dec(v___y_1091_);
lean_dec(v_decl_1029_);
lean_dec(v_stx_627_);
v_a_1116_ = lean_ctor_get(v___x_1110_, 0);
v_a_1117_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1110_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_inc(v_a_1116_);
lean_dec(v___x_1110_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1116_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v___y_1095_);
lean_dec(v___y_1091_);
lean_dec(v_decl_1029_);
lean_dec(v_stx_627_);
v_a_1125_ = lean_ctor_get(v___x_1102_, 0);
v_a_1126_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1102_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_inc(v_a_1125_);
lean_dec(v___x_1102_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec(v___y_1095_);
lean_dec(v___y_1091_);
v___x_1134_ = lean_unsigned_to_nat(2u);
v___x_1135_ = l_Lean_Syntax_getArg(v___y_1098_, v___x_1134_);
lean_dec(v___y_1098_);
v___x_1136_ = l_Lean_Syntax_setArg(v_decl_1029_, v___y_1093_, v___x_1135_);
v___x_1137_ = l_Lean_Syntax_setArg(v_stx_627_, v___x_892_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___y_1097_);
return v___x_1138_;
}
}
v___jp_1139_:
{
lean_object* v___x_1144_; lean_object* v_requiresStx_1145_; lean_object* v_ensuresStx_1146_; uint8_t v___x_1147_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v_requiresStx_1145_ = l_Lean_Syntax_getArg(v___y_1141_, v___x_1144_);
v_ensuresStx_1146_ = l_Lean_Syntax_getArg(v___y_1141_, v___x_892_);
v___x_1147_ = l_Lean_Syntax_isNone(v_requiresStx_1145_);
if (v___x_1147_ == 0)
{
v___y_1091_ = v_requiresStx_1145_;
v___y_1092_ = v___x_1144_;
v___y_1093_ = v___y_1140_;
v___y_1094_ = v___x_1147_;
v___y_1095_ = v_ensuresStx_1146_;
v___y_1096_ = v___y_1142_;
v___y_1097_ = v___y_1143_;
v___y_1098_ = v___y_1141_;
v___y_1099_ = v___x_1147_;
goto v___jp_1090_;
}
else
{
uint8_t v___x_1148_; 
v___x_1148_ = l_Lean_Syntax_isNone(v_ensuresStx_1146_);
v___y_1091_ = v_requiresStx_1145_;
v___y_1092_ = v___x_1144_;
v___y_1093_ = v___y_1140_;
v___y_1094_ = v___x_1147_;
v___y_1095_ = v_ensuresStx_1146_;
v___y_1096_ = v___y_1142_;
v___y_1097_ = v___y_1143_;
v___y_1098_ = v___y_1141_;
v___y_1099_ = v___x_1148_;
goto v___jp_1090_;
}
}
v___jp_1149_:
{
lean_object* v___x_1152_; lean_object* v_val_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1152_ = lean_unsigned_to_nat(3u);
v_val_1153_ = l_Lean_Syntax_getArg(v_decl_1029_, v___x_1152_);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__119));
lean_inc(v_val_1153_);
v___x_1155_ = l_Lean_Syntax_isOfKind(v_val_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1151_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 1);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 2);
v___y_1140_ = v___x_1152_;
v___y_1141_ = v_val_1153_;
v___y_1142_ = v___y_1150_;
v___y_1143_ = v_a_1157_;
goto v___jp_1139_;
}
else
{
lean_object* v_a_1158_; lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_val_1153_);
lean_dec(v_decl_1029_);
lean_dec(v_stx_627_);
v_a_1158_ = lean_ctor_get(v___x_1156_, 0);
v_a_1159_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1156_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_inc(v_a_1158_);
lean_dec(v___x_1156_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1158_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
v___y_1140_ = v___x_1152_;
v___y_1141_ = v_val_1153_;
v___y_1142_ = v___y_1150_;
v___y_1143_ = v___y_1151_;
goto v___jp_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___boxed(lean_object* v_stx_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Elab_Tactic_Do_expandDefContract(v_stx_1180_, v_a_1181_, v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1(){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1194_ = l_Lean_Elab_macroAttribute;
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_1196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3));
v___x_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_expandDefContract___boxed), 3, 0);
v___x_1198_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1194_, v___x_1195_, v___x_1196_, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___boxed(lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3(){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3));
v___x_1204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0));
v___x_1205_ = l_Lean_addBuiltinDocString(v___x_1203_, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
return v_res_1207_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___closed__0);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg();
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object* v_00_u03b1_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg();
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object* v_00_u03b1_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(v_00_u03b1_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object* v_msgData_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v_env_1243_; lean_object* v___x_1244_; lean_object* v_mctx_1245_; lean_object* v_lctx_1246_; lean_object* v_options_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1242_ = lean_st_ref_get(v___y_1240_);
v_env_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_env_1243_);
lean_dec(v___x_1242_);
v___x_1244_ = lean_st_ref_get(v___y_1238_);
v_mctx_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_mctx_1245_);
lean_dec(v___x_1244_);
v_lctx_1246_ = lean_ctor_get(v___y_1237_, 2);
v_options_1247_ = lean_ctor_get(v___y_1239_, 2);
lean_inc_ref(v_options_1247_);
lean_inc_ref(v_lctx_1246_);
v___x_1248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1248_, 0, v_env_1243_);
lean_ctor_set(v___x_1248_, 1, v_mctx_1245_);
lean_ctor_set(v___x_1248_, 2, v_lctx_1246_);
lean_ctor_set(v___x_1248_, 3, v_options_1247_);
v___x_1249_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v_msgData_1236_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_msgData_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___redArg(lean_object* v_msg_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_ref_1264_; lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1274_; 
v_ref_1264_ = lean_ctor_get(v___y_1261_, 5);
v___x_1265_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_msg_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
lean_inc(v_ref_1264_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_ref_1264_);
lean_ctor_set(v___x_1270_, 1, v_a_1266_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 0, v___x_1270_);
v___x_1272_ = v___x_1268_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___redArg(v_msg_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___redArg(lean_object* v_ref_1282_, lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_fileName_1292_; lean_object* v_fileMap_1293_; lean_object* v_options_1294_; lean_object* v_currRecDepth_1295_; lean_object* v_maxRecDepth_1296_; lean_object* v_ref_1297_; lean_object* v_currNamespace_1298_; lean_object* v_openDecls_1299_; lean_object* v_initHeartbeats_1300_; lean_object* v_maxHeartbeats_1301_; lean_object* v_quotContext_1302_; lean_object* v_currMacroScope_1303_; uint8_t v_diag_1304_; lean_object* v_cancelTk_x3f_1305_; uint8_t v_suppressElabErrors_1306_; lean_object* v_inheritedTraceOptions_1307_; lean_object* v_ref_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_fileName_1292_ = lean_ctor_get(v___y_1289_, 0);
v_fileMap_1293_ = lean_ctor_get(v___y_1289_, 1);
v_options_1294_ = lean_ctor_get(v___y_1289_, 2);
v_currRecDepth_1295_ = lean_ctor_get(v___y_1289_, 3);
v_maxRecDepth_1296_ = lean_ctor_get(v___y_1289_, 4);
v_ref_1297_ = lean_ctor_get(v___y_1289_, 5);
v_currNamespace_1298_ = lean_ctor_get(v___y_1289_, 6);
v_openDecls_1299_ = lean_ctor_get(v___y_1289_, 7);
v_initHeartbeats_1300_ = lean_ctor_get(v___y_1289_, 8);
v_maxHeartbeats_1301_ = lean_ctor_get(v___y_1289_, 9);
v_quotContext_1302_ = lean_ctor_get(v___y_1289_, 10);
v_currMacroScope_1303_ = lean_ctor_get(v___y_1289_, 11);
v_diag_1304_ = lean_ctor_get_uint8(v___y_1289_, sizeof(void*)*14);
v_cancelTk_x3f_1305_ = lean_ctor_get(v___y_1289_, 12);
v_suppressElabErrors_1306_ = lean_ctor_get_uint8(v___y_1289_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1307_ = lean_ctor_get(v___y_1289_, 13);
v_ref_1308_ = l_Lean_replaceRef(v_ref_1282_, v_ref_1297_);
lean_inc_ref(v_inheritedTraceOptions_1307_);
lean_inc(v_cancelTk_x3f_1305_);
lean_inc(v_currMacroScope_1303_);
lean_inc(v_quotContext_1302_);
lean_inc(v_maxHeartbeats_1301_);
lean_inc(v_initHeartbeats_1300_);
lean_inc(v_openDecls_1299_);
lean_inc(v_currNamespace_1298_);
lean_inc(v_maxRecDepth_1296_);
lean_inc(v_currRecDepth_1295_);
lean_inc_ref(v_options_1294_);
lean_inc_ref(v_fileMap_1293_);
lean_inc_ref(v_fileName_1292_);
v___x_1309_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1309_, 0, v_fileName_1292_);
lean_ctor_set(v___x_1309_, 1, v_fileMap_1293_);
lean_ctor_set(v___x_1309_, 2, v_options_1294_);
lean_ctor_set(v___x_1309_, 3, v_currRecDepth_1295_);
lean_ctor_set(v___x_1309_, 4, v_maxRecDepth_1296_);
lean_ctor_set(v___x_1309_, 5, v_ref_1308_);
lean_ctor_set(v___x_1309_, 6, v_currNamespace_1298_);
lean_ctor_set(v___x_1309_, 7, v_openDecls_1299_);
lean_ctor_set(v___x_1309_, 8, v_initHeartbeats_1300_);
lean_ctor_set(v___x_1309_, 9, v_maxHeartbeats_1301_);
lean_ctor_set(v___x_1309_, 10, v_quotContext_1302_);
lean_ctor_set(v___x_1309_, 11, v_currMacroScope_1303_);
lean_ctor_set(v___x_1309_, 12, v_cancelTk_x3f_1305_);
lean_ctor_set(v___x_1309_, 13, v_inheritedTraceOptions_1307_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*14, v_diag_1304_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*14 + 1, v_suppressElabErrors_1306_);
v___x_1310_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___redArg(v_msg_1283_, v___y_1287_, v___y_1288_, v___x_1309_, v___y_1290_);
lean_dec_ref_known(v___x_1309_, 14);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___redArg___boxed(lean_object* v_ref_1311_, lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___redArg(v_ref_1311_, v_msg_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v_ref_1311_);
return v_res_1321_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2));
v___x_1330_ = l_Lean_mkCIdent(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object* v_stx_1340_, lean_object* v_dec_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v_tk_1351_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v_as_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v_tk_1351_ = l_Lean_Syntax_getArg(v_stx_1340_, v___x_1350_);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7));
lean_inc(v_stx_1340_);
v___x_1420_ = l_Lean_Syntax_isOfKind(v_stx_1340_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_tk_1351_);
lean_dec_ref(v_dec_1341_);
lean_dec(v_stx_1340_);
v___x_1421_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg();
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v_p_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v_p_1431_ = l_Lean_Syntax_getArg(v_stx_1340_, v___x_1430_);
lean_dec(v_stx_1340_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
lean_inc(v_p_1431_);
v___x_1433_ = l_Lean_Syntax_isOfKind(v_p_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
v_as_1396_ = v_p_1431_;
v___y_1397_ = v_a_1342_;
v___y_1398_ = v_a_1343_;
v___y_1399_ = v_a_1344_;
v___y_1400_ = v_a_1345_;
v___y_1401_ = v_a_1346_;
v___y_1402_ = v_a_1347_;
v___y_1403_ = v_a_1348_;
goto v___jp_1395_;
}
else
{
lean_object* v_ref_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_ref_1434_ = lean_ctor_get(v_a_1347_, 5);
v___x_1435_ = 0;
v___x_1436_ = l_Lean_SourceInfo_fromRef(v_ref_1434_, v___x_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_1438_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_1436_);
v___x_1439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1436_);
lean_ctor_set(v___x_1439_, 1, v___x_1437_);
v___x_1440_ = l_Lean_Syntax_node2(v___x_1436_, v___x_1438_, v___x_1439_, v_p_1431_);
v_as_1396_ = v___x_1440_;
v___y_1397_ = v_a_1342_;
v___y_1398_ = v_a_1343_;
v___y_1399_ = v_a_1344_;
v___y_1400_ = v_a_1345_;
v___y_1401_ = v_a_1346_;
v___y_1402_ = v_a_1347_;
v___y_1403_ = v_a_1348_;
goto v___jp_1395_;
}
}
v___jp_1352_:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_1341_, v_tk_1351_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v_tk_1351_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v_ref_1363_; lean_object* v___x_1364_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v_ref_1363_ = lean_ctor_get(v___y_1359_, 5);
v___x_1364_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_1354_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = l_Lean_Elab_Do_mkMonadApp(v_a_1365_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1386_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1386_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1386_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1371_ = 0;
v___x_1372_ = l_Lean_SourceInfo_fromRef(v_ref_1363_, v___x_1371_);
v___x_1373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
lean_inc(v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node1(v___x_1372_, v___x_1373_, v___y_1353_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v___x_1376_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3);
v___x_1377_ = l_Lean_Syntax_node2(v___x_1372_, v___x_1375_, v___x_1376_, v___x_1374_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 1);
v___x_1379_ = v___x_1369_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1367_);
v___x_1379_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = 1;
v___x_1381_ = lean_box(0);
v___x_1382_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1377_, v___x_1379_, v___x_1380_, v___x_1380_, v___x_1381_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_1362_, v_a_1383_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1384_;
}
else
{
lean_dec(v_a_1362_);
return v___x_1382_;
}
}
}
}
else
{
lean_dec(v_a_1362_);
lean_dec(v___y_1353_);
return v___x_1366_;
}
}
else
{
lean_dec(v_a_1362_);
lean_dec(v___y_1353_);
return v___x_1364_;
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v___y_1353_);
v_a_1387_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1361_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1361_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
v___jp_1395_:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; uint8_t v___x_1408_; 
v___x_1404_ = lean_st_ref_get(v___y_1403_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2));
v___x_1407_ = 1;
v___x_1408_ = l_Lean_Environment_contains(v_env_1405_, v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_as_1396_);
lean_dec_ref(v_dec_1341_);
v___x_1409_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5);
v___x_1410_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___redArg(v_tk_1351_, v___x_1409_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v_tk_1351_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
v___y_1353_ = v_as_1396_;
v___y_1354_ = v___y_1397_;
v___y_1355_ = v___y_1398_;
v___y_1356_ = v___y_1399_;
v___y_1357_ = v___y_1400_;
v___y_1358_ = v___y_1401_;
v___y_1359_ = v___y_1402_;
v___y_1360_ = v___y_1403_;
goto v___jp_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object* v_stx_1441_, lean_object* v_dec_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Elab_Tactic_Do_elabDoAssertion(v_stx_1441_, v_dec_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object* v_00_u03b1_1452_, lean_object* v_ref_1453_, lean_object* v_msg_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___redArg(v_ref_1453_, v_msg_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_ref_1465_, lean_object* v_msg_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_00_u03b1_1464_, v_ref_1465_, v_msg_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v_ref_1465_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object* v_00_u03b1_1476_, lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___redArg(v_msg_1477_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1487_, lean_object* v_msg_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_00_u03b1_1487_, v_msg_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1(){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1506_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_1507_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7));
v___x_1508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1));
v___x_1509_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed), 10, 0);
v___x_1510_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1506_, v___x_1507_, v___x_1508_, v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
return v_res_1512_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Std_WP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Contract(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Contract(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Std_WP(uint8_t builtin);
lean_object* initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Contract(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Contract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Contract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Contract(builtin);
}
#ifdef __cplusplus
}
#endif
