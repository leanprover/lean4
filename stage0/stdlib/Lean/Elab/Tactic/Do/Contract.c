// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Contract
// Imports: public import Std.Tactic.Do.Syntax public import Std.WP public import Lean.Elab.Util public import Lean.Elab.Command public import Lean.Elab.Do.Basic import Lean.DocString.Extension meta import Lean.Parser.Command meta import Lean.Parser.Term meta import Lean.Parser.Do import Init.Syntax import Init.Grind.Interactive
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_Do_experimental_intrinsic;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_pop(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "contractDeclVal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 214, 40, 194, 192, 243, 241, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2_value),((lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`; the `where finally | spec => ...` section does not discharge them"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__94 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__94_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "`; discharge them in a `where finally | spec => ...` section of the definition"};
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
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 125, .m_capacity = 125, .m_length = 124, .m_data = "`given`/`requires`/`ensures` contracts elaborate to a `vcgen`-proved specification theorem; add `import Std.WP` to use them."};
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
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__118 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__118_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__118_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__119 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__119_value;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 313, .m_capacity = 313, .m_length = 302, .m_data = "Expand a `def` carrying `given`/`requires`/`ensures` clauses into the plain `def` plus a spec\ntheorem `@[spec] theorem f.spec : ∀ xs, ⦃P⦄ f args ⦃fun b => Q⦄` proved by `vcgen`. A\n`where finally | spec => steps` section supplies `grind`-mode steps for the verification conditions\n`finish` leaves open. "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "The "};
static const lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1;
static const lean_string_object l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = " is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning."};
static const lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2 = (const lean_object*)&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "` clause"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabContractNotice"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 64, 145, 33, 235, 196, 87, 155)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "Report the experimental status of each contract clause the notice carries. "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "`assert` element"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Gadget"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "assertGadget"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__114_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__115_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 124, 11, 88, 114, 168, 194, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "the `assert` element elaborates to a `vcgen` gadget; add `import Std.WP` to use it."};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(lean_object* v_val_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_285_ = l_Lean_Syntax_getArgs(v_val_283_);
v___x_286_ = lean_array_pop(v___x_285_);
v___x_287_ = lean_box(2);
v___x_288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2));
v___x_289_ = lean_array_push(v___x_286_, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_290_, 0, v___x_287_);
lean_ctor_set(v___x_290_, 1, v___x_284_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___boxed(lean_object* v_val_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v_val_291_);
lean_dec(v_val_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(size_t v_sz_293_, size_t v_i_294_, lean_object* v_bs_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_usize_dec_lt(v_i_294_, v_sz_293_);
if (v___x_296_ == 0)
{
return v_bs_295_;
}
else
{
lean_object* v_v_297_; lean_object* v___x_298_; lean_object* v_bs_x27_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v_v_297_ = lean_array_uget(v_bs_295_, v_i_294_);
v___x_298_ = lean_unsigned_to_nat(0u);
v_bs_x27_299_ = lean_array_uset(v_bs_295_, v_i_294_, v___x_298_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_add(v_i_294_, v___x_300_);
v___x_302_ = lean_array_uset(v_bs_x27_299_, v_i_294_, v_v_297_);
v_i_294_ = v___x_301_;
v_bs_295_ = v___x_302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0___boxed(lean_object* v_sz_304_, lean_object* v_i_305_, lean_object* v_bs_306_){
_start:
{
size_t v_sz_boxed_307_; size_t v_i_boxed_308_; lean_object* v_res_309_; 
v_sz_boxed_307_ = lean_unbox_usize(v_sz_304_);
lean_dec(v_sz_304_);
v_i_boxed_308_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_boxed_307_, v_i_boxed_308_, v_bs_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(lean_object* v_as_310_, size_t v_i_311_, size_t v_stop_312_, lean_object* v_b_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_usize_dec_eq(v_i_311_, v_stop_312_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; size_t v___x_318_; size_t v___x_319_; 
v___x_315_ = lean_array_uget_borrowed(v_as_310_, v_i_311_);
lean_inc(v___x_315_);
v___x_316_ = l_Lean_Elab_Tactic_Do_contractBinderIdents(v___x_315_);
v___x_317_ = l_Array_append___redArg(v_b_313_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_311_, v___x_318_);
v_i_311_ = v___x_319_;
v_b_313_ = v___x_317_;
goto _start;
}
else
{
return v_b_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___boxed(lean_object* v_as_321_, lean_object* v_i_322_, lean_object* v_stop_323_, lean_object* v_b_324_){
_start:
{
size_t v_i_boxed_325_; size_t v_stop_boxed_326_; lean_object* v_res_327_; 
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v_as_321_, v_i_boxed_325_, v_stop_boxed_326_, v_b_324_);
lean_dec_ref(v_as_321_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(size_t v_sz_328_, size_t v_i_329_, lean_object* v_bs_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_usize_dec_lt(v_i_329_, v_sz_328_);
if (v___x_331_ == 0)
{
return v_bs_330_;
}
else
{
lean_object* v_v_332_; lean_object* v___x_333_; lean_object* v_bs_x27_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v_v_332_ = lean_array_uget(v_bs_330_, v_i_329_);
v___x_333_ = lean_unsigned_to_nat(0u);
v_bs_x27_334_ = lean_array_uset(v_bs_330_, v_i_329_, v___x_333_);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_329_, v___x_335_);
v___x_337_ = lean_array_uset(v_bs_x27_334_, v_i_329_, v_v_332_);
v_i_329_ = v___x_336_;
v_bs_330_ = v___x_337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1___boxed(lean_object* v_sz_339_, lean_object* v_i_340_, lean_object* v_bs_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v_i_boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_339_);
lean_dec(v_sz_339_);
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_boxed_342_, v_i_boxed_343_, v_bs_341_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__8(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__7));
v___x_366_ = l_String_toRawSubstring_x27(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__10(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__9));
v___x_369_ = l_String_toRawSubstring_x27(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__19(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Array_mkArray0(lean_box(0));
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract(lean_object* v_stx_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; uint8_t v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; size_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v_specTac_663_; lean_object* v_quotContext_664_; lean_object* v_currMacroScope_665_; lean_object* v_ref_666_; lean_object* v___y_667_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; size_t v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; uint8_t v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; size_t v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; uint8_t v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; size_t v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v_post_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___x_936_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; uint8_t v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; size_t v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v_pre_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; uint8_t v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; size_t v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; uint8_t v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v_decl_1109_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; uint8_t v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; uint8_t v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; uint8_t v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; uint8_t v___y_1180_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; uint8_t v___y_1226_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v_decl_1109_ = l_Lean_Syntax_getArg(v_stx_641_, v___x_936_);
v___x_1262_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__119));
lean_inc(v_decl_1109_);
v___x_1263_ = l_Lean_Syntax_isOfKind(v_decl_1109_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Macro_throwUnsupported___redArg(v_a_643_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 2);
v___y_1245_ = v_a_642_;
v___y_1246_ = v_a_1265_;
goto v___jp_1244_;
}
else
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_decl_1109_);
lean_dec(v_stx_641_);
v_a_1266_ = lean_ctor_get(v___x_1264_, 0);
v_a_1267_ = lean_ctor_get(v___x_1264_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1264_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_inc(v_a_1266_);
lean_dec(v___x_1264_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1266_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_a_1267_);
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
else
{
v___y_1245_ = v_a_642_;
v___y_1246_ = v_a_643_;
goto v___jp_1244_;
}
v___jp_644_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; size_t v_sz_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_668_ = l_Lean_SourceInfo_fromRef(v_ref_666_, v___y_648_);
v___x_669_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0));
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1));
v___x_671_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
v___x_672_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_673_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__2));
v___x_674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
lean_inc_n(v___x_668_, 81);
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_668_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
v___x_676_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__5));
v___x_677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__6));
v___x_678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_668_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_680_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__8, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__8_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__8);
lean_inc_ref_n(v___y_649_, 2);
lean_inc_ref_n(v___y_645_, 2);
v___x_681_ = l_Lean_Name_mkStr2(v___y_645_, v___y_649_);
lean_inc_n(v_currMacroScope_665_, 2);
lean_inc(v___x_681_);
lean_inc_n(v_quotContext_664_, 2);
v___x_682_ = l_Lean_addMacroScope(v_quotContext_664_, v___x_681_, v_currMacroScope_665_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
v___x_684_ = lean_box(0);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_686_, 0, v___x_668_);
lean_ctor_set(v___x_686_, 1, v___x_680_);
lean_ctor_set(v___x_686_, 2, v___x_682_);
lean_ctor_set(v___x_686_, 3, v___x_685_);
v___x_687_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__10, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__10_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__10);
v___x_688_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__12));
v___x_689_ = l_Lean_addMacroScope(v_quotContext_664_, v___x_688_, v_currMacroScope_665_);
v___x_690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__14));
v___x_691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_691_, 0, v___x_668_);
lean_ctor_set(v___x_691_, 1, v___x_687_);
lean_ctor_set(v___x_691_, 2, v___x_689_);
lean_ctor_set(v___x_691_, 3, v___x_690_);
v___x_692_ = l_Lean_Syntax_node2(v___x_668_, v___x_679_, v___x_686_, v___x_691_);
v___x_693_ = l_Lean_Syntax_node2(v___x_668_, v___x_676_, v___x_678_, v___x_692_);
v___x_694_ = l_Lean_Syntax_node2(v___x_668_, v___x_674_, v___x_675_, v___x_693_);
v___x_695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_668_);
lean_ctor_set(v___x_695_, 1, v___x_671_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_697_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__18));
v___x_698_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__19, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__19_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__19);
v___x_699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_699_, 0, v___x_668_);
lean_ctor_set(v___x_699_, 1, v___x_679_);
lean_ctor_set(v___x_699_, 2, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__21));
v___x_701_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__22));
v___x_702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_668_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__24));
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__26));
lean_inc_ref_n(v___x_699_, 25);
v___x_705_ = l_Lean_Syntax_node1(v___x_668_, v___x_704_, v___x_699_);
v___x_706_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__27));
lean_inc_ref_n(v___y_659_, 2);
v___x_707_ = l_Lean_Name_mkStr4(v___x_669_, v___x_670_, v___x_706_, v___y_659_);
v___x_708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_668_);
lean_ctor_set(v___x_708_, 1, v___y_659_);
v___x_709_ = l_Lean_Syntax_node2(v___x_668_, v___x_707_, v___x_708_, v___x_699_);
v___x_710_ = l_Lean_Syntax_node2(v___x_668_, v___x_703_, v___x_705_, v___x_709_);
v___x_711_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___x_710_);
v___x_712_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__28));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_668_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
lean_inc_ref(v___x_713_);
v___x_714_ = l_Lean_Syntax_node3(v___x_668_, v___x_700_, v___x_702_, v___x_711_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___x_714_);
v___x_716_ = l_Lean_Syntax_node7(v___x_668_, v___x_697_, v___x_699_, v___x_715_, v___x_699_, v___x_699_, v___x_699_, v___x_699_, v___x_699_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__29));
v___x_718_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__30));
v___x_719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_668_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__32));
v___x_721_ = lean_mk_empty_array_with_capacity(v___y_652_);
lean_inc_n(v___y_651_, 2);
v___x_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_722_, 0, v___y_651_);
lean_ctor_set(v___x_722_, 1, v___x_679_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
v___x_723_ = lean_mk_empty_array_with_capacity(v___y_655_);
v___x_724_ = lean_array_push(v___x_723_, v___y_654_);
v___x_725_ = lean_array_push(v___x_724_, v___x_722_);
v___x_726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_726_, 0, v___y_651_);
lean_ctor_set(v___x_726_, 1, v___x_720_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__34));
v___x_728_ = l_Array_append___redArg(v___x_698_, v___y_657_);
lean_dec_ref(v___y_657_);
v___x_729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_729_, 0, v___x_668_);
lean_ctor_set(v___x_729_, 1, v___x_679_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__36));
v___x_731_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__37));
v___x_732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_668_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__38));
v___x_734_ = l_Lean_Name_mkStr3(v___y_645_, v___y_649_, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__39));
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_668_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__40));
v___x_738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_668_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v_sz_740_ = lean_array_size(v___y_661_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_740_, v___y_660_, v___y_661_);
v___x_742_ = l_Array_append___redArg(v___x_698_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_743_, 0, v___x_668_);
lean_ctor_set(v___x_743_, 1, v___x_679_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
lean_inc(v___y_647_);
v___x_744_ = l_Lean_Syntax_node2(v___x_668_, v___x_739_, v___y_647_, v___x_743_);
lean_inc_ref(v___x_738_);
lean_inc_ref(v___x_736_);
v___x_745_ = l_Lean_Syntax_node8(v___x_668_, v___x_734_, v___x_736_, v___y_646_, v___x_738_, v___x_699_, v___x_744_, v___x_736_, v___y_658_, v___x_738_);
v___x_746_ = l_Lean_Syntax_node2(v___x_668_, v___x_730_, v___x_732_, v___x_745_);
v___x_747_ = l_Lean_Syntax_node2(v___x_668_, v___x_727_, v___x_729_, v___x_746_);
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2));
v___x_749_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__43));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_668_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__45));
v___x_752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__46));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_668_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__49));
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__51));
v___x_756_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__52));
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__53));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_668_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
v___x_759_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_760_ = l_Lean_Syntax_node1(v___x_668_, v___x_759_, v___x_699_);
v___x_761_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__56));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_668_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__58));
v___x_764_ = l_Lean_Syntax_node3(v___x_668_, v___x_763_, v___x_699_, v___x_699_, v___y_647_);
v___x_765_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node3(v___x_668_, v___x_679_, v___x_762_, v___x_765_, v___x_713_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__59));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_668_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__61));
v___x_770_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__64));
v___x_771_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__65));
v___x_772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_668_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__67));
v___x_774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__71));
v___x_776_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__73));
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__74));
v___x_778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_668_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__75));
v___x_780_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__76));
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_668_);
lean_ctor_set(v___x_781_, 1, v___x_779_);
v___x_782_ = l_Lean_Syntax_node4(v___x_668_, v___x_780_, v___x_781_, v___x_699_, v___x_699_, v___x_699_);
v___x_783_ = l_Lean_Syntax_node2(v___x_668_, v___x_775_, v___x_782_, v___x_699_);
v___x_784_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___x_783_);
v___x_785_ = l_Lean_Syntax_node1(v___x_668_, v___x_774_, v___x_784_);
v___x_786_ = l_Lean_Syntax_node1(v___x_668_, v___x_773_, v___x_785_);
v___x_787_ = l_Lean_Syntax_node2(v___x_668_, v___x_776_, v___x_778_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node2(v___x_668_, v___x_775_, v___x_787_, v___x_699_);
v___x_789_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node1(v___x_668_, v___x_774_, v___x_789_);
v___x_791_ = l_Lean_Syntax_node1(v___x_668_, v___x_773_, v___x_790_);
v___x_792_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__77));
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_668_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_Syntax_node3(v___x_668_, v___x_770_, v___x_772_, v___x_791_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node1(v___x_668_, v___x_769_, v___x_794_);
v___x_796_ = l_Lean_Syntax_node2(v___x_668_, v___x_679_, v___x_768_, v___x_795_);
v___x_797_ = l_Lean_Syntax_node8(v___x_668_, v___x_757_, v___x_758_, v___x_760_, v___x_766_, v___x_699_, v___x_699_, v___x_699_, v___x_699_, v___x_796_);
v___x_798_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__78));
v___x_799_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__79));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_668_);
lean_ctor_set(v___x_800_, 1, v___x_798_);
v___x_801_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__81));
v___x_802_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__82));
v___x_803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_668_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__83));
v___x_805_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__84));
v___x_806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_668_);
lean_ctor_set(v___x_806_, 1, v___x_804_);
v___x_807_ = l_Lean_Syntax_node1(v___x_668_, v___x_805_, v___x_806_);
v___x_808_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___x_807_);
v___x_809_ = l_Lean_Syntax_node1(v___x_668_, v___x_755_, v___x_808_);
v___x_810_ = l_Lean_Syntax_node1(v___x_668_, v___x_754_, v___x_809_);
lean_inc_ref(v___x_803_);
v___x_811_ = l_Lean_Syntax_node2(v___x_668_, v___x_801_, v___x_803_, v___x_810_);
v___x_812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__85));
v___x_813_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__86));
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_668_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
v___x_815_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___y_656_);
v___x_816_ = l_Lean_Syntax_node2(v___x_668_, v___x_813_, v___x_814_, v___x_815_);
v___x_817_ = l_Lean_Syntax_node1(v___x_668_, v___x_679_, v___x_816_);
v___x_818_ = l_Lean_Syntax_node1(v___x_668_, v___x_755_, v___x_817_);
v___x_819_ = l_Lean_Syntax_node1(v___x_668_, v___x_754_, v___x_818_);
v___x_820_ = l_Lean_Syntax_node2(v___x_668_, v___x_801_, v___x_803_, v___x_819_);
v___x_821_ = l_Lean_Syntax_node2(v___x_668_, v___x_679_, v___x_811_, v___x_820_);
v___x_822_ = l_Lean_Syntax_node2(v___x_668_, v___x_799_, v___x_800_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node5(v___x_668_, v___x_679_, v___x_797_, v___x_699_, v_specTac_663_, v___x_699_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node1(v___x_668_, v___x_755_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node1(v___x_668_, v___x_754_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node2(v___x_668_, v___x_751_, v___x_753_, v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__89));
v___x_828_ = l_Lean_Syntax_node2(v___x_668_, v___x_827_, v___x_699_, v___x_699_);
v___x_829_ = l_Lean_Syntax_node4(v___x_668_, v___x_748_, v___x_750_, v___x_826_, v___x_828_, v___x_699_);
v___x_830_ = l_Lean_Syntax_node4(v___x_668_, v___x_718_, v___x_719_, v___x_726_, v___x_747_, v___x_829_);
v___x_831_ = l_Lean_Syntax_node2(v___x_668_, v___x_696_, v___x_716_, v___x_830_);
v___x_832_ = l_Lean_Syntax_node3(v___x_668_, v___x_672_, v___x_694_, v___x_695_, v___x_831_);
v___x_833_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v___y_653_);
lean_dec(v___y_653_);
v___x_834_ = lean_mk_empty_array_with_capacity(v___y_662_);
v___x_835_ = lean_array_push(v___x_834_, v___x_833_);
v___x_836_ = lean_array_push(v___x_835_, v___y_650_);
v___x_837_ = lean_array_push(v___x_836_, v___x_832_);
v___x_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_838_, 0, v___y_651_);
lean_ctor_set(v___x_838_, 1, v___x_679_);
lean_ctor_set(v___x_838_, 2, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___y_667_);
return v___x_839_;
}
v___jp_840_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_box(2);
v___x_862_ = l_Lean_Syntax_mkStrLit(v___y_860_, v___x_861_);
if (lean_obj_tag(v___y_843_) == 0)
{
lean_object* v_quotContext_863_; lean_object* v_currMacroScope_864_; lean_object* v_ref_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_quotContext_863_ = lean_ctor_get(v___y_855_, 1);
v_currMacroScope_864_ = lean_ctor_get(v___y_855_, 2);
v_ref_865_ = lean_ctor_get(v___y_855_, 5);
v___x_866_ = l_Lean_SourceInfo_fromRef(v_ref_865_, v___y_845_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__90));
v___x_868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__91));
lean_inc(v___x_866_);
v___x_869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_866_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
v___x_870_ = l_Lean_Syntax_node1(v___x_866_, v___x_868_, v___x_869_);
v___y_645_ = v___y_841_;
v___y_646_ = v___y_842_;
v___y_647_ = v___y_844_;
v___y_648_ = v___y_845_;
v___y_649_ = v___y_846_;
v___y_650_ = v___y_847_;
v___y_651_ = v___x_861_;
v___y_652_ = v___y_848_;
v___y_653_ = v___y_849_;
v___y_654_ = v___y_850_;
v___y_655_ = v___y_851_;
v___y_656_ = v___x_862_;
v___y_657_ = v___y_852_;
v___y_658_ = v___y_853_;
v___y_659_ = v___y_854_;
v___y_660_ = v___y_856_;
v___y_661_ = v___y_858_;
v___y_662_ = v___y_859_;
v_specTac_663_ = v___x_870_;
v_quotContext_664_ = v_quotContext_863_;
v_currMacroScope_665_ = v_currMacroScope_864_;
v_ref_666_ = v_ref_865_;
v___y_667_ = v___y_857_;
goto v___jp_644_;
}
else
{
lean_object* v_val_871_; lean_object* v_quotContext_872_; lean_object* v_currMacroScope_873_; lean_object* v_ref_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_val_871_ = lean_ctor_get(v___y_843_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v___y_843_, 1);
v_quotContext_872_ = lean_ctor_get(v___y_855_, 1);
v_currMacroScope_873_ = lean_ctor_get(v___y_855_, 2);
v_ref_874_ = lean_ctor_get(v___y_855_, 5);
v___x_875_ = l_Lean_SourceInfo_fromRef(v_ref_874_, v___y_845_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__92));
v___x_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__65));
lean_inc_n(v___x_875_, 2);
v___x_878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_875_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__77));
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_875_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_Syntax_node3(v___x_875_, v___x_876_, v___x_878_, v_val_871_, v___x_880_);
v___y_645_ = v___y_841_;
v___y_646_ = v___y_842_;
v___y_647_ = v___y_844_;
v___y_648_ = v___y_845_;
v___y_649_ = v___y_846_;
v___y_650_ = v___y_847_;
v___y_651_ = v___x_861_;
v___y_652_ = v___y_848_;
v___y_653_ = v___y_849_;
v___y_654_ = v___y_850_;
v___y_655_ = v___y_851_;
v___y_656_ = v___x_862_;
v___y_657_ = v___y_852_;
v___y_658_ = v___y_853_;
v___y_659_ = v___y_854_;
v___y_660_ = v___y_856_;
v___y_661_ = v___y_858_;
v___y_662_ = v___y_859_;
v_specTac_663_ = v___x_881_;
v_quotContext_664_ = v_quotContext_872_;
v_currMacroScope_665_ = v_currMacroScope_873_;
v_ref_666_ = v_ref_874_;
v___y_667_ = v___y_857_;
goto v___jp_644_;
}
}
v___jp_882_:
{
lean_object* v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__93));
v___x_904_ = 1;
v___x_905_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_894_, v___x_904_);
v___x_906_ = lean_string_append(v___x_903_, v___x_905_);
lean_dec_ref(v___x_905_);
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__94));
v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
v___y_841_ = v___y_883_;
v___y_842_ = v___y_884_;
v___y_843_ = v___y_885_;
v___y_844_ = v___y_886_;
v___y_845_ = v___y_887_;
v___y_846_ = v___y_888_;
v___y_847_ = v___y_889_;
v___y_848_ = v___y_890_;
v___y_849_ = v___y_891_;
v___y_850_ = v___y_892_;
v___y_851_ = v___y_893_;
v___y_852_ = v___y_895_;
v___y_853_ = v___y_897_;
v___y_854_ = v___y_896_;
v___y_855_ = v___y_899_;
v___y_856_ = v___y_898_;
v___y_857_ = v___y_901_;
v___y_858_ = v___y_900_;
v___y_859_ = v___y_902_;
v___y_860_ = v___x_908_;
goto v___jp_840_;
}
v___jp_909_:
{
if (lean_obj_tag(v___y_912_) == 0)
{
if (v___y_914_ == 0)
{
lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_930_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__93));
v___x_931_ = 1;
v___x_932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_921_, v___x_931_);
v___x_933_ = lean_string_append(v___x_930_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__95));
v___x_935_ = lean_string_append(v___x_933_, v___x_934_);
v___y_841_ = v___y_910_;
v___y_842_ = v___y_911_;
v___y_843_ = v___y_912_;
v___y_844_ = v___y_913_;
v___y_845_ = v___y_914_;
v___y_846_ = v___y_915_;
v___y_847_ = v___y_916_;
v___y_848_ = v___y_917_;
v___y_849_ = v___y_918_;
v___y_850_ = v___y_919_;
v___y_851_ = v___y_920_;
v___y_852_ = v___y_922_;
v___y_853_ = v_post_927_;
v___y_854_ = v___y_923_;
v___y_855_ = v___y_928_;
v___y_856_ = v___y_924_;
v___y_857_ = v___y_929_;
v___y_858_ = v___y_925_;
v___y_859_ = v___y_926_;
v___y_860_ = v___x_935_;
goto v___jp_840_;
}
else
{
v___y_883_ = v___y_910_;
v___y_884_ = v___y_911_;
v___y_885_ = v___y_912_;
v___y_886_ = v___y_913_;
v___y_887_ = v___y_914_;
v___y_888_ = v___y_915_;
v___y_889_ = v___y_916_;
v___y_890_ = v___y_917_;
v___y_891_ = v___y_918_;
v___y_892_ = v___y_919_;
v___y_893_ = v___y_920_;
v___y_894_ = v___y_921_;
v___y_895_ = v___y_922_;
v___y_896_ = v___y_923_;
v___y_897_ = v_post_927_;
v___y_898_ = v___y_924_;
v___y_899_ = v___y_928_;
v___y_900_ = v___y_925_;
v___y_901_ = v___y_929_;
v___y_902_ = v___y_926_;
goto v___jp_882_;
}
}
else
{
v___y_883_ = v___y_910_;
v___y_884_ = v___y_911_;
v___y_885_ = v___y_912_;
v___y_886_ = v___y_913_;
v___y_887_ = v___y_914_;
v___y_888_ = v___y_915_;
v___y_889_ = v___y_916_;
v___y_890_ = v___y_917_;
v___y_891_ = v___y_918_;
v___y_892_ = v___y_919_;
v___y_893_ = v___y_920_;
v___y_894_ = v___y_921_;
v___y_895_ = v___y_922_;
v___y_896_ = v___y_923_;
v___y_897_ = v_post_927_;
v___y_898_ = v___y_924_;
v___y_899_ = v___y_928_;
v___y_900_ = v___y_925_;
v___y_901_ = v___y_929_;
v___y_902_ = v___y_926_;
goto v___jp_882_;
}
}
v___jp_937_:
{
uint8_t v___x_958_; 
v___x_958_ = l_Lean_Syntax_isNone(v___y_943_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_959_ = l_Lean_Syntax_getArg(v___y_943_, v___y_945_);
lean_dec(v___y_943_);
v___x_960_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__97));
lean_inc(v___x_959_);
v___x_961_ = l_Lean_Syntax_isOfKind(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v___x_959_);
v___x_962_ = l_Lean_Macro_throwUnsupported___redArg(v___y_957_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v_a_964_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
v_a_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_962_, 2);
v___y_910_ = v___y_938_;
v___y_911_ = v_pre_955_;
v___y_912_ = v___y_939_;
v___y_913_ = v___y_940_;
v___y_914_ = v___y_941_;
v___y_915_ = v___y_942_;
v___y_916_ = v___y_944_;
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_947_;
v___y_920_ = v___y_948_;
v___y_921_ = v___y_949_;
v___y_922_ = v___y_950_;
v___y_923_ = v___y_951_;
v___y_924_ = v___y_952_;
v___y_925_ = v___y_953_;
v___y_926_ = v___y_954_;
v_post_927_ = v_a_963_;
v___y_928_ = v___y_956_;
v___y_929_ = v_a_964_;
goto v___jp_909_;
}
else
{
lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_pre_955_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
lean_dec(v___y_944_);
lean_dec(v___y_940_);
lean_dec(v___y_939_);
v_a_965_ = lean_ctor_get(v___x_962_, 0);
v_a_966_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_962_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_inc(v_a_965_);
lean_dec(v___x_962_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_965_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = l_Lean_Syntax_getArg(v___x_959_, v___x_936_);
lean_dec(v___x_959_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
lean_inc(v___x_974_);
v___x_976_ = l_Lean_Syntax_isOfKind(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__101));
lean_inc(v___x_974_);
v___x_978_ = l_Lean_Syntax_isOfKind(v___x_974_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec(v___x_974_);
v___x_979_ = l_Lean_Macro_throwUnsupported___redArg(v___y_957_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v_a_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
v_a_981_ = lean_ctor_get(v___x_979_, 1);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_979_, 2);
v___y_910_ = v___y_938_;
v___y_911_ = v_pre_955_;
v___y_912_ = v___y_939_;
v___y_913_ = v___y_940_;
v___y_914_ = v___y_941_;
v___y_915_ = v___y_942_;
v___y_916_ = v___y_944_;
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_947_;
v___y_920_ = v___y_948_;
v___y_921_ = v___y_949_;
v___y_922_ = v___y_950_;
v___y_923_ = v___y_951_;
v___y_924_ = v___y_952_;
v___y_925_ = v___y_953_;
v___y_926_ = v___y_954_;
v_post_927_ = v_a_980_;
v___y_928_ = v___y_956_;
v___y_929_ = v_a_981_;
goto v___jp_909_;
}
else
{
lean_object* v_a_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_pre_955_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
lean_dec(v___y_944_);
lean_dec(v___y_940_);
lean_dec(v___y_939_);
v_a_982_ = lean_ctor_get(v___x_979_, 0);
v_a_983_ = lean_ctor_get(v___x_979_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_979_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_inc(v_a_982_);
lean_dec(v___x_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_982_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_ref_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_ref_991_ = lean_ctor_get(v___y_956_, 5);
v___x_992_ = l_Lean_SourceInfo_fromRef(v_ref_991_, v___x_976_);
v___x_993_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_994_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_992_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_992_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
v___x_996_ = l_Lean_Syntax_node2(v___x_992_, v___x_994_, v___x_995_, v___x_974_);
v___y_910_ = v___y_938_;
v___y_911_ = v_pre_955_;
v___y_912_ = v___y_939_;
v___y_913_ = v___y_940_;
v___y_914_ = v___y_941_;
v___y_915_ = v___y_942_;
v___y_916_ = v___y_944_;
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_947_;
v___y_920_ = v___y_948_;
v___y_921_ = v___y_949_;
v___y_922_ = v___y_950_;
v___y_923_ = v___y_951_;
v___y_924_ = v___y_952_;
v___y_925_ = v___y_953_;
v___y_926_ = v___y_954_;
v_post_927_ = v___x_996_;
v___y_928_ = v___y_956_;
v___y_929_ = v___y_957_;
goto v___jp_909_;
}
}
else
{
lean_object* v_ref_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_ref_997_ = lean_ctor_get(v___y_956_, 5);
v___x_998_ = l_Lean_SourceInfo_fromRef(v_ref_997_, v___x_958_);
v___x_999_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_998_);
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_998_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
v___x_1002_ = l_Lean_Syntax_node2(v___x_998_, v___x_1000_, v___x_1001_, v___x_974_);
v___y_910_ = v___y_938_;
v___y_911_ = v_pre_955_;
v___y_912_ = v___y_939_;
v___y_913_ = v___y_940_;
v___y_914_ = v___y_941_;
v___y_915_ = v___y_942_;
v___y_916_ = v___y_944_;
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_947_;
v___y_920_ = v___y_948_;
v___y_921_ = v___y_949_;
v___y_922_ = v___y_950_;
v___y_923_ = v___y_951_;
v___y_924_ = v___y_952_;
v___y_925_ = v___y_953_;
v___y_926_ = v___y_954_;
v_post_927_ = v___x_1002_;
v___y_928_ = v___y_956_;
v___y_929_ = v___y_957_;
goto v___jp_909_;
}
}
}
else
{
lean_object* v_ref_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v___y_943_);
v_ref_1003_ = lean_ctor_get(v___y_956_, 5);
v___x_1004_ = l_Lean_SourceInfo_fromRef(v_ref_1003_, v___y_941_);
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc_n(v___x_1004_, 9);
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1004_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
v___x_1009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__105));
v___x_1011_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__106));
v___x_1012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1004_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_Syntax_node1(v___x_1004_, v___x_1010_, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node1(v___x_1004_, v___x_1009_, v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__19, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__19_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__19);
v___x_1016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1004_);
lean_ctor_set(v___x_1016_, 1, v___x_1009_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__107));
v___x_1018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1004_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__109));
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__110));
v___x_1021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1004_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_node1(v___x_1004_, v___x_1019_, v___x_1021_);
v___x_1023_ = l_Lean_Syntax_node4(v___x_1004_, v___x_1008_, v___x_1014_, v___x_1016_, v___x_1018_, v___x_1022_);
v___x_1024_ = l_Lean_Syntax_node2(v___x_1004_, v___x_1006_, v___x_1007_, v___x_1023_);
v___y_910_ = v___y_938_;
v___y_911_ = v_pre_955_;
v___y_912_ = v___y_939_;
v___y_913_ = v___y_940_;
v___y_914_ = v___y_941_;
v___y_915_ = v___y_942_;
v___y_916_ = v___y_944_;
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_947_;
v___y_920_ = v___y_948_;
v___y_921_ = v___y_949_;
v___y_922_ = v___y_950_;
v___y_923_ = v___y_951_;
v___y_924_ = v___y_952_;
v___y_925_ = v___y_953_;
v___y_926_ = v___y_954_;
v_post_927_ = v___x_1024_;
v___y_928_ = v___y_956_;
v___y_929_ = v___y_957_;
goto v___jp_909_;
}
}
v___jp_1025_:
{
uint8_t v___x_1046_; 
v___x_1046_ = l_Lean_Syntax_isNone(v___y_1035_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = l_Lean_Syntax_getArg(v___y_1035_, v___y_1033_);
lean_dec(v___y_1035_);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__112));
lean_inc(v___x_1047_);
v___x_1049_ = l_Lean_Syntax_isOfKind(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec(v___x_1047_);
v___x_1050_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1039_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v_a_1052_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
v_a_1052_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1050_, 2);
v___y_938_ = v___y_1026_;
v___y_939_ = v___y_1027_;
v___y_940_ = v___y_1028_;
v___y_941_ = v___y_1029_;
v___y_942_ = v___y_1030_;
v___y_943_ = v___y_1031_;
v___y_944_ = v___y_1032_;
v___y_945_ = v___y_1033_;
v___y_946_ = v___y_1034_;
v___y_947_ = v___y_1036_;
v___y_948_ = v___y_1037_;
v___y_949_ = v___y_1040_;
v___y_950_ = v___y_1041_;
v___y_951_ = v___y_1042_;
v___y_952_ = v___y_1043_;
v___y_953_ = v___y_1045_;
v___y_954_ = v___y_1044_;
v_pre_955_ = v_a_1051_;
v___y_956_ = v___y_1038_;
v___y_957_ = v_a_1052_;
goto v___jp_937_;
}
else
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v___y_1045_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1036_);
lean_dec(v___y_1034_);
lean_dec(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec(v___y_1028_);
lean_dec(v___y_1027_);
v_a_1053_ = lean_ctor_get(v___x_1050_, 0);
v_a_1054_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1050_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_inc(v_a_1053_);
lean_dec(v___x_1050_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1053_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = l_Lean_Syntax_getArg(v___x_1047_, v___x_936_);
lean_dec(v___x_1047_);
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
lean_inc(v___x_1062_);
v___x_1064_ = l_Lean_Syntax_isOfKind(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
v___y_938_ = v___y_1026_;
v___y_939_ = v___y_1027_;
v___y_940_ = v___y_1028_;
v___y_941_ = v___y_1029_;
v___y_942_ = v___y_1030_;
v___y_943_ = v___y_1031_;
v___y_944_ = v___y_1032_;
v___y_945_ = v___y_1033_;
v___y_946_ = v___y_1034_;
v___y_947_ = v___y_1036_;
v___y_948_ = v___y_1037_;
v___y_949_ = v___y_1040_;
v___y_950_ = v___y_1041_;
v___y_951_ = v___y_1042_;
v___y_952_ = v___y_1043_;
v___y_953_ = v___y_1045_;
v___y_954_ = v___y_1044_;
v_pre_955_ = v___x_1062_;
v___y_956_ = v___y_1038_;
v___y_957_ = v___y_1039_;
goto v___jp_937_;
}
else
{
lean_object* v_ref_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_ref_1065_ = lean_ctor_get(v___y_1038_, 5);
v___x_1066_ = l_Lean_SourceInfo_fromRef(v_ref_1065_, v___x_1046_);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_1066_);
v___x_1069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1066_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
v___x_1070_ = l_Lean_Syntax_node2(v___x_1066_, v___x_1068_, v___x_1069_, v___x_1062_);
v___y_938_ = v___y_1026_;
v___y_939_ = v___y_1027_;
v___y_940_ = v___y_1028_;
v___y_941_ = v___y_1029_;
v___y_942_ = v___y_1030_;
v___y_943_ = v___y_1031_;
v___y_944_ = v___y_1032_;
v___y_945_ = v___y_1033_;
v___y_946_ = v___y_1034_;
v___y_947_ = v___y_1036_;
v___y_948_ = v___y_1037_;
v___y_949_ = v___y_1040_;
v___y_950_ = v___y_1041_;
v___y_951_ = v___y_1042_;
v___y_952_ = v___y_1043_;
v___y_953_ = v___y_1045_;
v___y_954_ = v___y_1044_;
v_pre_955_ = v___x_1070_;
v___y_956_ = v___y_1038_;
v___y_957_ = v___y_1039_;
goto v___jp_937_;
}
}
}
else
{
lean_object* v_ref_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v___y_1035_);
v_ref_1071_ = lean_ctor_get(v___y_1038_, 5);
v___x_1072_ = l_Lean_SourceInfo_fromRef(v_ref_1071_, v___y_1029_);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__109));
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__110));
lean_inc(v___x_1072_);
v___x_1075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1072_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1073_, v___x_1075_);
v___y_938_ = v___y_1026_;
v___y_939_ = v___y_1027_;
v___y_940_ = v___y_1028_;
v___y_941_ = v___y_1029_;
v___y_942_ = v___y_1030_;
v___y_943_ = v___y_1031_;
v___y_944_ = v___y_1032_;
v___y_945_ = v___y_1033_;
v___y_946_ = v___y_1034_;
v___y_947_ = v___y_1036_;
v___y_948_ = v___y_1037_;
v___y_949_ = v___y_1040_;
v___y_950_ = v___y_1041_;
v___y_951_ = v___y_1042_;
v___y_952_ = v___y_1043_;
v___y_953_ = v___y_1045_;
v___y_954_ = v___y_1044_;
v_pre_955_ = v___x_1076_;
v___y_956_ = v___y_1038_;
v___y_957_ = v___y_1039_;
goto v___jp_937_;
}
}
v___jp_1077_:
{
lean_object* v___x_1097_; size_t v_sz_1098_; size_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
lean_inc_ref(v___y_1089_);
v___x_1097_ = l_Array_append___redArg(v___y_1089_, v___y_1096_);
lean_dec_ref(v___y_1096_);
v_sz_1098_ = lean_array_size(v___x_1097_);
v___x_1099_ = ((size_t)0ULL);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_1098_, v___x_1099_, v___x_1097_);
v___x_1101_ = lean_mk_empty_array_with_capacity(v___y_1085_);
v___x_1102_ = lean_array_get_size(v___y_1089_);
v___x_1103_ = lean_nat_dec_lt(v___y_1085_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v___y_1089_);
v___y_1026_ = v___y_1078_;
v___y_1027_ = v___y_1079_;
v___y_1028_ = v___y_1080_;
v___y_1029_ = v___y_1081_;
v___y_1030_ = v___y_1082_;
v___y_1031_ = v___y_1083_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
v___y_1036_ = v___y_1088_;
v___y_1037_ = v___y_1090_;
v___y_1038_ = v___y_1092_;
v___y_1039_ = v___y_1091_;
v___y_1040_ = v___y_1093_;
v___y_1041_ = v___x_1100_;
v___y_1042_ = v___y_1094_;
v___y_1043_ = v___x_1099_;
v___y_1044_ = v___y_1095_;
v___y_1045_ = v___x_1101_;
goto v___jp_1025_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_nat_dec_le(v___x_1102_, v___x_1102_);
if (v___x_1104_ == 0)
{
if (v___x_1103_ == 0)
{
lean_dec_ref(v___y_1089_);
v___y_1026_ = v___y_1078_;
v___y_1027_ = v___y_1079_;
v___y_1028_ = v___y_1080_;
v___y_1029_ = v___y_1081_;
v___y_1030_ = v___y_1082_;
v___y_1031_ = v___y_1083_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
v___y_1036_ = v___y_1088_;
v___y_1037_ = v___y_1090_;
v___y_1038_ = v___y_1092_;
v___y_1039_ = v___y_1091_;
v___y_1040_ = v___y_1093_;
v___y_1041_ = v___x_1100_;
v___y_1042_ = v___y_1094_;
v___y_1043_ = v___x_1099_;
v___y_1044_ = v___y_1095_;
v___y_1045_ = v___x_1101_;
goto v___jp_1025_;
}
else
{
size_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_usize_of_nat(v___x_1102_);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___y_1089_, v___x_1099_, v___x_1105_, v___x_1101_);
lean_dec_ref(v___y_1089_);
v___y_1026_ = v___y_1078_;
v___y_1027_ = v___y_1079_;
v___y_1028_ = v___y_1080_;
v___y_1029_ = v___y_1081_;
v___y_1030_ = v___y_1082_;
v___y_1031_ = v___y_1083_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
v___y_1036_ = v___y_1088_;
v___y_1037_ = v___y_1090_;
v___y_1038_ = v___y_1092_;
v___y_1039_ = v___y_1091_;
v___y_1040_ = v___y_1093_;
v___y_1041_ = v___x_1100_;
v___y_1042_ = v___y_1094_;
v___y_1043_ = v___x_1099_;
v___y_1044_ = v___y_1095_;
v___y_1045_ = v___x_1106_;
goto v___jp_1025_;
}
}
else
{
size_t v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_usize_of_nat(v___x_1102_);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___y_1089_, v___x_1099_, v___x_1107_, v___x_1101_);
lean_dec_ref(v___y_1089_);
v___y_1026_ = v___y_1078_;
v___y_1027_ = v___y_1079_;
v___y_1028_ = v___y_1080_;
v___y_1029_ = v___y_1081_;
v___y_1030_ = v___y_1082_;
v___y_1031_ = v___y_1083_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v___y_1086_;
v___y_1035_ = v___y_1087_;
v___y_1036_ = v___y_1088_;
v___y_1037_ = v___y_1090_;
v___y_1038_ = v___y_1092_;
v___y_1039_ = v___y_1091_;
v___y_1040_ = v___y_1093_;
v___y_1041_ = v___x_1100_;
v___y_1042_ = v___y_1094_;
v___y_1043_ = v___x_1099_;
v___y_1044_ = v___y_1095_;
v___y_1045_ = v___x_1108_;
goto v___jp_1025_;
}
}
}
v___jp_1110_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1126_ = l_Lean_Syntax_getArg(v_decl_1109_, v___y_1121_);
v___x_1127_ = l_Lean_Syntax_getArg(v_decl_1109_, v___x_936_);
lean_dec(v_decl_1109_);
v___x_1128_ = l_Lean_Syntax_getArg(v___x_1127_, v___y_1118_);
lean_dec(v___x_1127_);
v___x_1129_ = l_Lean_TSyntax_getId(v___x_1128_);
v___x_1130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0));
v___x_1131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
lean_inc(v___x_1129_);
v___x_1132_ = l_Lean_Name_append(v___x_1129_, v___x_1131_);
v___x_1133_ = l_Lean_mkIdentFrom(v___x_1128_, v___x_1132_, v___y_1114_);
v___x_1134_ = l_Lean_Syntax_getArg(v___x_1126_, v___y_1118_);
lean_dec(v___x_1126_);
v___x_1135_ = l_Lean_Syntax_getArgs(v___x_1134_);
lean_dec(v___x_1134_);
if (v___y_1122_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = l_Lean_Syntax_getArg(v___y_1113_, v___y_1118_);
lean_dec(v___y_1113_);
v___x_1137_ = l_Lean_Syntax_getArg(v___x_1136_, v___x_936_);
lean_dec(v___x_1136_);
v___x_1138_ = l_Lean_Syntax_getArgs(v___x_1137_);
lean_dec(v___x_1137_);
v___y_1078_ = v___y_1111_;
v___y_1079_ = v___y_1112_;
v___y_1080_ = v___x_1128_;
v___y_1081_ = v___y_1114_;
v___y_1082_ = v___y_1115_;
v___y_1083_ = v___y_1116_;
v___y_1084_ = v___y_1117_;
v___y_1085_ = v___y_1118_;
v___y_1086_ = v___y_1119_;
v___y_1087_ = v___y_1120_;
v___y_1088_ = v___x_1133_;
v___y_1089_ = v___x_1135_;
v___y_1090_ = v___y_1121_;
v___y_1091_ = v___y_1125_;
v___y_1092_ = v___y_1124_;
v___y_1093_ = v___x_1129_;
v___y_1094_ = v___x_1130_;
v___y_1095_ = v___y_1123_;
v___y_1096_ = v___x_1138_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1139_; 
lean_dec(v___y_1113_);
v___x_1139_ = lean_mk_empty_array_with_capacity(v___y_1118_);
v___y_1078_ = v___y_1111_;
v___y_1079_ = v___y_1112_;
v___y_1080_ = v___x_1128_;
v___y_1081_ = v___y_1114_;
v___y_1082_ = v___y_1115_;
v___y_1083_ = v___y_1116_;
v___y_1084_ = v___y_1117_;
v___y_1085_ = v___y_1118_;
v___y_1086_ = v___y_1119_;
v___y_1087_ = v___y_1120_;
v___y_1088_ = v___x_1133_;
v___y_1089_ = v___x_1135_;
v___y_1090_ = v___y_1121_;
v___y_1091_ = v___y_1125_;
v___y_1092_ = v___y_1124_;
v___y_1093_ = v___x_1129_;
v___y_1094_ = v___x_1130_;
v___y_1095_ = v___y_1123_;
v___y_1096_ = v___x_1139_;
goto v___jp_1077_;
}
}
v___jp_1140_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__113));
v___x_1158_ = l_Lean_Macro_throwErrorAt___redArg(v___y_1156_, v___x_1157_, v___y_1153_, v___y_1142_);
lean_dec(v___y_1156_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 1);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 2);
v___y_1111_ = v___y_1141_;
v___y_1112_ = v___y_1143_;
v___y_1113_ = v___y_1144_;
v___y_1114_ = v___y_1145_;
v___y_1115_ = v___y_1146_;
v___y_1116_ = v___y_1147_;
v___y_1117_ = v___y_1148_;
v___y_1118_ = v___y_1149_;
v___y_1119_ = v___y_1150_;
v___y_1120_ = v___y_1151_;
v___y_1121_ = v___y_1152_;
v___y_1122_ = v___y_1154_;
v___y_1123_ = v___y_1155_;
v___y_1124_ = v___y_1153_;
v___y_1125_ = v_a_1159_;
goto v___jp_1110_;
}
else
{
lean_object* v_a_1160_; lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec(v_decl_1109_);
v_a_1160_ = lean_ctor_get(v___x_1158_, 0);
v_a_1161_ = lean_ctor_get(v___x_1158_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1158_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_inc(v_a_1160_);
lean_dec(v___x_1158_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1160_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
v___jp_1169_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = l_Lean_Syntax_getArg(v___y_1177_, v___y_1179_);
v___x_1182_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v___x_1181_, v___y_1175_, v___y_1172_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v_a_1184_; lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
v_a_1184_ = lean_ctor_get(v___x_1182_, 1);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1182_, 2);
v_fst_1185_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_fst_1185_);
v_snd_1186_ = lean_ctor_get(v_a_1183_, 1);
lean_inc(v_snd_1186_);
lean_dec(v_a_1183_);
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__114));
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__115));
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__117));
v___x_1190_ = l_Lean_Macro_hasDecl(v___x_1189_, v___y_1175_, v_a_1184_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
v_a_1192_ = lean_ctor_get(v___x_1190_, 1);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1190_, 2);
lean_inc(v_decl_1109_);
v___x_1193_ = l_Lean_Syntax_setArg(v_decl_1109_, v___y_1179_, v_snd_1186_);
v___x_1194_ = l_Lean_Syntax_setArg(v_stx_641_, v___x_936_, v___x_1193_);
v___x_1195_ = lean_unbox(v_a_1191_);
lean_dec(v_a_1191_);
if (v___x_1195_ == 0)
{
if (v___y_1176_ == 0)
{
lean_inc(v___y_1170_);
v___y_1141_ = v___x_1187_;
v___y_1142_ = v_a_1192_;
v___y_1143_ = v_fst_1185_;
v___y_1144_ = v___y_1170_;
v___y_1145_ = v___y_1180_;
v___y_1146_ = v___x_1188_;
v___y_1147_ = v___y_1173_;
v___y_1148_ = v___x_1194_;
v___y_1149_ = v___y_1174_;
v___y_1150_ = v___y_1177_;
v___y_1151_ = v___y_1178_;
v___y_1152_ = v___y_1171_;
v___y_1153_ = v___y_1175_;
v___y_1154_ = v___y_1176_;
v___y_1155_ = v___y_1179_;
v___y_1156_ = v___y_1170_;
goto v___jp_1140_;
}
else
{
uint8_t v___x_1196_; 
v___x_1196_ = l_Lean_Syntax_isNone(v___y_1178_);
if (v___x_1196_ == 0)
{
lean_inc(v___y_1178_);
v___y_1141_ = v___x_1187_;
v___y_1142_ = v_a_1192_;
v___y_1143_ = v_fst_1185_;
v___y_1144_ = v___y_1170_;
v___y_1145_ = v___y_1180_;
v___y_1146_ = v___x_1188_;
v___y_1147_ = v___y_1173_;
v___y_1148_ = v___x_1194_;
v___y_1149_ = v___y_1174_;
v___y_1150_ = v___y_1177_;
v___y_1151_ = v___y_1178_;
v___y_1152_ = v___y_1171_;
v___y_1153_ = v___y_1175_;
v___y_1154_ = v___y_1176_;
v___y_1155_ = v___y_1179_;
v___y_1156_ = v___y_1178_;
goto v___jp_1140_;
}
else
{
lean_inc(v___y_1173_);
v___y_1141_ = v___x_1187_;
v___y_1142_ = v_a_1192_;
v___y_1143_ = v_fst_1185_;
v___y_1144_ = v___y_1170_;
v___y_1145_ = v___y_1180_;
v___y_1146_ = v___x_1188_;
v___y_1147_ = v___y_1173_;
v___y_1148_ = v___x_1194_;
v___y_1149_ = v___y_1174_;
v___y_1150_ = v___y_1177_;
v___y_1151_ = v___y_1178_;
v___y_1152_ = v___y_1171_;
v___y_1153_ = v___y_1175_;
v___y_1154_ = v___y_1176_;
v___y_1155_ = v___y_1179_;
v___y_1156_ = v___y_1173_;
goto v___jp_1140_;
}
}
}
else
{
v___y_1111_ = v___x_1187_;
v___y_1112_ = v_fst_1185_;
v___y_1113_ = v___y_1170_;
v___y_1114_ = v___y_1180_;
v___y_1115_ = v___x_1188_;
v___y_1116_ = v___y_1173_;
v___y_1117_ = v___x_1194_;
v___y_1118_ = v___y_1174_;
v___y_1119_ = v___y_1177_;
v___y_1120_ = v___y_1178_;
v___y_1121_ = v___y_1171_;
v___y_1122_ = v___y_1176_;
v___y_1123_ = v___y_1179_;
v___y_1124_ = v___y_1175_;
v___y_1125_ = v_a_1192_;
goto v___jp_1110_;
}
}
else
{
lean_object* v_a_1197_; lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v_snd_1186_);
lean_dec(v_fst_1185_);
lean_dec(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec(v___y_1173_);
lean_dec(v___y_1170_);
lean_dec(v_decl_1109_);
lean_dec(v_stx_641_);
v_a_1197_ = lean_ctor_get(v___x_1190_, 0);
v_a_1198_ = lean_ctor_get(v___x_1190_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1190_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_inc(v_a_1197_);
lean_dec(v___x_1190_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1197_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec(v___y_1173_);
lean_dec(v___y_1170_);
lean_dec(v_decl_1109_);
lean_dec(v_stx_641_);
v_a_1206_ = lean_ctor_get(v___x_1182_, 0);
v_a_1207_ = lean_ctor_get(v___x_1182_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1182_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_inc(v_a_1206_);
lean_dec(v___x_1182_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1206_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
v___jp_1215_:
{
if (v___y_1226_ == 0)
{
v___y_1170_ = v___y_1216_;
v___y_1171_ = v___y_1217_;
v___y_1172_ = v___y_1218_;
v___y_1173_ = v___y_1219_;
v___y_1174_ = v___y_1221_;
v___y_1175_ = v___y_1220_;
v___y_1176_ = v___y_1222_;
v___y_1177_ = v___y_1223_;
v___y_1178_ = v___y_1224_;
v___y_1179_ = v___y_1225_;
v___y_1180_ = v___y_1226_;
goto v___jp_1169_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Lean_Syntax_isNone(v___y_1219_);
if (v___x_1227_ == 0)
{
v___y_1170_ = v___y_1216_;
v___y_1171_ = v___y_1217_;
v___y_1172_ = v___y_1218_;
v___y_1173_ = v___y_1219_;
v___y_1174_ = v___y_1221_;
v___y_1175_ = v___y_1220_;
v___y_1176_ = v___y_1222_;
v___y_1177_ = v___y_1223_;
v___y_1178_ = v___y_1224_;
v___y_1179_ = v___y_1225_;
v___y_1180_ = v___x_1227_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v___y_1224_);
lean_dec(v___y_1219_);
lean_dec(v___y_1216_);
v___x_1228_ = l_Lean_Syntax_getArg(v___y_1223_, v___y_1225_);
lean_dec(v___y_1223_);
v___x_1229_ = l_Lean_Syntax_setArg(v_decl_1109_, v___y_1225_, v___x_1228_);
v___x_1230_ = l_Lean_Syntax_setArg(v_stx_641_, v___x_936_, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___y_1218_);
return v___x_1231_;
}
}
}
v___jp_1232_:
{
lean_object* v___x_1237_; lean_object* v_givenStx_1238_; lean_object* v_requiresStx_1239_; lean_object* v___x_1240_; lean_object* v_ensuresStx_1241_; uint8_t v___x_1242_; 
v___x_1237_ = lean_unsigned_to_nat(0u);
v_givenStx_1238_ = l_Lean_Syntax_getArg(v___y_1233_, v___x_1237_);
v_requiresStx_1239_ = l_Lean_Syntax_getArg(v___y_1233_, v___x_936_);
v___x_1240_ = lean_unsigned_to_nat(2u);
v_ensuresStx_1241_ = l_Lean_Syntax_getArg(v___y_1233_, v___x_1240_);
v___x_1242_ = l_Lean_Syntax_isNone(v_givenStx_1238_);
if (v___x_1242_ == 0)
{
v___y_1216_ = v_givenStx_1238_;
v___y_1217_ = v___x_1240_;
v___y_1218_ = v___y_1236_;
v___y_1219_ = v_ensuresStx_1241_;
v___y_1220_ = v___y_1235_;
v___y_1221_ = v___x_1237_;
v___y_1222_ = v___x_1242_;
v___y_1223_ = v___y_1233_;
v___y_1224_ = v_requiresStx_1239_;
v___y_1225_ = v___y_1234_;
v___y_1226_ = v___x_1242_;
goto v___jp_1215_;
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Lean_Syntax_isNone(v_requiresStx_1239_);
v___y_1216_ = v_givenStx_1238_;
v___y_1217_ = v___x_1240_;
v___y_1218_ = v___y_1236_;
v___y_1219_ = v_ensuresStx_1241_;
v___y_1220_ = v___y_1235_;
v___y_1221_ = v___x_1237_;
v___y_1222_ = v___x_1242_;
v___y_1223_ = v___y_1233_;
v___y_1224_ = v_requiresStx_1239_;
v___y_1225_ = v___y_1234_;
v___y_1226_ = v___x_1243_;
goto v___jp_1215_;
}
}
v___jp_1244_:
{
lean_object* v___x_1247_; lean_object* v_val_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1247_ = lean_unsigned_to_nat(3u);
v_val_1248_ = l_Lean_Syntax_getArg(v_decl_1109_, v___x_1247_);
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
lean_inc(v_val_1248_);
v___x_1250_ = l_Lean_Syntax_isOfKind(v_val_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1246_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 2);
v___y_1233_ = v_val_1248_;
v___y_1234_ = v___x_1247_;
v___y_1235_ = v___y_1245_;
v___y_1236_ = v_a_1252_;
goto v___jp_1232_;
}
else
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_val_1248_);
lean_dec(v_decl_1109_);
lean_dec(v_stx_641_);
v_a_1253_ = lean_ctor_get(v___x_1251_, 0);
v_a_1254_ = lean_ctor_get(v___x_1251_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1251_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_inc(v_a_1253_);
lean_dec(v___x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
v___y_1233_ = v_val_1248_;
v___y_1234_ = v___x_1247_;
v___y_1235_ = v___y_1245_;
v___y_1236_ = v___y_1246_;
goto v___jp_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___boxed(lean_object* v_stx_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Elab_Tactic_Do_expandDefContract(v_stx_1275_, v_a_1276_, v_a_1277_);
lean_dec_ref(v_a_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1(){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1289_ = l_Lean_Elab_macroAttribute;
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_1291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3));
v___x_1292_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_expandDefContract___boxed), 3, 0);
v___x_1293_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1289_, v___x_1290_, v___x_1291_, v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___boxed(lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3(){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__3));
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0));
v___x_1300_ = l_Lean_addBuiltinDocString(v___x_1298_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
return v_res_1302_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t v___y_1304_, uint8_t v_suppressElabErrors_1305_, lean_object* v_x_1306_){
_start:
{
if (lean_obj_tag(v_x_1306_) == 1)
{
lean_object* v_pre_1307_; 
v_pre_1307_ = lean_ctor_get(v_x_1306_, 0);
if (lean_obj_tag(v_pre_1307_) == 0)
{
lean_object* v_str_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_str_1308_ = lean_ctor_get(v_x_1306_, 1);
v___x_1309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_1310_ = lean_string_dec_eq(v_str_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
return v___y_1304_;
}
else
{
return v_suppressElabErrors_1305_;
}
}
else
{
return v___y_1304_;
}
}
else
{
return v___y_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object* v___y_1311_, lean_object* v_suppressElabErrors_1312_, lean_object* v_x_1313_){
_start:
{
uint8_t v___y_3210__boxed_1314_; uint8_t v_suppressElabErrors_boxed_1315_; uint8_t v_res_1316_; lean_object* v_r_1317_; 
v___y_3210__boxed_1314_ = lean_unbox(v___y_1311_);
v_suppressElabErrors_boxed_1315_ = lean_unbox(v_suppressElabErrors_1312_);
v_res_1316_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(v___y_3210__boxed_1314_, v_suppressElabErrors_boxed_1315_, v_x_1313_);
lean_dec(v_x_1313_);
v_r_1317_ = lean_box(v_res_1316_);
return v_r_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(lean_object* v_opts_1318_, lean_object* v_opt_1319_){
_start:
{
lean_object* v_name_1320_; lean_object* v_defValue_1321_; lean_object* v_map_1322_; lean_object* v___x_1323_; 
v_name_1320_ = lean_ctor_get(v_opt_1319_, 0);
v_defValue_1321_ = lean_ctor_get(v_opt_1319_, 1);
v_map_1322_ = lean_ctor_get(v_opts_1318_, 0);
v___x_1323_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1322_, v_name_1320_);
if (lean_obj_tag(v___x_1323_) == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_unbox(v_defValue_1321_);
return v___x_1324_;
}
else
{
lean_object* v_val_1325_; 
v_val_1325_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1325_);
lean_dec_ref_known(v___x_1323_, 1);
if (lean_obj_tag(v_val_1325_) == 1)
{
uint8_t v_v_1326_; 
v_v_1326_ = lean_ctor_get_uint8(v_val_1325_, 0);
lean_dec_ref_known(v_val_1325_, 0);
return v_v_1326_;
}
else
{
uint8_t v___x_1327_; 
lean_dec(v_val_1325_);
v___x_1327_ = lean_unbox(v_defValue_1321_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0___boxed(lean_object* v_opts_1328_, lean_object* v_opt_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_1328_, v_opt_1329_);
lean_dec_ref(v_opt_1329_);
lean_dec_ref(v_opts_1328_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
lean_ctor_set(v___x_1337_, 2, v___x_1336_);
lean_ctor_set(v___x_1337_, 3, v___x_1336_);
lean_ctor_set(v___x_1337_, 4, v___x_1335_);
lean_ctor_set(v___x_1337_, 5, v___x_1335_);
lean_ctor_set(v___x_1337_, 6, v___x_1335_);
lean_ctor_set(v___x_1337_, 7, v___x_1335_);
lean_ctor_set(v___x_1337_, 8, v___x_1335_);
lean_ctor_set(v___x_1337_, 9, v___x_1335_);
lean_ctor_set(v___x_1337_, 10, v___x_1335_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_unsigned_to_nat(32u);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1341_ = ((size_t)5ULL);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_unsigned_to_nat(32u);
v___x_1344_ = lean_mk_empty_array_with_capacity(v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__3);
v___x_1346_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
lean_ctor_set(v___x_1346_, 2, v___x_1342_);
lean_ctor_set(v___x_1346_, 3, v___x_1342_);
lean_ctor_set_usize(v___x_1346_, 4, v___x_1341_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = lean_box(1);
v___x_1348_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__4);
v___x_1349_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1347_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v_env_1355_; lean_object* v___x_1356_; lean_object* v_scopes_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_opts_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1354_ = lean_st_ref_get(v___y_1352_);
v_env_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc_ref(v_env_1355_);
lean_dec(v___x_1354_);
v___x_1356_ = lean_st_ref_get(v___y_1352_);
v_scopes_1357_ = lean_ctor_get(v___x_1356_, 2);
lean_inc(v_scopes_1357_);
lean_dec(v___x_1356_);
v___x_1358_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1359_ = l_List_head_x21___redArg(v___x_1358_, v_scopes_1357_);
lean_dec(v_scopes_1357_);
v_opts_1360_ = lean_ctor_get(v___x_1359_, 1);
lean_inc_ref(v_opts_1360_);
lean_dec(v___x_1359_);
v___x_1361_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1362_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___closed__5);
v___x_1363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1363_, 0, v_env_1355_);
lean_ctor_set(v___x_1363_, 1, v___x_1361_);
lean_ctor_set(v___x_1363_, 2, v___x_1362_);
lean_ctor_set(v___x_1363_, 3, v_opts_1360_);
v___x_1364_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_msgData_1351_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1366_, v___y_1367_);
lean_dec(v___y_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(lean_object* v_ref_1371_, lean_object* v_msgData_1372_, uint8_t v_severity_1373_, uint8_t v_isSilent_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___y_1379_; lean_object* v___y_1380_; uint8_t v___y_1381_; uint8_t v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1443_; uint8_t v___y_1444_; uint8_t v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; uint8_t v___y_1471_; lean_object* v___y_1472_; uint8_t v___y_1473_; uint8_t v___y_1474_; lean_object* v___y_1475_; uint8_t v___y_1479_; uint8_t v___y_1480_; uint8_t v___y_1481_; uint8_t v___x_1496_; uint8_t v___y_1498_; uint8_t v___y_1499_; uint8_t v___y_1500_; uint8_t v___y_1502_; uint8_t v___x_1514_; 
v___x_1496_ = 2;
v___x_1514_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1373_, v___x_1496_);
if (v___x_1514_ == 0)
{
v___y_1502_ = v___x_1514_;
goto v___jp_1501_;
}
else
{
uint8_t v___x_1515_; 
lean_inc_ref(v_msgData_1372_);
v___x_1515_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1372_);
v___y_1502_ = v___x_1515_;
goto v___jp_1501_;
}
v___jp_1378_:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Elab_Command_getScope___redArg(v___y_1386_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1389_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1389_ = l_Lean_Elab_Command_getScope___redArg(v___y_1386_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1425_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1425_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1425_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v_currNamespace_1395_; lean_object* v_openDecls_1396_; lean_object* v_env_1397_; lean_object* v_messages_1398_; lean_object* v_scopes_1399_; lean_object* v_usedQuotCtxts_1400_; lean_object* v_nextMacroScope_1401_; lean_object* v_maxRecDepth_1402_; lean_object* v_ngen_1403_; lean_object* v_auxDeclNGen_1404_; lean_object* v_infoState_1405_; lean_object* v_traceState_1406_; lean_object* v_snapshotTasks_1407_; lean_object* v_prevLinterStates_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1424_; 
v___x_1394_ = lean_st_ref_take(v___y_1386_);
v_currNamespace_1395_ = lean_ctor_get(v_a_1388_, 2);
lean_inc(v_currNamespace_1395_);
lean_dec(v_a_1388_);
v_openDecls_1396_ = lean_ctor_get(v_a_1390_, 3);
lean_inc(v_openDecls_1396_);
lean_dec(v_a_1390_);
v_env_1397_ = lean_ctor_get(v___x_1394_, 0);
v_messages_1398_ = lean_ctor_get(v___x_1394_, 1);
v_scopes_1399_ = lean_ctor_get(v___x_1394_, 2);
v_usedQuotCtxts_1400_ = lean_ctor_get(v___x_1394_, 3);
v_nextMacroScope_1401_ = lean_ctor_get(v___x_1394_, 4);
v_maxRecDepth_1402_ = lean_ctor_get(v___x_1394_, 5);
v_ngen_1403_ = lean_ctor_get(v___x_1394_, 6);
v_auxDeclNGen_1404_ = lean_ctor_get(v___x_1394_, 7);
v_infoState_1405_ = lean_ctor_get(v___x_1394_, 8);
v_traceState_1406_ = lean_ctor_get(v___x_1394_, 9);
v_snapshotTasks_1407_ = lean_ctor_get(v___x_1394_, 10);
v_prevLinterStates_1408_ = lean_ctor_get(v___x_1394_, 11);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1410_ = v___x_1394_;
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_prevLinterStates_1408_);
lean_inc(v_snapshotTasks_1407_);
lean_inc(v_traceState_1406_);
lean_inc(v_infoState_1405_);
lean_inc(v_auxDeclNGen_1404_);
lean_inc(v_ngen_1403_);
lean_inc(v_maxRecDepth_1402_);
lean_inc(v_nextMacroScope_1401_);
lean_inc(v_usedQuotCtxts_1400_);
lean_inc(v_scopes_1399_);
lean_inc(v_messages_1398_);
lean_inc(v_env_1397_);
lean_dec(v___x_1394_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_currNamespace_1395_);
lean_ctor_set(v___x_1412_, 1, v_openDecls_1396_);
v___x_1413_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v___y_1384_);
lean_inc_ref(v___y_1383_);
lean_inc_ref(v___y_1380_);
v___x_1414_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1414_, 0, v___y_1380_);
lean_ctor_set(v___x_1414_, 1, v___y_1379_);
lean_ctor_set(v___x_1414_, 2, v___y_1385_);
lean_ctor_set(v___x_1414_, 3, v___y_1383_);
lean_ctor_set(v___x_1414_, 4, v___x_1413_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*5, v___y_1382_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*5 + 1, v___y_1381_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*5 + 2, v_isSilent_1374_);
v___x_1415_ = l_Lean_MessageLog_add(v___x_1414_, v_messages_1398_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___x_1415_);
v___x_1417_ = v___x_1410_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_env_1397_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_scopes_1399_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_usedQuotCtxts_1400_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_nextMacroScope_1401_);
lean_ctor_set(v_reuseFailAlloc_1423_, 5, v_maxRecDepth_1402_);
lean_ctor_set(v_reuseFailAlloc_1423_, 6, v_ngen_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 7, v_auxDeclNGen_1404_);
lean_ctor_set(v_reuseFailAlloc_1423_, 8, v_infoState_1405_);
lean_ctor_set(v_reuseFailAlloc_1423_, 9, v_traceState_1406_);
lean_ctor_set(v_reuseFailAlloc_1423_, 10, v_snapshotTasks_1407_);
lean_ctor_set(v_reuseFailAlloc_1423_, 11, v_prevLinterStates_1408_);
v___x_1417_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_st_ref_put(v___y_1386_, v___x_1417_);
v___x_1419_ = lean_box(0);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1419_);
v___x_1421_ = v___x_1392_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_a_1388_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___y_1379_);
v_a_1426_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1389_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1389_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___y_1379_);
v_a_1434_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1387_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1387_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
v___jp_1442_:
{
lean_object* v_fileName_1448_; lean_object* v_fileMap_1449_; uint8_t v_suppressElabErrors_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1469_; 
v_fileName_1448_ = lean_ctor_get(v___y_1375_, 0);
v_fileMap_1449_ = lean_ctor_get(v___y_1375_, 1);
v_suppressElabErrors_1450_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*10);
v___x_1451_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1372_);
v___x_1452_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg(v___x_1451_, v___y_1376_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1469_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1469_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_inc_ref_n(v_fileMap_1449_, 2);
v___x_1457_ = l_Lean_FileMap_toPosition(v_fileMap_1449_, v___y_1446_);
lean_dec(v___y_1446_);
v___x_1458_ = l_Lean_FileMap_toPosition(v_fileMap_1449_, v___y_1447_);
lean_dec(v___y_1447_);
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
v___x_1460_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___closed__0));
if (v_suppressElabErrors_1450_ == 0)
{
lean_del_object(v___x_1455_);
v___y_1379_ = v___x_1457_;
v___y_1380_ = v_fileName_1448_;
v___y_1381_ = v___y_1444_;
v___y_1382_ = v___y_1445_;
v___y_1383_ = v___x_1460_;
v___y_1384_ = v_a_1453_;
v___y_1385_ = v___x_1459_;
v___y_1386_ = v___y_1376_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___f_1463_; uint8_t v___x_1464_; 
v___x_1461_ = lean_box(v___y_1443_);
v___x_1462_ = lean_box(v_suppressElabErrors_1450_);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1463_, 0, v___x_1461_);
lean_closure_set(v___f_1463_, 1, v___x_1462_);
lean_inc(v_a_1453_);
v___x_1464_ = l_Lean_MessageData_hasTag(v___f_1463_, v_a_1453_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec_ref_known(v___x_1459_, 1);
lean_dec_ref(v___x_1457_);
lean_dec(v_a_1453_);
v___x_1465_ = lean_box(0);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1465_);
v___x_1467_ = v___x_1455_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_del_object(v___x_1455_);
v___y_1379_ = v___x_1457_;
v___y_1380_ = v_fileName_1448_;
v___y_1381_ = v___y_1444_;
v___y_1382_ = v___y_1445_;
v___y_1383_ = v___x_1460_;
v___y_1384_ = v_a_1453_;
v___y_1385_ = v___x_1459_;
v___y_1386_ = v___y_1376_;
goto v___jp_1378_;
}
}
}
}
v___jp_1470_:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Syntax_getTailPos_x3f(v___y_1472_, v___y_1474_);
lean_dec(v___y_1472_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_inc(v___y_1475_);
v___y_1443_ = v___y_1471_;
v___y_1444_ = v___y_1473_;
v___y_1445_ = v___y_1474_;
v___y_1446_ = v___y_1475_;
v___y_1447_ = v___y_1475_;
goto v___jp_1442_;
}
else
{
lean_object* v_val_1477_; 
v_val_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___y_1443_ = v___y_1471_;
v___y_1444_ = v___y_1473_;
v___y_1445_ = v___y_1474_;
v___y_1446_ = v___y_1475_;
v___y_1447_ = v_val_1477_;
goto v___jp_1442_;
}
}
v___jp_1478_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Elab_Command_getRef___redArg(v___y_1375_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v_ref_1484_; lean_object* v___x_1485_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v_ref_1484_ = l_Lean_replaceRef(v_ref_1371_, v_a_1483_);
lean_dec(v_a_1483_);
v___x_1485_ = l_Lean_Syntax_getPos_x3f(v_ref_1484_, v___y_1480_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___y_1471_ = v___y_1479_;
v___y_1472_ = v_ref_1484_;
v___y_1473_ = v___y_1481_;
v___y_1474_ = v___y_1480_;
v___y_1475_ = v___x_1486_;
goto v___jp_1470_;
}
else
{
lean_object* v_val_1487_; 
v_val_1487_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v___x_1485_, 1);
v___y_1471_ = v___y_1479_;
v___y_1472_ = v_ref_1484_;
v___y_1473_ = v___y_1481_;
v___y_1474_ = v___y_1480_;
v___y_1475_ = v_val_1487_;
goto v___jp_1470_;
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v_msgData_1372_);
v_a_1488_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1482_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1482_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
v___jp_1497_:
{
if (v___y_1500_ == 0)
{
v___y_1479_ = v___y_1498_;
v___y_1480_ = v___y_1499_;
v___y_1481_ = v_severity_1373_;
goto v___jp_1478_;
}
else
{
v___y_1479_ = v___y_1498_;
v___y_1480_ = v___y_1499_;
v___y_1481_ = v___x_1496_;
goto v___jp_1478_;
}
}
v___jp_1501_:
{
if (v___y_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v_scopes_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_opts_1507_; uint8_t v___x_1508_; uint8_t v___x_1509_; 
v___x_1503_ = lean_st_ref_get(v___y_1376_);
v_scopes_1504_ = lean_ctor_get(v___x_1503_, 2);
lean_inc(v_scopes_1504_);
lean_dec(v___x_1503_);
v___x_1505_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1506_ = l_List_head_x21___redArg(v___x_1505_, v_scopes_1504_);
lean_dec(v_scopes_1504_);
v_opts_1507_ = lean_ctor_get(v___x_1506_, 1);
lean_inc_ref(v_opts_1507_);
lean_dec(v___x_1506_);
v___x_1508_ = 1;
v___x_1509_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1373_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_dec_ref(v_opts_1507_);
v___y_1498_ = v___y_1502_;
v___y_1499_ = v___y_1502_;
v___y_1500_ = v___x_1509_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = l_Lean_warningAsError;
v___x_1511_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_1507_, v___x_1510_);
lean_dec_ref(v_opts_1507_);
v___y_1498_ = v___y_1502_;
v___y_1499_ = v___y_1502_;
v___y_1500_ = v___x_1511_;
goto v___jp_1497_;
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec_ref(v_msgData_1372_);
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___boxed(lean_object* v_ref_1516_, lean_object* v_msgData_1517_, lean_object* v_severity_1518_, lean_object* v_isSilent_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v_severity_boxed_1523_; uint8_t v_isSilent_boxed_1524_; lean_object* v_res_1525_; 
v_severity_boxed_1523_ = lean_unbox(v_severity_1518_);
v_isSilent_boxed_1524_ = lean_unbox(v_isSilent_1519_);
v_res_1525_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_1516_, v_msgData_1517_, v_severity_boxed_1523_, v_isSilent_boxed_1524_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v_ref_1516_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(lean_object* v_ref_1526_, lean_object* v_msgData_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = 1;
v___x_1532_ = 0;
v___x_1533_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_1526_, v_msgData_1527_, v___x_1531_, v___x_1532_, v___y_1528_, v___y_1529_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1___boxed(lean_object* v_ref_1534_, lean_object* v_msgData_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_ref_1534_, v_msgData_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_ref_1534_);
return v_res_1539_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(lean_object* v_kw_1546_, lean_object* v_what_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v_scopes_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v_opts_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1551_ = lean_st_ref_get(v___y_1549_);
v_scopes_1552_ = lean_ctor_get(v___x_1551_, 2);
lean_inc(v_scopes_1552_);
lean_dec(v___x_1551_);
v___x_1553_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1554_ = l_List_head_x21___redArg(v___x_1553_, v_scopes_1552_);
lean_dec(v_scopes_1552_);
v_opts_1555_ = lean_ctor_get(v___x_1554_, 1);
lean_inc_ref(v_opts_1555_);
lean_dec(v___x_1554_);
v___x_1556_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_1557_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_1555_, v___x_1556_);
lean_dec_ref(v_opts_1555_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_what_1547_);
v___x_1560_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_kw_1546_, v___x_1561_, v___y_1548_, v___y_1549_);
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_what_1547_);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___boxed(lean_object* v_kw_1565_, lean_object* v_what_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v_kw_1565_, v_what_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v_kw_1565_);
return v_res_1570_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(lean_object* v_as_1577_, size_t v_sz_1578_, size_t v_i_1579_, lean_object* v_b_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_a_1585_; uint8_t v___x_1589_; 
v___x_1589_ = lean_usize_dec_lt(v_i_1579_, v_sz_1578_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_b_1580_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; lean_object* v_a_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_box(0);
v_a_1592_ = lean_array_uget_borrowed(v_as_1577_, v_i_1579_);
v___x_1593_ = l_Lean_Syntax_isNone(v_a_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = l_Lean_Syntax_getArg(v_a_1592_, v___x_1594_);
v___x_1596_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1594_);
lean_dec(v___x_1595_);
v___x_1597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1);
v___x_1598_ = l_Lean_Syntax_getAtomVal(v___x_1596_);
v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1597_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3);
v___x_1602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1600_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v___x_1596_, v___x_1602_, v___y_1581_, v___y_1582_);
lean_dec(v___x_1596_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_dec_ref_known(v___x_1603_, 1);
v_a_1585_ = v___x_1591_;
goto v___jp_1584_;
}
else
{
return v___x_1603_;
}
}
else
{
v_a_1585_ = v___x_1591_;
goto v___jp_1584_;
}
}
v___jp_1584_:
{
size_t v___x_1586_; size_t v___x_1587_; 
v___x_1586_ = ((size_t)1ULL);
v___x_1587_ = lean_usize_add(v_i_1579_, v___x_1586_);
v_i_1579_ = v___x_1587_;
v_b_1580_ = v_a_1585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___boxed(lean_object* v_as_1604_, lean_object* v_sz_1605_, lean_object* v_i_1606_, lean_object* v_b_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_sz_boxed_1611_; size_t v_i_boxed_1612_; lean_object* v_res_1613_; 
v_sz_boxed_1611_ = lean_unbox_usize(v_sz_1605_);
lean_dec(v_sz_1605_);
v_i_boxed_1612_ = lean_unbox_usize(v_i_1606_);
lean_dec(v_i_1606_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v_as_1604_, v_sz_boxed_1611_, v_i_boxed_1612_, v_b_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v_as_1604_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice(lean_object* v_stx_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; size_t v_sz_1621_; size_t v___x_1622_; lean_object* v___x_1623_; 
v___x_1618_ = l_Lean_Syntax_getArgs(v_stx_1614_);
v___x_1619_ = lean_array_pop(v___x_1618_);
v___x_1620_ = lean_box(0);
v_sz_1621_ = lean_array_size(v___x_1619_);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v___x_1619_, v_sz_1621_, v___x_1622_, v___x_1620_, v_a_1615_, v_a_1616_);
lean_dec_ref(v___x_1619_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v___x_1623_, 0);
lean_dec(v_unused_1631_);
v___x_1625_ = v___x_1623_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v___x_1623_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1620_);
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1620_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice___boxed(lean_object* v_stx_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Elab_Tactic_Do_elabContractNotice(v_stx_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_stx_1632_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1637_, v___y_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__4(v_msgData_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1(){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1655_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_1657_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_1658_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractNotice___boxed), 4, 0);
v___x_1659_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1655_, v___x_1656_, v___x_1657_, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___boxed(lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3(){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_1665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0));
v___x_1666_ = l_Lean_addBuiltinDocString(v___x_1664_, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___boxed(lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
return v_res_1668_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg(){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___boxed(lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_object* v_00_u03b1_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___boxed(lean_object* v_00_u03b1_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(v_00_u03b1_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(lean_object* v_msgData_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v_env_1704_; lean_object* v___x_1705_; lean_object* v_mctx_1706_; lean_object* v_lctx_1707_; lean_object* v_options_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1703_ = lean_st_ref_get(v___y_1701_);
v_env_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc_ref(v_env_1704_);
lean_dec(v___x_1703_);
v___x_1705_ = lean_st_ref_get(v___y_1699_);
v_mctx_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc_ref(v_mctx_1706_);
lean_dec(v___x_1705_);
v_lctx_1707_ = lean_ctor_get(v___y_1698_, 2);
v_options_1708_ = lean_ctor_get(v___y_1700_, 2);
lean_inc_ref(v_options_1708_);
lean_inc_ref(v_lctx_1707_);
v___x_1709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1709_, 0, v_env_1704_);
lean_ctor_set(v___x_1709_, 1, v_mctx_1706_);
lean_ctor_set(v___x_1709_, 2, v_lctx_1707_);
lean_ctor_set(v___x_1709_, 3, v_options_1708_);
v___x_1710_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v_msgData_1697_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msgData_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1718_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v___y_1724_, uint8_t v_suppressElabErrors_1725_, lean_object* v_x_1726_){
_start:
{
if (lean_obj_tag(v_x_1726_) == 1)
{
lean_object* v_pre_1727_; 
v_pre_1727_ = lean_ctor_get(v_x_1726_, 0);
switch(lean_obj_tag(v_pre_1727_))
{
case 1:
{
lean_object* v_pre_1728_; 
v_pre_1728_ = lean_ctor_get(v_pre_1727_, 0);
switch(lean_obj_tag(v_pre_1728_))
{
case 0:
{
lean_object* v_str_1729_; lean_object* v_str_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v_str_1729_ = lean_ctor_get(v_x_1726_, 1);
v_str_1730_ = lean_ctor_get(v_pre_1727_, 1);
v___x_1731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0));
v___x_1732_ = lean_string_dec_eq(v_str_1730_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__47));
v___x_1734_ = lean_string_dec_eq(v_str_1730_, v___x_1733_);
if (v___x_1734_ == 0)
{
return v___y_1724_;
}
else
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_1736_ = lean_string_dec_eq(v_str_1729_, v___x_1735_);
if (v___x_1736_ == 0)
{
return v___y_1724_;
}
else
{
return v_suppressElabErrors_1725_;
}
}
}
else
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_1738_ = lean_string_dec_eq(v_str_1729_, v___x_1737_);
if (v___x_1738_ == 0)
{
return v___y_1724_;
}
else
{
return v_suppressElabErrors_1725_;
}
}
}
case 1:
{
lean_object* v_pre_1739_; 
v_pre_1739_ = lean_ctor_get(v_pre_1728_, 0);
if (lean_obj_tag(v_pre_1739_) == 0)
{
lean_object* v_str_1740_; lean_object* v_str_1741_; lean_object* v_str_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_str_1740_ = lean_ctor_get(v_x_1726_, 1);
v_str_1741_ = lean_ctor_get(v_pre_1727_, 1);
v_str_1742_ = lean_ctor_get(v_pre_1728_, 1);
v___x_1743_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_1744_ = lean_string_dec_eq(v_str_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
return v___y_1724_;
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_1746_ = lean_string_dec_eq(v_str_1741_, v___x_1745_);
if (v___x_1746_ == 0)
{
return v___y_1724_;
}
else
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_1748_ = lean_string_dec_eq(v_str_1740_, v___x_1747_);
if (v___x_1748_ == 0)
{
return v___y_1724_;
}
else
{
return v_suppressElabErrors_1725_;
}
}
}
}
else
{
return v___y_1724_;
}
}
default: 
{
return v___y_1724_;
}
}
}
case 0:
{
lean_object* v_str_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_str_1749_ = lean_ctor_get(v_x_1726_, 1);
v___x_1750_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_1751_ = lean_string_dec_eq(v_str_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
return v___y_1724_;
}
else
{
return v_suppressElabErrors_1725_;
}
}
default: 
{
return v___y_1724_;
}
}
}
else
{
return v___y_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_1752_, lean_object* v_suppressElabErrors_1753_, lean_object* v_x_1754_){
_start:
{
uint8_t v___y_16219__boxed_1755_; uint8_t v_suppressElabErrors_boxed_1756_; uint8_t v_res_1757_; lean_object* v_r_1758_; 
v___y_16219__boxed_1755_ = lean_unbox(v___y_1752_);
v_suppressElabErrors_boxed_1756_ = lean_unbox(v_suppressElabErrors_1753_);
v_res_1757_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(v___y_16219__boxed_1755_, v_suppressElabErrors_boxed_1756_, v_x_1754_);
lean_dec(v_x_1754_);
v_r_1758_ = lean_box(v_res_1757_);
return v_r_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1759_, lean_object* v_msgData_1760_, uint8_t v_severity_1761_, uint8_t v_isSilent_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; uint8_t v___y_1809_; uint8_t v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; uint8_t v___y_1833_; uint8_t v___y_1834_; uint8_t v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1841_; lean_object* v___y_1842_; uint8_t v___y_1843_; uint8_t v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; uint8_t v___y_1847_; uint8_t v___x_1852_; lean_object* v___y_1854_; lean_object* v___y_1855_; uint8_t v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; uint8_t v___y_1859_; uint8_t v___y_1860_; uint8_t v___y_1862_; uint8_t v___x_1877_; 
v___x_1852_ = 2;
v___x_1877_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1761_, v___x_1852_);
if (v___x_1877_ == 0)
{
v___y_1862_ = v___x_1877_;
goto v___jp_1861_;
}
else
{
uint8_t v___x_1878_; 
lean_inc_ref(v_msgData_1760_);
v___x_1878_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1760_);
v___y_1862_ = v___x_1878_;
goto v___jp_1861_;
}
v___jp_1768_:
{
lean_object* v___x_1778_; lean_object* v_currNamespace_1779_; lean_object* v_openDecls_1780_; lean_object* v_env_1781_; lean_object* v_nextMacroScope_1782_; lean_object* v_ngen_1783_; lean_object* v_auxDeclNGen_1784_; lean_object* v_traceState_1785_; lean_object* v_cache_1786_; lean_object* v_messages_1787_; lean_object* v_infoState_1788_; lean_object* v_snapshotTasks_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1803_; 
v___x_1778_ = lean_st_ref_take(v___y_1777_);
v_currNamespace_1779_ = lean_ctor_get(v___y_1776_, 6);
v_openDecls_1780_ = lean_ctor_get(v___y_1776_, 7);
v_env_1781_ = lean_ctor_get(v___x_1778_, 0);
v_nextMacroScope_1782_ = lean_ctor_get(v___x_1778_, 1);
v_ngen_1783_ = lean_ctor_get(v___x_1778_, 2);
v_auxDeclNGen_1784_ = lean_ctor_get(v___x_1778_, 3);
v_traceState_1785_ = lean_ctor_get(v___x_1778_, 4);
v_cache_1786_ = lean_ctor_get(v___x_1778_, 5);
v_messages_1787_ = lean_ctor_get(v___x_1778_, 6);
v_infoState_1788_ = lean_ctor_get(v___x_1778_, 7);
v_snapshotTasks_1789_ = lean_ctor_get(v___x_1778_, 8);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1791_ = v___x_1778_;
v_isShared_1792_ = v_isSharedCheck_1803_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_snapshotTasks_1789_);
lean_inc(v_infoState_1788_);
lean_inc(v_messages_1787_);
lean_inc(v_cache_1786_);
lean_inc(v_traceState_1785_);
lean_inc(v_auxDeclNGen_1784_);
lean_inc(v_ngen_1783_);
lean_inc(v_nextMacroScope_1782_);
lean_inc(v_env_1781_);
lean_dec(v___x_1778_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1803_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_inc(v_openDecls_1780_);
lean_inc(v_currNamespace_1779_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_currNamespace_1779_);
lean_ctor_set(v___x_1793_, 1, v_openDecls_1780_);
v___x_1794_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v___y_1775_);
lean_inc_ref(v___y_1773_);
lean_inc_ref(v___y_1770_);
v___x_1795_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1795_, 0, v___y_1770_);
lean_ctor_set(v___x_1795_, 1, v___y_1769_);
lean_ctor_set(v___x_1795_, 2, v___y_1774_);
lean_ctor_set(v___x_1795_, 3, v___y_1773_);
lean_ctor_set(v___x_1795_, 4, v___x_1794_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*5, v___y_1771_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*5 + 1, v___y_1772_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*5 + 2, v_isSilent_1762_);
v___x_1796_ = l_Lean_MessageLog_add(v___x_1795_, v_messages_1787_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 6, v___x_1796_);
v___x_1798_ = v___x_1791_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_env_1781_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_nextMacroScope_1782_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_ngen_1783_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_auxDeclNGen_1784_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v_traceState_1785_);
lean_ctor_set(v_reuseFailAlloc_1802_, 5, v_cache_1786_);
lean_ctor_set(v_reuseFailAlloc_1802_, 6, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1802_, 7, v_infoState_1788_);
lean_ctor_set(v_reuseFailAlloc_1802_, 8, v_snapshotTasks_1789_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_st_ref_put(v___y_1777_, v___x_1798_);
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
}
}
v___jp_1804_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1828_; 
v___x_1813_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1760_);
v___x_1814_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v___x_1813_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1828_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1828_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_inc_ref_n(v___y_1811_, 2);
v___x_1819_ = l_Lean_FileMap_toPosition(v___y_1811_, v___y_1806_);
lean_dec(v___y_1806_);
v___x_1820_ = l_Lean_FileMap_toPosition(v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
v___x_1822_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___closed__0));
if (v___y_1808_ == 0)
{
lean_del_object(v___x_1817_);
lean_dec_ref(v___y_1805_);
v___y_1769_ = v___x_1819_;
v___y_1770_ = v___y_1807_;
v___y_1771_ = v___y_1809_;
v___y_1772_ = v___y_1810_;
v___y_1773_ = v___x_1822_;
v___y_1774_ = v___x_1821_;
v___y_1775_ = v_a_1815_;
v___y_1776_ = v___y_1765_;
v___y_1777_ = v___y_1766_;
goto v___jp_1768_;
}
else
{
uint8_t v___x_1823_; 
lean_inc(v_a_1815_);
v___x_1823_ = l_Lean_MessageData_hasTag(v___y_1805_, v_a_1815_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
lean_dec_ref_known(v___x_1821_, 1);
lean_dec_ref(v___x_1819_);
lean_dec(v_a_1815_);
v___x_1824_ = lean_box(0);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1824_);
v___x_1826_ = v___x_1817_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
else
{
lean_del_object(v___x_1817_);
v___y_1769_ = v___x_1819_;
v___y_1770_ = v___y_1807_;
v___y_1771_ = v___y_1809_;
v___y_1772_ = v___y_1810_;
v___y_1773_ = v___x_1822_;
v___y_1774_ = v___x_1821_;
v___y_1775_ = v_a_1815_;
v___y_1776_ = v___y_1765_;
v___y_1777_ = v___y_1766_;
goto v___jp_1768_;
}
}
}
}
v___jp_1829_:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_Syntax_getTailPos_x3f(v___y_1832_, v___y_1834_);
lean_dec(v___y_1832_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_inc(v___y_1837_);
v___y_1805_ = v___y_1830_;
v___y_1806_ = v___y_1837_;
v___y_1807_ = v___y_1831_;
v___y_1808_ = v___y_1833_;
v___y_1809_ = v___y_1834_;
v___y_1810_ = v___y_1835_;
v___y_1811_ = v___y_1836_;
v___y_1812_ = v___y_1837_;
goto v___jp_1804_;
}
else
{
lean_object* v_val_1839_; 
v_val_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_val_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v___y_1805_ = v___y_1830_;
v___y_1806_ = v___y_1837_;
v___y_1807_ = v___y_1831_;
v___y_1808_ = v___y_1833_;
v___y_1809_ = v___y_1834_;
v___y_1810_ = v___y_1835_;
v___y_1811_ = v___y_1836_;
v___y_1812_ = v_val_1839_;
goto v___jp_1804_;
}
}
v___jp_1840_:
{
lean_object* v_ref_1848_; lean_object* v___x_1849_; 
v_ref_1848_ = l_Lean_replaceRef(v_ref_1759_, v___y_1845_);
v___x_1849_ = l_Lean_Syntax_getPos_x3f(v_ref_1848_, v___y_1844_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_unsigned_to_nat(0u);
v___y_1830_ = v___y_1841_;
v___y_1831_ = v___y_1842_;
v___y_1832_ = v_ref_1848_;
v___y_1833_ = v___y_1843_;
v___y_1834_ = v___y_1844_;
v___y_1835_ = v___y_1847_;
v___y_1836_ = v___y_1846_;
v___y_1837_ = v___x_1850_;
goto v___jp_1829_;
}
else
{
lean_object* v_val_1851_; 
v_val_1851_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v___x_1849_, 1);
v___y_1830_ = v___y_1841_;
v___y_1831_ = v___y_1842_;
v___y_1832_ = v_ref_1848_;
v___y_1833_ = v___y_1843_;
v___y_1834_ = v___y_1844_;
v___y_1835_ = v___y_1847_;
v___y_1836_ = v___y_1846_;
v___y_1837_ = v_val_1851_;
goto v___jp_1829_;
}
}
v___jp_1853_:
{
if (v___y_1860_ == 0)
{
v___y_1841_ = v___y_1854_;
v___y_1842_ = v___y_1855_;
v___y_1843_ = v___y_1856_;
v___y_1844_ = v___y_1859_;
v___y_1845_ = v___y_1857_;
v___y_1846_ = v___y_1858_;
v___y_1847_ = v_severity_1761_;
goto v___jp_1840_;
}
else
{
v___y_1841_ = v___y_1854_;
v___y_1842_ = v___y_1855_;
v___y_1843_ = v___y_1856_;
v___y_1844_ = v___y_1859_;
v___y_1845_ = v___y_1857_;
v___y_1846_ = v___y_1858_;
v___y_1847_ = v___x_1852_;
goto v___jp_1840_;
}
}
v___jp_1861_:
{
if (v___y_1862_ == 0)
{
lean_object* v_fileName_1863_; lean_object* v_fileMap_1864_; lean_object* v_options_1865_; lean_object* v_ref_1866_; uint8_t v_suppressElabErrors_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___f_1870_; uint8_t v___x_1871_; uint8_t v___x_1872_; 
v_fileName_1863_ = lean_ctor_get(v___y_1765_, 0);
v_fileMap_1864_ = lean_ctor_get(v___y_1765_, 1);
v_options_1865_ = lean_ctor_get(v___y_1765_, 2);
v_ref_1866_ = lean_ctor_get(v___y_1765_, 5);
v_suppressElabErrors_1867_ = lean_ctor_get_uint8(v___y_1765_, sizeof(void*)*14 + 1);
v___x_1868_ = lean_box(v___y_1862_);
v___x_1869_ = lean_box(v_suppressElabErrors_1867_);
v___f_1870_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1870_, 0, v___x_1868_);
lean_closure_set(v___f_1870_, 1, v___x_1869_);
v___x_1871_ = 1;
v___x_1872_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1761_, v___x_1871_);
if (v___x_1872_ == 0)
{
v___y_1854_ = v___f_1870_;
v___y_1855_ = v_fileName_1863_;
v___y_1856_ = v_suppressElabErrors_1867_;
v___y_1857_ = v_ref_1866_;
v___y_1858_ = v_fileMap_1864_;
v___y_1859_ = v___y_1862_;
v___y_1860_ = v___x_1872_;
goto v___jp_1853_;
}
else
{
lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = l_Lean_warningAsError;
v___x_1874_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_options_1865_, v___x_1873_);
v___y_1854_ = v___f_1870_;
v___y_1855_ = v_fileName_1863_;
v___y_1856_ = v_suppressElabErrors_1867_;
v___y_1857_ = v_ref_1866_;
v___y_1858_ = v_fileMap_1864_;
v___y_1859_ = v___y_1862_;
v___y_1860_ = v___x_1874_;
goto v___jp_1853_;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec_ref(v_msgData_1760_);
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1879_, lean_object* v_msgData_1880_, lean_object* v_severity_1881_, lean_object* v_isSilent_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
uint8_t v_severity_boxed_1888_; uint8_t v_isSilent_boxed_1889_; lean_object* v_res_1890_; 
v_severity_boxed_1888_ = lean_unbox(v_severity_1881_);
v_isSilent_boxed_1889_ = lean_unbox(v_isSilent_1882_);
v_res_1890_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_1879_, v_msgData_1880_, v_severity_boxed_1888_, v_isSilent_boxed_1889_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v_ref_1879_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object* v_ref_1891_, lean_object* v_msgData_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
uint8_t v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = 1;
v___x_1902_ = 0;
v___x_1903_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_1891_, v_msgData_1892_, v___x_1901_, v___x_1902_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object* v_ref_1904_, lean_object* v_msgData_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_ref_1904_, v_msgData_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v_ref_1904_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object* v_kw_1915_, lean_object* v_what_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_options_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v_options_1925_ = lean_ctor_get(v___y_1922_, 2);
v___x_1926_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_1927_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_options_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1928_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v_what_1916_);
v___x_1930_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_kw_1915_, v___x_1931_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec_ref(v_what_1916_);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object* v_kw_1935_, lean_object* v_what_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_kw_1935_, v_what_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v_kw_1935_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(lean_object* v_msg_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_ref_1952_; lean_object* v___x_1953_; lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1962_; 
v_ref_1952_ = lean_ctor_get(v___y_1949_, 5);
v___x_1953_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msg_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_inc(v_ref_1952_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_ref_1952_);
lean_ctor_set(v___x_1958_, 1, v_a_1954_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 1);
lean_ctor_set(v___x_1956_, 0, v___x_1958_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(lean_object* v_ref_1970_, lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_fileName_1980_; lean_object* v_fileMap_1981_; lean_object* v_options_1982_; lean_object* v_currRecDepth_1983_; lean_object* v_maxRecDepth_1984_; lean_object* v_ref_1985_; lean_object* v_currNamespace_1986_; lean_object* v_openDecls_1987_; lean_object* v_initHeartbeats_1988_; lean_object* v_maxHeartbeats_1989_; lean_object* v_quotContext_1990_; lean_object* v_currMacroScope_1991_; uint8_t v_diag_1992_; lean_object* v_cancelTk_x3f_1993_; uint8_t v_suppressElabErrors_1994_; lean_object* v_inheritedTraceOptions_1995_; lean_object* v_ref_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_fileName_1980_ = lean_ctor_get(v___y_1977_, 0);
v_fileMap_1981_ = lean_ctor_get(v___y_1977_, 1);
v_options_1982_ = lean_ctor_get(v___y_1977_, 2);
v_currRecDepth_1983_ = lean_ctor_get(v___y_1977_, 3);
v_maxRecDepth_1984_ = lean_ctor_get(v___y_1977_, 4);
v_ref_1985_ = lean_ctor_get(v___y_1977_, 5);
v_currNamespace_1986_ = lean_ctor_get(v___y_1977_, 6);
v_openDecls_1987_ = lean_ctor_get(v___y_1977_, 7);
v_initHeartbeats_1988_ = lean_ctor_get(v___y_1977_, 8);
v_maxHeartbeats_1989_ = lean_ctor_get(v___y_1977_, 9);
v_quotContext_1990_ = lean_ctor_get(v___y_1977_, 10);
v_currMacroScope_1991_ = lean_ctor_get(v___y_1977_, 11);
v_diag_1992_ = lean_ctor_get_uint8(v___y_1977_, sizeof(void*)*14);
v_cancelTk_x3f_1993_ = lean_ctor_get(v___y_1977_, 12);
v_suppressElabErrors_1994_ = lean_ctor_get_uint8(v___y_1977_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1995_ = lean_ctor_get(v___y_1977_, 13);
v_ref_1996_ = l_Lean_replaceRef(v_ref_1970_, v_ref_1985_);
lean_inc_ref(v_inheritedTraceOptions_1995_);
lean_inc(v_cancelTk_x3f_1993_);
lean_inc(v_currMacroScope_1991_);
lean_inc(v_quotContext_1990_);
lean_inc(v_maxHeartbeats_1989_);
lean_inc(v_initHeartbeats_1988_);
lean_inc(v_openDecls_1987_);
lean_inc(v_currNamespace_1986_);
lean_inc(v_maxRecDepth_1984_);
lean_inc(v_currRecDepth_1983_);
lean_inc_ref(v_options_1982_);
lean_inc_ref(v_fileMap_1981_);
lean_inc_ref(v_fileName_1980_);
v___x_1997_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1997_, 0, v_fileName_1980_);
lean_ctor_set(v___x_1997_, 1, v_fileMap_1981_);
lean_ctor_set(v___x_1997_, 2, v_options_1982_);
lean_ctor_set(v___x_1997_, 3, v_currRecDepth_1983_);
lean_ctor_set(v___x_1997_, 4, v_maxRecDepth_1984_);
lean_ctor_set(v___x_1997_, 5, v_ref_1996_);
lean_ctor_set(v___x_1997_, 6, v_currNamespace_1986_);
lean_ctor_set(v___x_1997_, 7, v_openDecls_1987_);
lean_ctor_set(v___x_1997_, 8, v_initHeartbeats_1988_);
lean_ctor_set(v___x_1997_, 9, v_maxHeartbeats_1989_);
lean_ctor_set(v___x_1997_, 10, v_quotContext_1990_);
lean_ctor_set(v___x_1997_, 11, v_currMacroScope_1991_);
lean_ctor_set(v___x_1997_, 12, v_cancelTk_x3f_1993_);
lean_ctor_set(v___x_1997_, 13, v_inheritedTraceOptions_1995_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*14, v_diag_1992_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*14 + 1, v_suppressElabErrors_1994_);
v___x_1998_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_1971_, v___y_1975_, v___y_1976_, v___x_1997_, v___y_1978_);
lean_dec_ref_known(v___x_1997_, 14);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object* v_ref_1999_, lean_object* v_msg_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_1999_, v_msg_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v_ref_1999_);
return v_res_2009_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4));
v___x_2021_ = l_Lean_mkCIdent(v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6));
v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object* v_stx_2031_, lean_object* v_dec_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v_tk_2042_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v_as_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2041_ = lean_unsigned_to_nat(0u);
v_tk_2042_ = l_Lean_Syntax_getArg(v_stx_2031_, v___x_2041_);
v___x_2120_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9));
lean_inc(v_stx_2031_);
v___x_2121_ = l_Lean_Syntax_isOfKind(v_stx_2031_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_tk_2042_);
lean_dec_ref(v_dec_2032_);
lean_dec(v_stx_2031_);
v___x_2122_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
lean_object* v___x_2131_; lean_object* v_p_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_unsigned_to_nat(1u);
v_p_2132_ = l_Lean_Syntax_getArg(v_stx_2031_, v___x_2131_);
lean_dec(v_stx_2031_);
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__99));
lean_inc(v_p_2132_);
v___x_2134_ = l_Lean_Syntax_isOfKind(v_p_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
v_as_2097_ = v_p_2132_;
v___y_2098_ = v_a_2033_;
v___y_2099_ = v_a_2034_;
v___y_2100_ = v_a_2035_;
v___y_2101_ = v_a_2036_;
v___y_2102_ = v_a_2037_;
v___y_2103_ = v_a_2038_;
v___y_2104_ = v_a_2039_;
goto v___jp_2096_;
}
else
{
lean_object* v_ref_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_ref_2135_ = lean_ctor_get(v_a_2038_, 5);
v___x_2136_ = 0;
v___x_2137_ = l_Lean_SourceInfo_fromRef(v_ref_2135_, v___x_2136_);
v___x_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__102));
v___x_2139_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__103));
lean_inc(v___x_2137_);
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2137_);
lean_ctor_set(v___x_2140_, 1, v___x_2138_);
v___x_2141_ = l_Lean_Syntax_node2(v___x_2137_, v___x_2139_, v___x_2140_, v_p_2132_);
v_as_2097_ = v___x_2141_;
v___y_2098_ = v_a_2033_;
v___y_2099_ = v_a_2034_;
v___y_2100_ = v_a_2035_;
v___y_2101_ = v_a_2036_;
v___y_2102_ = v_a_2037_;
v___y_2103_ = v_a_2038_;
v___y_2104_ = v_a_2039_;
goto v___jp_2096_;
}
}
v___jp_2043_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1);
v___x_2053_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_tk_2042_, v___x_2052_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_2053_, 1);
v___x_2054_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_2032_, v_tk_2042_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v_tk_2042_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v_ref_2056_; lean_object* v___x_2057_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v_ref_2056_ = lean_ctor_get(v___y_2050_, 5);
v___x_2057_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_2045_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = l_Lean_Elab_Do_mkMonadApp(v_a_2058_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2079_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2079_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2079_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2064_ = 0;
v___x_2065_ = l_Lean_SourceInfo_fromRef(v_ref_2056_, v___x_2064_);
v___x_2066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
lean_inc(v___x_2065_);
v___x_2067_ = l_Lean_Syntax_node1(v___x_2065_, v___x_2066_, v___y_2044_);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v___x_2069_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5);
v___x_2070_ = l_Lean_Syntax_node2(v___x_2065_, v___x_2068_, v___x_2069_, v___x_2067_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 1);
v___x_2072_ = v___x_2062_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2060_);
v___x_2072_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = 1;
v___x_2074_ = lean_box(0);
v___x_2075_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2070_, v___x_2072_, v___x_2073_, v___x_2073_, v___x_2074_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_2055_, v_a_2076_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2077_;
}
else
{
lean_dec(v_a_2055_);
return v___x_2075_;
}
}
}
}
else
{
lean_dec(v_a_2055_);
lean_dec(v___y_2044_);
return v___x_2059_;
}
}
else
{
lean_dec(v_a_2055_);
lean_dec(v___y_2044_);
return v___x_2057_;
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v___y_2044_);
v_a_2080_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2054_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2054_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v___y_2044_);
lean_dec(v_tk_2042_);
lean_dec_ref(v_dec_2032_);
v_a_2088_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2053_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2053_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
v___jp_2096_:
{
lean_object* v___x_2105_; lean_object* v_env_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2105_ = lean_st_ref_get(v___y_2104_);
v_env_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc_ref(v_env_2106_);
lean_dec(v___x_2105_);
v___x_2107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4));
v___x_2108_ = 1;
v___x_2109_ = l_Lean_Environment_contains(v_env_2106_, v___x_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_as_2097_);
lean_dec_ref(v_dec_2032_);
v___x_2110_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7);
v___x_2111_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_tk_2042_, v___x_2110_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v_tk_2042_);
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
v___y_2044_ = v_as_2097_;
v___y_2045_ = v___y_2098_;
v___y_2046_ = v___y_2099_;
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2101_;
v___y_2049_ = v___y_2102_;
v___y_2050_ = v___y_2103_;
v___y_2051_ = v___y_2104_;
goto v___jp_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object* v_stx_2142_, lean_object* v_dec_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Elab_Tactic_Do_elabDoAssertion(v_stx_2142_, v_dec_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec_ref(v_a_2144_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object* v_00_u03b1_2153_, lean_object* v_ref_2154_, lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_2154_, v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object* v_00_u03b1_2165_, lean_object* v_ref_2166_, lean_object* v_msg_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(v_00_u03b1_2165_, v_ref_2166_, v_msg_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v_ref_2166_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_object* v_00_u03b1_2177_, lean_object* v_msg_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_2178_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2188_, lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(v_00_u03b1_2188_, v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object* v_ref_2199_, lean_object* v_msgData_2200_, uint8_t v_severity_2201_, uint8_t v_isSilent_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_2199_, v_msgData_2200_, v_severity_2201_, v_isSilent_2202_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_2212_, lean_object* v_msgData_2213_, lean_object* v_severity_2214_, lean_object* v_isSilent_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
uint8_t v_severity_boxed_2224_; uint8_t v_isSilent_boxed_2225_; lean_object* v_res_2226_; 
v_severity_boxed_2224_ = lean_unbox(v_severity_2214_);
v_isSilent_boxed_2225_ = lean_unbox(v_isSilent_2215_);
v_res_2226_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_ref_2212_, v_msgData_2213_, v_severity_boxed_2224_, v_isSilent_boxed_2225_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v_ref_2212_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1(){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2235_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9));
v___x_2237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1));
v___x_2238_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed), 10, 0);
v___x_2239_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2235_, v___x_2236_, v___x_2237_, v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
return v_res_2241_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Std_WP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_Command(builtin);
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
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
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
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
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
res = initialize_Lean_Elab_Command(builtin);
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
