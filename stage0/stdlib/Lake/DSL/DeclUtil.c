// Lean compiler output
// Module: Lake.DSL.DeclUtil
// Imports: public import Lake.Util.Binder public import Lake.Config.MetaClasses public import Lean.Elab.Command
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM;
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_getMainModule___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
extern lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM;
extern lean_object* l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
static const lean_string_object l_Lake_DSL_packageDeclName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_package"};
static const lean_object* l_Lake_DSL_packageDeclName___closed__0 = (const lean_object*)&l_Lake_DSL_packageDeclName___closed__0_value;
static const lean_ctor_object l_Lake_DSL_packageDeclName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_packageDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 195, 71, 41, 5, 9, 150, 238)}};
static const lean_object* l_Lake_DSL_packageDeclName___closed__1 = (const lean_object*)&l_Lake_DSL_packageDeclName___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_packageDeclName = (const lean_object*)&l_Lake_DSL_packageDeclName___closed__1_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__0 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__1 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__2 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value;
static const lean_string_object l_Lake_DSL_expandAttrs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lake_DSL_expandAttrs___closed__3 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__3_value;
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandAttrs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value_aux_2),((lean_object*)&l_Lake_DSL_expandAttrs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lake_DSL_expandAttrs___closed__4 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__4_value;
static const lean_array_object l_Lake_DSL_expandAttrs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_DSL_expandAttrs___closed__5 = (const lean_object*)&l_Lake_DSL_expandAttrs___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object*);
static const lean_string_object l_Lake_DSL_identOrStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identOrStr"};
static const lean_object* l_Lake_DSL_identOrStr___closed__0 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__0_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_DSL_identOrStr___closed__1 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__1_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_DSL_identOrStr___closed__2 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__2_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__3_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__3_value_aux_1),((lean_object*)&l_Lake_DSL_identOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 188, 128, 7, 103, 245, 245, 49)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__3 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__3_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lake_DSL_identOrStr___closed__4 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__4_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__5 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__5_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_DSL_identOrStr___closed__6 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__6_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__7 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__7_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__7_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__8 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__8_value;
static const lean_string_object l_Lake_DSL_identOrStr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lake_DSL_identOrStr___closed__9 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__9_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__10 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__10_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__10_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__11 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__11_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__5_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__11_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__12 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__12_value;
static const lean_ctor_object l_Lake_DSL_identOrStr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__0_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__12_value)}};
static const lean_object* l_Lake_DSL_identOrStr___closed__13 = (const lean_object*)&l_Lake_DSL_identOrStr___closed__13_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_identOrStr = (const lean_object*)&l_Lake_DSL_identOrStr___closed__13_value;
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
static const lean_string_object l_Lake_DSL_declField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declField"};
static const lean_object* l_Lake_DSL_declField___closed__0 = (const lean_object*)&l_Lake_DSL_declField___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declField___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 4, 47, 196, 245, 170, 224, 183)}};
static const lean_object* l_Lake_DSL_declField___closed__1 = (const lean_object*)&l_Lake_DSL_declField___closed__1_value;
static const lean_string_object l_Lake_DSL_declField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_DSL_declField___closed__2 = (const lean_object*)&l_Lake_DSL_declField___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declField___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_DSL_declField___closed__3 = (const lean_object*)&l_Lake_DSL_declField___closed__3_value;
static const lean_string_object l_Lake_DSL_declField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_DSL_declField___closed__4 = (const lean_object*)&l_Lake_DSL_declField___closed__4_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__4_value)}};
static const lean_object* l_Lake_DSL_declField___closed__5 = (const lean_object*)&l_Lake_DSL_declField___closed__5_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_declField___closed__5_value)}};
static const lean_object* l_Lake_DSL_declField___closed__6 = (const lean_object*)&l_Lake_DSL_declField___closed__6_value;
static const lean_string_object l_Lake_DSL_declField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_DSL_declField___closed__7 = (const lean_object*)&l_Lake_DSL_declField___closed__7_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declField___closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_DSL_declField___closed__8 = (const lean_object*)&l_Lake_DSL_declField___closed__8_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_DSL_declField___closed__9 = (const lean_object*)&l_Lake_DSL_declField___closed__9_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declField___closed__6_value),((lean_object*)&l_Lake_DSL_declField___closed__9_value)}};
static const lean_object* l_Lake_DSL_declField___closed__10 = (const lean_object*)&l_Lake_DSL_declField___closed__10_value;
static const lean_ctor_object l_Lake_DSL_declField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__0_value),((lean_object*)&l_Lake_DSL_declField___closed__1_value),((lean_object*)&l_Lake_DSL_declField___closed__10_value)}};
static const lean_object* l_Lake_DSL_declField___closed__11 = (const lean_object*)&l_Lake_DSL_declField___closed__11_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declField = (const lean_object*)&l_Lake_DSL_declField___closed__11_value;
static const lean_string_object l_Lake_DSL_structVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structVal"};
static const lean_object* l_Lake_DSL_structVal___closed__0 = (const lean_object*)&l_Lake_DSL_structVal___closed__0_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_structVal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_structVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_structVal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 76, 221, 200, 37, 245, 130, 150)}};
static const lean_object* l_Lake_DSL_structVal___closed__1 = (const lean_object*)&l_Lake_DSL_structVal___closed__1_value;
static const lean_string_object l_Lake_DSL_structVal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lake_DSL_structVal___closed__2 = (const lean_object*)&l_Lake_DSL_structVal___closed__2_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__2_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__3 = (const lean_object*)&l_Lake_DSL_structVal___closed__3_value;
static const lean_string_object l_Lake_DSL_structVal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_DSL_structVal___closed__4 = (const lean_object*)&l_Lake_DSL_structVal___closed__4_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_structVal___closed__4_value),LEAN_SCALAR_PTR_LITERAL(176, 25, 16, 25, 82, 100, 240, 199)}};
static const lean_object* l_Lake_DSL_structVal___closed__5 = (const lean_object*)&l_Lake_DSL_structVal___closed__5_value;
static const lean_string_object l_Lake_DSL_structVal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sepByIndentSemicolon"};
static const lean_object* l_Lake_DSL_structVal___closed__6 = (const lean_object*)&l_Lake_DSL_structVal___closed__6_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_structVal___closed__6_value),LEAN_SCALAR_PTR_LITERAL(139, 141, 160, 225, 89, 107, 71, 117)}};
static const lean_object* l_Lake_DSL_structVal___closed__7 = (const lean_object*)&l_Lake_DSL_structVal___closed__7_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__7_value),((lean_object*)&l_Lake_DSL_declField___closed__11_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__8 = (const lean_object*)&l_Lake_DSL_structVal___closed__8_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__5_value),((lean_object*)&l_Lake_DSL_structVal___closed__8_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__9 = (const lean_object*)&l_Lake_DSL_structVal___closed__9_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__9_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__10 = (const lean_object*)&l_Lake_DSL_structVal___closed__10_value;
static const lean_string_object l_Lake_DSL_structVal___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lake_DSL_structVal___closed__11 = (const lean_object*)&l_Lake_DSL_structVal___closed__11_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__11_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__12 = (const lean_object*)&l_Lake_DSL_structVal___closed__12_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__10_value),((lean_object*)&l_Lake_DSL_structVal___closed__12_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__13 = (const lean_object*)&l_Lake_DSL_structVal___closed__13_value;
static const lean_ctor_object l_Lake_DSL_structVal___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_structVal___closed__0_value),((lean_object*)&l_Lake_DSL_structVal___closed__1_value),((lean_object*)&l_Lake_DSL_structVal___closed__13_value)}};
static const lean_object* l_Lake_DSL_structVal___closed__14 = (const lean_object*)&l_Lake_DSL_structVal___closed__14_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_structVal = (const lean_object*)&l_Lake_DSL_structVal___closed__14_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declValDo"};
static const lean_object* l_Lake_DSL_declValDo___closed__0 = (const lean_object*)&l_Lake_DSL_declValDo___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declValDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 210, 120, 194, 116, 135, 247, 152)}};
static const lean_object* l_Lake_DSL_declValDo___closed__1 = (const lean_object*)&l_Lake_DSL_declValDo___closed__1_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lake_DSL_declValDo___closed__2 = (const lean_object*)&l_Lake_DSL_declValDo___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declValDo___closed__2_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lake_DSL_declValDo___closed__3 = (const lean_object*)&l_Lake_DSL_declValDo___closed__3_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__3_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__4 = (const lean_object*)&l_Lake_DSL_declValDo___closed__4_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lake_DSL_declValDo___closed__5 = (const lean_object*)&l_Lake_DSL_declValDo___closed__5_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value_aux_2),((lean_object*)&l_Lake_DSL_declValDo___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l_Lake_DSL_declValDo___closed__6 = (const lean_object*)&l_Lake_DSL_declValDo___closed__6_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__6_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__7 = (const lean_object*)&l_Lake_DSL_declValDo___closed__7_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValDo___closed__4_value),((lean_object*)&l_Lake_DSL_declValDo___closed__7_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__8 = (const lean_object*)&l_Lake_DSL_declValDo___closed__8_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lake_DSL_declValDo___closed__9 = (const lean_object*)&l_Lake_DSL_declValDo___closed__9_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_declValDo___closed__9_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lake_DSL_declValDo___closed__10 = (const lean_object*)&l_Lake_DSL_declValDo___closed__10_value;
static const lean_string_object l_Lake_DSL_declValDo___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l_Lake_DSL_declValDo___closed__11 = (const lean_object*)&l_Lake_DSL_declValDo___closed__11_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_declValDo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value_aux_2),((lean_object*)&l_Lake_DSL_declValDo___closed__11_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l_Lake_DSL_declValDo___closed__12 = (const lean_object*)&l_Lake_DSL_declValDo___closed__12_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__12_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__13 = (const lean_object*)&l_Lake_DSL_declValDo___closed__13_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__10_value),((lean_object*)&l_Lake_DSL_declValDo___closed__13_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__14 = (const lean_object*)&l_Lake_DSL_declValDo___closed__14_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValDo___closed__8_value),((lean_object*)&l_Lake_DSL_declValDo___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__15 = (const lean_object*)&l_Lake_DSL_declValDo___closed__15_value;
static const lean_ctor_object l_Lake_DSL_declValDo___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__0_value),((lean_object*)&l_Lake_DSL_declValDo___closed__1_value),((lean_object*)&l_Lake_DSL_declValDo___closed__15_value)}};
static const lean_object* l_Lake_DSL_declValDo___closed__16 = (const lean_object*)&l_Lake_DSL_declValDo___closed__16_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declValDo = (const lean_object*)&l_Lake_DSL_declValDo___closed__16_value;
static const lean_string_object l_Lake_DSL_declValStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValStruct"};
static const lean_object* l_Lake_DSL_declValStruct___closed__0 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValStruct___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValStruct___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declValStruct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 214, 189, 204, 150, 4, 239, 13)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__1 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__1_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValDo___closed__4_value),((lean_object*)&l_Lake_DSL_structVal___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__2 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__2_value),((lean_object*)&l_Lake_DSL_declValDo___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__3 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__3_value;
static const lean_ctor_object l_Lake_DSL_declValStruct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declValStruct___closed__0_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__1_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__3_value)}};
static const lean_object* l_Lake_DSL_declValStruct___closed__4 = (const lean_object*)&l_Lake_DSL_declValStruct___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declValStruct = (const lean_object*)&l_Lake_DSL_declValStruct___closed__4_value;
static const lean_string_object l_Lake_DSL_declValWhere___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declValWhere"};
static const lean_object* l_Lake_DSL_declValWhere___closed__0 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__0_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_declValWhere___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 133, 86, 223, 245, 102, 246, 81)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__1 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__1_value;
static const lean_string_object l_Lake_DSL_declValWhere___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " where "};
static const lean_object* l_Lake_DSL_declValWhere___closed__2 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__2_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__2_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__3 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__3_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__3_value),((lean_object*)&l_Lake_DSL_structVal___closed__9_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__4 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__4_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__4_value),((lean_object*)&l_Lake_DSL_declValDo___closed__14_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__5 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__5_value;
static const lean_ctor_object l_Lake_DSL_declValWhere___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_declValWhere___closed__0_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__1_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__5_value)}};
static const lean_object* l_Lake_DSL_declValWhere___closed__6 = (const lean_object*)&l_Lake_DSL_declValWhere___closed__6_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_declValWhere = (const lean_object*)&l_Lake_DSL_declValWhere___closed__6_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpleDeclSig"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__0 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__0_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 30, 135, 149, 186, 116, 70, 7)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__1 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__2 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__2_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value_aux_2),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__3 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__3_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__4 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__4_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__4_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__5 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__5_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__6 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value;
static const lean_string_object l_Lake_DSL_simpleDeclSig___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__7 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__7_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value_aux_2),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__7_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__8 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__8_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__9 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__9_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__5_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__9_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__10 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__10_value;
static const lean_ctor_object l_Lake_DSL_simpleDeclSig___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__0_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__1_value),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__10_value)}};
static const lean_object* l_Lake_DSL_simpleDeclSig___closed__11 = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__11_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_simpleDeclSig = (const lean_object*)&l_Lake_DSL_simpleDeclSig___closed__11_value;
static const lean_string_object l_Lake_DSL_optConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_DSL_optConfig___closed__0 = (const lean_object*)&l_Lake_DSL_optConfig___closed__0_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_optConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_optConfig___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_optConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_optConfig___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_optConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_DSL_optConfig___closed__1 = (const lean_object*)&l_Lake_DSL_optConfig___closed__1_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__5_value),((lean_object*)&l_Lake_DSL_declValWhere___closed__6_value),((lean_object*)&l_Lake_DSL_declValStruct___closed__4_value)}};
static const lean_object* l_Lake_DSL_optConfig___closed__2 = (const lean_object*)&l_Lake_DSL_optConfig___closed__2_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__10_value),((lean_object*)&l_Lake_DSL_optConfig___closed__2_value)}};
static const lean_object* l_Lake_DSL_optConfig___closed__3 = (const lean_object*)&l_Lake_DSL_optConfig___closed__3_value;
static const lean_ctor_object l_Lake_DSL_optConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_optConfig___closed__0_value),((lean_object*)&l_Lake_DSL_optConfig___closed__1_value),((lean_object*)&l_Lake_DSL_optConfig___closed__3_value)}};
static const lean_object* l_Lake_DSL_optConfig___closed__4 = (const lean_object*)&l_Lake_DSL_optConfig___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_optConfig = (const lean_object*)&l_Lake_DSL_optConfig___closed__4_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "bracketedSimpleBinder"};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__0 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 236, 129, 27, 124, 223, 134, 77)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__1 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__2 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__2_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__2_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__3 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__3_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__3_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__4 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__4_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__5 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__5_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__5_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__6 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__6_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__6_value),((lean_object*)&l_Lake_DSL_declField___closed__9_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__7 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__7_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_declValDo___closed__10_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__7_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__8 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__8_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__4_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__8_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__9 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__9_value;
static const lean_string_object l_Lake_DSL_bracketedSimpleBinder___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__10 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__10_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__10_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__11 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__11_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_declField___closed__3_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__9_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__11_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__12 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__12_value;
static const lean_ctor_object l_Lake_DSL_bracketedSimpleBinder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__0_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__1_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__12_value)}};
static const lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__13 = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__13_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_bracketedSimpleBinder = (const lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__13_value;
static const lean_string_object l_Lake_DSL_simpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpleBinder"};
static const lean_object* l_Lake_DSL_simpleBinder___closed__0 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_simpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 16, 244, 231, 102, 138, 237, 36)}};
static const lean_object* l_Lake_DSL_simpleBinder___closed__1 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value;
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_DSL_identOrStr___closed__5_value),((lean_object*)&l_Lake_DSL_identOrStr___closed__8_value),((lean_object*)&l_Lake_DSL_bracketedSimpleBinder___closed__13_value)}};
static const lean_object* l_Lake_DSL_simpleBinder___closed__2 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__2_value;
static const lean_ctor_object l_Lake_DSL_simpleBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lake_DSL_simpleBinder___closed__0_value),((lean_object*)&l_Lake_DSL_simpleBinder___closed__1_value),((lean_object*)&l_Lake_DSL_simpleBinder___closed__2_value)}};
static const lean_object* l_Lake_DSL_simpleBinder___closed__3 = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_simpleBinder = (const lean_object*)&l_Lake_DSL_simpleBinder___closed__3_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__0 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value_aux_2),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__1 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__1_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__2 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__2_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__3 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__3_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value_aux_2),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__4 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__4_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__5 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__5_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value_aux_2),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__6 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__6_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__7 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__7_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__8 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__8_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__9 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__9_value;
static lean_once_cell_t l_Lake_DSL_expandOptSimpleBinder___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__10;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_identOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__11_value_aux_0),((lean_object*)&l_Lake_DSL_identOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__11 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__11_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__11_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__12 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__12_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__13 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__13_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__14 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__14_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__15 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__15_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__16 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__16_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__17_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__17 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__17_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__17_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__18 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__18_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__19 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__19_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__19_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__20 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__20_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__21 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__21_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__18_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__21_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__22 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__22_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__16_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__22_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__23 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__23_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__14_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__23_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__24 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__24_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__12_value),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__24_value)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__25 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__25_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__26 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__26_value;
static const lean_string_object l_Lake_DSL_expandOptSimpleBinder___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__27 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__27_value;
static const lean_ctor_object l_Lake_DSL_expandOptSimpleBinder___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__27_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_DSL_expandOptSimpleBinder___closed__28 = (const lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__28_value;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "ill-formed field declaration syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "redefined field '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "' ('"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "' is an alias of '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "')"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unknown '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "' field '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_1),((lean_object*)&l_Lake_DSL_expandAttrs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value_aux_2),((lean_object*)&l_Lake_DSL_structVal___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0 = (const lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0_value;
static const lean_array_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1 = (const lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandOptSimpleBinder___closed__28_value),((lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__1_value)}};
static const lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2 = (const lean_object*)&l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_DSL_elabConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake_DSL_elabConfig___closed__0 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__0_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake_DSL_elabConfig___closed__1 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__1_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lake_DSL_elabConfig___closed__2 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__2_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lake_DSL_elabConfig___closed__3 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__3_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake_DSL_elabConfig___closed__4 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__4_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lake_DSL_elabConfig___closed__5 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__5_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__6;
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__7;
static const lean_closure_object l_Lake_DSL_elabConfig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_elabConfig___closed__8 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__8_value;
static const lean_closure_object l_Lake_DSL_elabConfig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_elabConfig___closed__9 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__9_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l_Lake_DSL_elabConfig___closed__10 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__10_value;
static const lean_string_object l_Lake_DSL_elabConfig___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l_Lake_DSL_elabConfig___closed__11 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__11_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_expandAttrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_expandAttrs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___closed__12_value_aux_1),((lean_object*)&l_Lake_DSL_simpleDeclSig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___closed__12_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___closed__11_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l_Lake_DSL_elabConfig___closed__12 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__12_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__13;
static const lean_string_object l_Lake_DSL_elabConfig___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed configuration syntax"};
static const lean_object* l_Lake_DSL_elabConfig___closed__14 = (const lean_object*)&l_Lake_DSL_elabConfig___closed__14_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___closed__15;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object* v_attrs_x3f_16_){
_start:
{
if (lean_obj_tag(v_attrs_x3f_16_) == 1)
{
lean_object* v_val_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v_val_17_ = lean_ctor_get(v_attrs_x3f_16_, 0);
lean_inc_n(v_val_17_, 2);
lean_dec_ref(v_attrs_x3f_16_);
v___x_18_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__4));
v___x_19_ = l_Lean_Syntax_isOfKind(v_val_17_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
lean_dec(v_val_17_);
v___x_20_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
return v___x_20_;
}
else
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_attrs_23_; lean_object* v___x_24_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = l_Lean_Syntax_getArg(v_val_17_, v___x_21_);
lean_dec(v_val_17_);
v_attrs_23_ = l_Lean_Syntax_getArgs(v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_attrs_23_);
lean_dec_ref(v_attrs_23_);
return v___x_24_;
}
}
else
{
lean_object* v___x_25_; 
lean_dec(v_attrs_x3f_16_);
v___x_25_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object* v_stx_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lake_DSL_identOrStr___closed__3));
lean_inc(v_stx_55_);
v___x_57_ = l_Lean_Syntax_isOfKind(v_stx_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec(v_stx_55_);
v___x_58_ = lean_box(0);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v_x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v_x_60_ = l_Lean_Syntax_getArg(v_stx_55_, v___x_59_);
lean_dec(v_stx_55_);
v___x_61_ = ((lean_object*)(l_Lake_DSL_identOrStr___closed__7));
lean_inc(v_x_60_);
v___x_62_ = l_Lean_Syntax_isOfKind(v_x_60_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lake_DSL_identOrStr___closed__10));
lean_inc(v_x_60_);
v___x_64_ = l_Lean_Syntax_isOfKind(v_x_60_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec(v_x_60_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = l_Lean_TSyntax_getString(v_x_60_);
v___x_67_ = lean_box(0);
v___x_68_ = l_Lean_Name_str___override(v___x_67_, v___x_66_);
v___x_69_ = l_Lean_mkIdentFrom(v_x_60_, v___x_68_, v___x_62_);
lean_dec(v_x_60_);
return v___x_69_;
}
}
else
{
return v_x_60_;
}
}
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___closed__10(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__9));
v___x_348_ = l_String_toRawSubstring_x27(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object* v_stx_x3f_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
if (lean_obj_tag(v_stx_x3f_394_) == 0)
{
lean_object* v_ref_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_ref_397_ = lean_ctor_get(v_a_395_, 5);
v___x_398_ = 0;
v___x_399_ = l_Lean_SourceInfo_fromRef(v_ref_397_, v___x_398_);
v___x_400_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
v___x_401_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(v___x_399_);
v___x_402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_399_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_Syntax_node1(v___x_399_, v___x_400_, v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_396_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_493_; 
v_val_405_ = lean_ctor_get(v_stx_x3f_394_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_stx_x3f_394_);
if (v_isSharedCheck_493_ == 0)
{
v___x_407_ = v_stx_x3f_394_;
v_isShared_408_ = v_isSharedCheck_493_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v_stx_x3f_394_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_493_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lake_DSL_simpleBinder___closed__1));
lean_inc(v_val_405_);
v___x_410_ = l_Lean_Syntax_isOfKind(v_val_405_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v_ref_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_del_object(v___x_407_);
lean_dec(v_val_405_);
v_ref_411_ = lean_ctor_get(v_a_395_, 5);
v___x_412_ = l_Lean_SourceInfo_fromRef(v_ref_411_, v___x_410_);
v___x_413_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
v___x_414_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(v___x_412_);
v___x_415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_412_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = l_Lean_Syntax_node1(v___x_412_, v___x_413_, v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v_a_396_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = l_Lean_Syntax_getArg(v_val_405_, v___x_418_);
lean_dec(v_val_405_);
v___x_420_ = ((lean_object*)(l_Lake_DSL_identOrStr___closed__7));
lean_inc(v___x_419_);
v___x_421_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lake_DSL_bracketedSimpleBinder___closed__1));
lean_inc(v___x_419_);
v___x_423_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v_ref_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v___x_419_);
lean_del_object(v___x_407_);
v_ref_424_ = lean_ctor_get(v_a_395_, 5);
v___x_425_ = l_Lean_SourceInfo_fromRef(v_ref_424_, v___x_421_);
v___x_426_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
v___x_427_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(v___x_425_);
v___x_428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_425_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_Syntax_node1(v___x_425_, v___x_426_, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_a_396_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___y_434_; lean_object* v_quotContext_435_; lean_object* v_currMacroScope_436_; lean_object* v_ref_437_; lean_object* v___y_438_; lean_object* v_ty_x3f_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = l_Lean_Syntax_getArg(v___x_419_, v___x_431_);
v___x_476_ = lean_unsigned_to_nat(2u);
v___x_477_ = l_Lean_Syntax_getArg(v___x_419_, v___x_476_);
lean_dec(v___x_419_);
v___x_478_ = l_Lean_Syntax_isNone(v___x_477_);
if (v___x_478_ == 0)
{
uint8_t v___x_479_; 
lean_inc(v___x_477_);
v___x_479_ = l_Lean_Syntax_matchesNull(v___x_477_, v___x_476_);
if (v___x_479_ == 0)
{
lean_object* v_ref_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v___x_477_);
lean_dec(v___x_432_);
lean_del_object(v___x_407_);
v_ref_480_ = lean_ctor_get(v_a_395_, 5);
v___x_481_ = l_Lean_SourceInfo_fromRef(v_ref_480_, v___x_421_);
v___x_482_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
v___x_483_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(v___x_481_);
v___x_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_481_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = l_Lean_Syntax_node1(v___x_481_, v___x_482_, v___x_484_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_396_);
return v___x_486_;
}
else
{
lean_object* v_ty_x3f_487_; lean_object* v___x_489_; 
v_ty_x3f_487_ = l_Lean_Syntax_getArg(v___x_477_, v___x_431_);
lean_dec(v___x_477_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v_ty_x3f_487_);
v___x_489_ = v___x_407_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_ty_x3f_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v_ty_x3f_461_ = v___x_489_;
v___y_462_ = v_a_395_;
v___y_463_ = v_a_396_;
goto v___jp_460_;
}
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v___x_477_);
lean_del_object(v___x_407_);
v___x_491_ = lean_box(0);
v_ty_x3f_461_ = v___x_491_;
v___y_462_ = v_a_395_;
v___y_463_ = v_a_396_;
goto v___jp_460_;
}
v___jp_433_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_439_ = l_Lean_SourceInfo_fromRef(v_ref_437_, v___x_421_);
v___x_440_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__4));
v___x_441_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__6));
v___x_442_ = ((lean_object*)(l_Lake_DSL_bracketedSimpleBinder___closed__2));
lean_inc_n(v___x_439_, 7);
v___x_443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_439_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__8));
v___x_445_ = lean_obj_once(&l_Lake_DSL_expandOptSimpleBinder___closed__10, &l_Lake_DSL_expandOptSimpleBinder___closed__10_once, _init_l_Lake_DSL_expandOptSimpleBinder___closed__10);
v___x_446_ = lean_box(0);
lean_inc(v_currMacroScope_436_);
lean_inc(v_quotContext_435_);
v___x_447_ = l_Lean_addMacroScope(v_quotContext_435_, v___x_446_, v_currMacroScope_436_);
v___x_448_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__25));
v___x_449_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_449_, 0, v___x_439_);
lean_ctor_set(v___x_449_, 1, v___x_445_);
lean_ctor_set(v___x_449_, 2, v___x_447_);
lean_ctor_set(v___x_449_, 3, v___x_448_);
v___x_450_ = l_Lean_Syntax_node1(v___x_439_, v___x_444_, v___x_449_);
v___x_451_ = l_Lean_Syntax_node2(v___x_439_, v___x_441_, v___x_443_, v___x_450_);
v___x_452_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__26));
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_439_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
v___x_455_ = l_Lean_Syntax_node1(v___x_439_, v___x_454_, v___y_438_);
v___x_456_ = ((lean_object*)(l_Lake_DSL_bracketedSimpleBinder___closed__10));
v___x_457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_439_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_Syntax_node5(v___x_439_, v___x_440_, v___x_451_, v___x_432_, v___x_453_, v___x_455_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___y_434_);
return v___x_459_;
}
v___jp_460_:
{
if (lean_obj_tag(v_ty_x3f_461_) == 0)
{
lean_object* v_quotContext_464_; lean_object* v_currMacroScope_465_; lean_object* v_ref_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_quotContext_464_ = lean_ctor_get(v___y_462_, 1);
v_currMacroScope_465_ = lean_ctor_get(v___y_462_, 2);
v_ref_466_ = lean_ctor_get(v___y_462_, 5);
v___x_467_ = l_Lean_SourceInfo_fromRef(v_ref_466_, v___x_421_);
v___x_468_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__2));
lean_inc(v___x_467_);
v___x_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__1));
v___x_471_ = l_Lean_Syntax_node1(v___x_467_, v___x_470_, v___x_469_);
v___y_434_ = v___y_463_;
v_quotContext_435_ = v_quotContext_464_;
v_currMacroScope_436_ = v_currMacroScope_465_;
v_ref_437_ = v_ref_466_;
v___y_438_ = v___x_471_;
goto v___jp_433_;
}
else
{
lean_object* v_quotContext_472_; lean_object* v_currMacroScope_473_; lean_object* v_ref_474_; lean_object* v_val_475_; 
v_quotContext_472_ = lean_ctor_get(v___y_462_, 1);
v_currMacroScope_473_ = lean_ctor_get(v___y_462_, 2);
v_ref_474_ = lean_ctor_get(v___y_462_, 5);
v_val_475_ = lean_ctor_get(v_ty_x3f_461_, 0);
lean_inc(v_val_475_);
lean_dec_ref(v_ty_x3f_461_);
v___y_434_ = v___y_463_;
v_quotContext_435_ = v_quotContext_472_;
v_currMacroScope_436_ = v_currMacroScope_473_;
v_ref_437_ = v_ref_474_;
v___y_438_ = v_val_475_;
goto v___jp_433_;
}
}
}
}
else
{
lean_object* v___x_492_; 
lean_del_object(v___x_407_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_419_);
lean_ctor_set(v___x_492_, 1, v_a_396_);
return v___x_492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___boxed(lean_object* v_stx_x3f_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lake_DSL_expandOptSimpleBinder(v_stx_x3f_494_, v_a_495_, v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_497_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0(void){
_start:
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = 0;
v___x_499_ = lean_box(0);
v___x_500_ = l_Lean_SourceInfo_fromRef(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Array_mkArray0(lean_box(0));
return v___x_513_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
v___x_515_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
v___x_516_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
v___x_517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___x_515_);
lean_ctor_set(v___x_517_, 2, v___x_514_);
return v___x_517_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__9));
v___x_526_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(lean_object* v_init_528_, lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_k_531_; lean_object* v_v_532_; lean_object* v_l_533_; lean_object* v_r_534_; lean_object* v___x_535_; lean_object* v_a_536_; lean_object* v_ref_537_; lean_object* v_val_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_k_531_ = lean_ctor_get(v_x_529_, 1);
lean_inc(v_k_531_);
v_v_532_ = lean_ctor_get(v_x_529_, 2);
lean_inc(v_v_532_);
v_l_533_ = lean_ctor_get(v_x_529_, 3);
lean_inc(v_l_533_);
v_r_534_ = lean_ctor_get(v_x_529_, 4);
lean_inc(v_r_534_);
lean_dec_ref(v_x_529_);
v___x_535_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_528_, v_l_533_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v_ref_537_ = lean_ctor_get(v_v_532_, 0);
lean_inc(v_ref_537_);
v_val_538_ = lean_ctor_get(v_v_532_, 1);
lean_inc(v_val_538_);
lean_dec(v_v_532_);
v___x_539_ = 1;
v___x_540_ = l_Lean_mkIdentFrom(v_ref_537_, v_k_531_, v___x_539_);
lean_dec(v_ref_537_);
v___x_541_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__0);
v___x_542_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__2));
v___x_543_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__4));
v___x_544_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
v___x_545_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__6);
v___x_546_ = l_Lean_Syntax_node2(v___x_541_, v___x_543_, v___x_540_, v___x_545_);
v___x_547_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__8));
v___x_548_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__10);
v___x_549_ = l_Lean_Syntax_node3(v___x_541_, v___x_547_, v___x_548_, v___x_545_, v_val_538_);
v___x_550_ = l_Lean_Syntax_node3(v___x_541_, v___x_544_, v___x_545_, v___x_545_, v___x_549_);
v___x_551_ = l_Lean_Syntax_node2(v___x_541_, v___x_542_, v___x_546_, v___x_550_);
v___x_552_ = lean_array_push(v_a_536_, v___x_551_);
v_init_528_ = v___x_552_;
v_x_529_ = v_r_534_;
goto _start;
}
else
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_init_528_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___boxed(lean_object* v_init_555_, lean_object* v_x_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_555_, v_x_556_);
return v_res_558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(lean_object* v_opts_559_, lean_object* v_opt_560_){
_start:
{
lean_object* v_name_561_; lean_object* v_defValue_562_; lean_object* v_map_563_; lean_object* v___x_564_; 
v_name_561_ = lean_ctor_get(v_opt_560_, 0);
v_defValue_562_ = lean_ctor_get(v_opt_560_, 1);
v_map_563_ = lean_ctor_get(v_opts_559_, 0);
v___x_564_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_563_, v_name_561_);
if (lean_obj_tag(v___x_564_) == 0)
{
uint8_t v___x_565_; 
v___x_565_ = lean_unbox(v_defValue_562_);
return v___x_565_;
}
else
{
lean_object* v_val_566_; 
v_val_566_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_566_);
lean_dec_ref(v___x_564_);
if (lean_obj_tag(v_val_566_) == 1)
{
uint8_t v_v_567_; 
v_v_567_ = lean_ctor_get_uint8(v_val_566_, 0);
lean_dec_ref(v_val_566_);
return v_v_567_;
}
else
{
uint8_t v___x_568_; 
lean_dec(v_val_566_);
v___x_568_ = lean_unbox(v_defValue_562_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8___boxed(lean_object* v_opts_569_, lean_object* v_opt_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_569_, v_opt_570_);
lean_dec_ref(v_opt_570_);
lean_dec_ref(v_opts_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t v___y_574_, uint8_t v_suppressElabErrors_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 1)
{
lean_object* v_pre_577_; 
v_pre_577_ = lean_ctor_get(v_x_576_, 0);
if (lean_obj_tag(v_pre_577_) == 0)
{
lean_object* v_str_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_str_578_ = lean_ctor_get(v_x_576_, 1);
v___x_579_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0));
v___x_580_ = lean_string_dec_eq(v_str_578_, v___x_579_);
if (v___x_580_ == 0)
{
return v___y_574_;
}
else
{
return v_suppressElabErrors_575_;
}
}
else
{
return v___y_574_;
}
}
else
{
return v___y_574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object* v___y_581_, lean_object* v_suppressElabErrors_582_, lean_object* v_x_583_){
_start:
{
uint8_t v___y_9364__boxed_584_; uint8_t v_suppressElabErrors_boxed_585_; uint8_t v_res_586_; lean_object* v_r_587_; 
v___y_9364__boxed_584_ = lean_unbox(v___y_581_);
v_suppressElabErrors_boxed_585_ = lean_unbox(v_suppressElabErrors_582_);
v_res_586_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(v___y_9364__boxed_584_, v_suppressElabErrors_boxed_585_, v_x_583_);
lean_dec(v_x_583_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_588_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
lean_ctor_set(v___x_593_, 3, v___x_592_);
lean_ctor_set(v___x_593_, 4, v___x_591_);
lean_ctor_set(v___x_593_, 5, v___x_591_);
lean_ctor_set(v___x_593_, 6, v___x_591_);
lean_ctor_set(v___x_593_, 7, v___x_591_);
lean_ctor_set(v___x_593_, 8, v___x_591_);
lean_ctor_set(v___x_593_, 9, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_unsigned_to_nat(32u);
v___x_595_ = lean_mk_empty_array_with_capacity(v___x_594_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = ((size_t)5ULL);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_unsigned_to_nat(32u);
v___x_600_ = lean_mk_empty_array_with_capacity(v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_602_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
lean_ctor_set(v___x_602_, 2, v___x_598_);
lean_ctor_set(v___x_602_, 3, v___x_598_);
lean_ctor_set_usize(v___x_602_, 4, v___x_597_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_603_ = lean_box(1);
v___x_604_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_605_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
lean_ctor_set(v___x_606_, 2, v___x_603_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; lean_object* v_env_611_; lean_object* v___x_612_; lean_object* v_scopes_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_opts_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_610_ = lean_st_ref_get(v___y_608_);
v_env_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_611_);
lean_dec(v___x_610_);
v___x_612_ = lean_st_ref_get(v___y_608_);
v_scopes_613_ = lean_ctor_get(v___x_612_, 2);
lean_inc(v_scopes_613_);
lean_dec(v___x_612_);
v___x_614_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_615_ = l_List_head_x21___redArg(v___x_614_, v_scopes_613_);
lean_dec(v_scopes_613_);
v_opts_616_ = lean_ctor_get(v___x_615_, 1);
lean_inc_ref(v_opts_616_);
lean_dec(v___x_615_);
v___x_617_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_618_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5);
v___x_619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_619_, 0, v_env_611_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_618_);
lean_ctor_set(v___x_619_, 3, v_opts_616_);
v___x_620_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_msgData_607_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_622_, v___y_623_);
lean_dec(v___y_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(lean_object* v_ref_626_, lean_object* v_msgData_627_, uint8_t v_severity_628_, uint8_t v_isSilent_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___y_634_; uint8_t v___y_635_; lean_object* v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; uint8_t v___y_697_; lean_object* v___y_698_; uint8_t v___y_699_; uint8_t v___y_700_; lean_object* v___y_701_; uint8_t v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; uint8_t v___y_733_; uint8_t v___y_734_; uint8_t v___y_735_; uint8_t v___x_750_; uint8_t v___y_752_; uint8_t v___y_753_; uint8_t v___y_754_; uint8_t v___y_756_; uint8_t v___x_768_; 
v___x_750_ = 2;
v___x_768_ = l_Lean_instBEqMessageSeverity_beq(v_severity_628_, v___x_750_);
if (v___x_768_ == 0)
{
v___y_756_ = v___x_768_;
goto v___jp_755_;
}
else
{
uint8_t v___x_769_; 
lean_inc_ref(v_msgData_627_);
v___x_769_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_627_);
v___y_756_ = v___x_769_;
goto v___jp_755_;
}
v___jp_633_:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Elab_Command_getScope___redArg(v___y_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v___x_642_);
v___x_644_ = l_Lean_Elab_Command_getScope___redArg(v___y_641_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_679_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_679_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_679_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_679_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v_currNamespace_650_; lean_object* v_openDecls_651_; lean_object* v_env_652_; lean_object* v_messages_653_; lean_object* v_scopes_654_; lean_object* v_usedQuotCtxts_655_; lean_object* v_nextMacroScope_656_; lean_object* v_maxRecDepth_657_; lean_object* v_ngen_658_; lean_object* v_auxDeclNGen_659_; lean_object* v_infoState_660_; lean_object* v_traceState_661_; lean_object* v_snapshotTasks_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_678_; 
v___x_649_ = lean_st_ref_take(v___y_641_);
v_currNamespace_650_ = lean_ctor_get(v_a_643_, 2);
lean_inc(v_currNamespace_650_);
lean_dec(v_a_643_);
v_openDecls_651_ = lean_ctor_get(v_a_645_, 3);
lean_inc(v_openDecls_651_);
lean_dec(v_a_645_);
v_env_652_ = lean_ctor_get(v___x_649_, 0);
v_messages_653_ = lean_ctor_get(v___x_649_, 1);
v_scopes_654_ = lean_ctor_get(v___x_649_, 2);
v_usedQuotCtxts_655_ = lean_ctor_get(v___x_649_, 3);
v_nextMacroScope_656_ = lean_ctor_get(v___x_649_, 4);
v_maxRecDepth_657_ = lean_ctor_get(v___x_649_, 5);
v_ngen_658_ = lean_ctor_get(v___x_649_, 6);
v_auxDeclNGen_659_ = lean_ctor_get(v___x_649_, 7);
v_infoState_660_ = lean_ctor_get(v___x_649_, 8);
v_traceState_661_ = lean_ctor_get(v___x_649_, 9);
v_snapshotTasks_662_ = lean_ctor_get(v___x_649_, 10);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_678_ == 0)
{
v___x_664_ = v___x_649_;
v_isShared_665_ = v_isSharedCheck_678_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snapshotTasks_662_);
lean_inc(v_traceState_661_);
lean_inc(v_infoState_660_);
lean_inc(v_auxDeclNGen_659_);
lean_inc(v_ngen_658_);
lean_inc(v_maxRecDepth_657_);
lean_inc(v_nextMacroScope_656_);
lean_inc(v_usedQuotCtxts_655_);
lean_inc(v_scopes_654_);
lean_inc(v_messages_653_);
lean_inc(v_env_652_);
lean_dec(v___x_649_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_678_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_currNamespace_650_);
lean_ctor_set(v___x_666_, 1, v_openDecls_651_);
v___x_667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___y_640_);
lean_inc_ref(v___y_634_);
lean_inc_ref(v___y_639_);
v___x_668_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_668_, 0, v___y_639_);
lean_ctor_set(v___x_668_, 1, v___y_636_);
lean_ctor_set(v___x_668_, 2, v___y_638_);
lean_ctor_set(v___x_668_, 3, v___y_634_);
lean_ctor_set(v___x_668_, 4, v___x_667_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*5, v___y_637_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*5 + 1, v___y_635_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*5 + 2, v_isSilent_629_);
v___x_669_ = l_Lean_MessageLog_add(v___x_668_, v_messages_653_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v___x_669_);
v___x_671_ = v___x_664_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_env_652_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_scopes_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_usedQuotCtxts_655_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_nextMacroScope_656_);
lean_ctor_set(v_reuseFailAlloc_677_, 5, v_maxRecDepth_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 6, v_ngen_658_);
lean_ctor_set(v_reuseFailAlloc_677_, 7, v_auxDeclNGen_659_);
lean_ctor_set(v_reuseFailAlloc_677_, 8, v_infoState_660_);
lean_ctor_set(v_reuseFailAlloc_677_, 9, v_traceState_661_);
lean_ctor_set(v_reuseFailAlloc_677_, 10, v_snapshotTasks_662_);
v___x_671_ = v_reuseFailAlloc_677_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = lean_st_ref_set(v___y_641_, v___x_671_);
v___x_673_ = lean_box(0);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_673_);
v___x_675_ = v___x_647_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_a_643_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_636_);
v_a_680_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_644_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_644_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v___y_640_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_636_);
v_a_688_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_642_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_642_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
v___jp_696_:
{
lean_object* v_fileName_702_; lean_object* v_fileMap_703_; uint8_t v_suppressElabErrors_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_723_; 
v_fileName_702_ = lean_ctor_get(v___y_630_, 0);
v_fileMap_703_ = lean_ctor_get(v___y_630_, 1);
v_suppressElabErrors_704_ = lean_ctor_get_uint8(v___y_630_, sizeof(void*)*10);
v___x_705_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_627_);
v___x_706_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v___x_705_, v___y_631_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_723_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_723_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_723_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_inc_ref_n(v_fileMap_703_, 2);
v___x_711_ = l_Lean_FileMap_toPosition(v_fileMap_703_, v___y_698_);
lean_dec(v___y_698_);
v___x_712_ = l_Lean_FileMap_toPosition(v_fileMap_703_, v___y_701_);
lean_dec(v___y_701_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
v___x_714_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__9));
if (v_suppressElabErrors_704_ == 0)
{
lean_del_object(v___x_709_);
v___y_634_ = v___x_714_;
v___y_635_ = v___y_699_;
v___y_636_ = v___x_711_;
v___y_637_ = v___y_700_;
v___y_638_ = v___x_713_;
v___y_639_ = v_fileName_702_;
v___y_640_ = v_a_707_;
v___y_641_ = v___y_631_;
goto v___jp_633_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___f_717_; uint8_t v___x_718_; 
v___x_715_ = lean_box(v___y_697_);
v___x_716_ = lean_box(v_suppressElabErrors_704_);
v___f_717_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_717_, 0, v___x_715_);
lean_closure_set(v___f_717_, 1, v___x_716_);
lean_inc(v_a_707_);
v___x_718_ = l_Lean_MessageData_hasTag(v___f_717_, v_a_707_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_dec(v_a_707_);
v___x_719_ = lean_box(0);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_719_);
v___x_721_ = v___x_709_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
else
{
lean_del_object(v___x_709_);
v___y_634_ = v___x_714_;
v___y_635_ = v___y_699_;
v___y_636_ = v___x_711_;
v___y_637_ = v___y_700_;
v___y_638_ = v___x_713_;
v___y_639_ = v_fileName_702_;
v___y_640_ = v_a_707_;
v___y_641_ = v___y_631_;
goto v___jp_633_;
}
}
}
}
v___jp_724_:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Syntax_getTailPos_x3f(v___y_726_, v___y_728_);
lean_dec(v___y_726_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_inc(v___y_729_);
v___y_697_ = v___y_725_;
v___y_698_ = v___y_729_;
v___y_699_ = v___y_727_;
v___y_700_ = v___y_728_;
v___y_701_ = v___y_729_;
goto v___jp_696_;
}
else
{
lean_object* v_val_731_; 
v_val_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref(v___x_730_);
v___y_697_ = v___y_725_;
v___y_698_ = v___y_729_;
v___y_699_ = v___y_727_;
v___y_700_ = v___y_728_;
v___y_701_ = v_val_731_;
goto v___jp_696_;
}
}
v___jp_732_:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Elab_Command_getRef___redArg(v___y_630_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v_ref_738_; lean_object* v___x_739_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v_ref_738_ = l_Lean_replaceRef(v_ref_626_, v_a_737_);
lean_dec(v_a_737_);
v___x_739_ = l_Lean_Syntax_getPos_x3f(v_ref_738_, v___y_734_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___y_725_ = v___y_733_;
v___y_726_ = v_ref_738_;
v___y_727_ = v___y_735_;
v___y_728_ = v___y_734_;
v___y_729_ = v___x_740_;
goto v___jp_724_;
}
else
{
lean_object* v_val_741_; 
v_val_741_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_741_);
lean_dec_ref(v___x_739_);
v___y_725_ = v___y_733_;
v___y_726_ = v_ref_738_;
v___y_727_ = v___y_735_;
v___y_728_ = v___y_734_;
v___y_729_ = v_val_741_;
goto v___jp_724_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_msgData_627_);
v_a_742_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_736_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_736_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
v___jp_751_:
{
if (v___y_754_ == 0)
{
v___y_733_ = v___y_752_;
v___y_734_ = v___y_753_;
v___y_735_ = v_severity_628_;
goto v___jp_732_;
}
else
{
v___y_733_ = v___y_752_;
v___y_734_ = v___y_753_;
v___y_735_ = v___x_750_;
goto v___jp_732_;
}
}
v___jp_755_:
{
if (v___y_756_ == 0)
{
lean_object* v___x_757_; lean_object* v_scopes_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_opts_761_; uint8_t v___x_762_; uint8_t v___x_763_; 
v___x_757_ = lean_st_ref_get(v___y_631_);
v_scopes_758_ = lean_ctor_get(v___x_757_, 2);
lean_inc(v_scopes_758_);
lean_dec(v___x_757_);
v___x_759_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_760_ = l_List_head_x21___redArg(v___x_759_, v_scopes_758_);
lean_dec(v_scopes_758_);
v_opts_761_ = lean_ctor_get(v___x_760_, 1);
lean_inc_ref(v_opts_761_);
lean_dec(v___x_760_);
v___x_762_ = 1;
v___x_763_ = l_Lean_instBEqMessageSeverity_beq(v_severity_628_, v___x_762_);
if (v___x_763_ == 0)
{
lean_dec_ref(v_opts_761_);
v___y_752_ = v___y_756_;
v___y_753_ = v___y_756_;
v___y_754_ = v___x_763_;
goto v___jp_751_;
}
else
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = l_Lean_warningAsError;
v___x_765_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_761_, v___x_764_);
lean_dec_ref(v_opts_761_);
v___y_752_ = v___y_756_;
v___y_753_ = v___y_756_;
v___y_754_ = v___x_765_;
goto v___jp_751_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref(v_msgData_627_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(lean_object* v_ref_770_, lean_object* v_msgData_771_, lean_object* v_severity_772_, lean_object* v_isSilent_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
uint8_t v_severity_boxed_777_; uint8_t v_isSilent_boxed_778_; lean_object* v_res_779_; 
v_severity_boxed_777_ = lean_unbox(v_severity_772_);
v_isSilent_boxed_778_ = lean_unbox(v_isSilent_773_);
v_res_779_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_770_, v_msgData_771_, v_severity_boxed_777_, v_isSilent_boxed_778_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v_ref_770_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(lean_object* v_ref_780_, lean_object* v_msgData_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
uint8_t v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = 1;
v___x_786_ = 0;
v___x_787_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_780_, v_msgData_781_, v___x_785_, v___x_786_, v___y_782_, v___y_783_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(lean_object* v_ref_788_, lean_object* v_msgData_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v_ref_788_, v_msgData_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v_ref_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(lean_object* v_t_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; lean_object* v_infoState_798_; uint8_t v_enabled_799_; 
v___x_797_ = lean_st_ref_get(v___y_795_);
v_infoState_798_ = lean_ctor_get(v___x_797_, 8);
lean_inc_ref(v_infoState_798_);
lean_dec(v___x_797_);
v_enabled_799_ = lean_ctor_get_uint8(v_infoState_798_, sizeof(void*)*3);
lean_dec_ref(v_infoState_798_);
if (v_enabled_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v_t_794_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v_infoState_803_; lean_object* v_env_804_; lean_object* v_messages_805_; lean_object* v_scopes_806_; lean_object* v_usedQuotCtxts_807_; lean_object* v_nextMacroScope_808_; lean_object* v_maxRecDepth_809_; lean_object* v_ngen_810_; lean_object* v_auxDeclNGen_811_; lean_object* v_traceState_812_; lean_object* v_snapshotTasks_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_835_; 
v___x_802_ = lean_st_ref_take(v___y_795_);
v_infoState_803_ = lean_ctor_get(v___x_802_, 8);
v_env_804_ = lean_ctor_get(v___x_802_, 0);
v_messages_805_ = lean_ctor_get(v___x_802_, 1);
v_scopes_806_ = lean_ctor_get(v___x_802_, 2);
v_usedQuotCtxts_807_ = lean_ctor_get(v___x_802_, 3);
v_nextMacroScope_808_ = lean_ctor_get(v___x_802_, 4);
v_maxRecDepth_809_ = lean_ctor_get(v___x_802_, 5);
v_ngen_810_ = lean_ctor_get(v___x_802_, 6);
v_auxDeclNGen_811_ = lean_ctor_get(v___x_802_, 7);
v_traceState_812_ = lean_ctor_get(v___x_802_, 9);
v_snapshotTasks_813_ = lean_ctor_get(v___x_802_, 10);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_835_ == 0)
{
v___x_815_ = v___x_802_;
v_isShared_816_ = v_isSharedCheck_835_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_snapshotTasks_813_);
lean_inc(v_traceState_812_);
lean_inc(v_infoState_803_);
lean_inc(v_auxDeclNGen_811_);
lean_inc(v_ngen_810_);
lean_inc(v_maxRecDepth_809_);
lean_inc(v_nextMacroScope_808_);
lean_inc(v_usedQuotCtxts_807_);
lean_inc(v_scopes_806_);
lean_inc(v_messages_805_);
lean_inc(v_env_804_);
lean_dec(v___x_802_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_835_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v_enabled_817_; lean_object* v_assignment_818_; lean_object* v_lazyAssignment_819_; lean_object* v_trees_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_834_; 
v_enabled_817_ = lean_ctor_get_uint8(v_infoState_803_, sizeof(void*)*3);
v_assignment_818_ = lean_ctor_get(v_infoState_803_, 0);
v_lazyAssignment_819_ = lean_ctor_get(v_infoState_803_, 1);
v_trees_820_ = lean_ctor_get(v_infoState_803_, 2);
v_isSharedCheck_834_ = !lean_is_exclusive(v_infoState_803_);
if (v_isSharedCheck_834_ == 0)
{
v___x_822_ = v_infoState_803_;
v_isShared_823_ = v_isSharedCheck_834_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_trees_820_);
lean_inc(v_lazyAssignment_819_);
lean_inc(v_assignment_818_);
lean_dec(v_infoState_803_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_834_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = l_Lean_PersistentArray_push___redArg(v_trees_820_, v_t_794_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 2, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_assignment_818_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_lazyAssignment_819_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v___x_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_833_, sizeof(void*)*3, v_enabled_817_);
v___x_826_ = v_reuseFailAlloc_833_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 8, v___x_826_);
v___x_828_ = v___x_815_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_env_804_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_messages_805_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_scopes_806_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_usedQuotCtxts_807_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_nextMacroScope_808_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v_maxRecDepth_809_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_ngen_810_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_auxDeclNGen_811_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_832_, 9, v_traceState_812_);
lean_ctor_set(v_reuseFailAlloc_832_, 10, v_snapshotTasks_813_);
v___x_828_ = v_reuseFailAlloc_832_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_st_ref_set(v___y_795_, v___x_828_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_t_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_836_, v___y_837_);
lean_dec(v___y_837_);
return v_res_839_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_unsigned_to_nat(32u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_843_ = ((size_t)5ULL);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_unsigned_to_nat(32u);
v___x_846_ = lean_mk_empty_array_with_capacity(v___x_845_);
v___x_847_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0);
v___x_848_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
lean_ctor_set(v___x_848_, 2, v___x_844_);
lean_ctor_set(v___x_848_, 3, v___x_844_);
lean_ctor_set_usize(v___x_848_, 4, v___x_843_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(lean_object* v_t_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_infoState_854_; uint8_t v_enabled_855_; 
v___x_853_ = lean_st_ref_get(v___y_851_);
v_infoState_854_ = lean_ctor_get(v___x_853_, 8);
lean_inc_ref(v_infoState_854_);
lean_dec(v___x_853_);
v_enabled_855_ = lean_ctor_get_uint8(v_infoState_854_, sizeof(void*)*3);
lean_dec_ref(v_infoState_854_);
if (v_enabled_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_t_849_);
v___x_856_ = lean_box(0);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v_t_849_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v___x_859_, v___y_851_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(lean_object* v_t_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v_t_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(lean_object* v_info_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_870_, 0, v_info_866_);
v___x_871_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v___x_870_, v___y_867_, v___y_868_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(lean_object* v_info_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v_info_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_876_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_box(1);
v___x_878_ = l_Lean_MessageData_ofFormat(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2));
v___x_883_ = l_Lean_MessageData_ofFormat(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
if (lean_obj_tag(v_x_885_) == 0)
{
return v_x_884_;
}
else
{
lean_object* v_head_886_; lean_object* v_tail_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_909_; 
v_head_886_ = lean_ctor_get(v_x_885_, 0);
v_tail_887_ = lean_ctor_get(v_x_885_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_885_);
if (v_isSharedCheck_909_ == 0)
{
v___x_889_ = v_x_885_;
v_isShared_890_ = v_isSharedCheck_909_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_tail_887_);
lean_inc(v_head_886_);
lean_dec(v_x_885_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_909_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_before_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_907_; 
v_before_891_ = lean_ctor_get(v_head_886_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_head_886_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_head_886_, 1);
lean_dec(v_unused_908_);
v___x_893_ = v_head_886_;
v_isShared_894_ = v_isSharedCheck_907_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_before_891_);
lean_dec(v_head_886_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_907_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 7);
lean_ctor_set(v___x_893_, 1, v___x_895_);
lean_ctor_set(v___x_893_, 0, v_x_884_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_x_884_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_906_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 7);
lean_ctor_set(v___x_889_, 1, v___x_898_);
lean_ctor_set(v___x_889_, 0, v___x_897_);
v___x_900_ = v___x_889_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_898_);
v___x_900_ = v_reuseFailAlloc_905_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = l_Lean_MessageData_ofSyntax(v_before_891_);
v___x_902_ = l_Lean_indentD(v___x_901_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_900_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v_x_884_ = v___x_903_;
v_x_885_ = v_tail_887_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_914_ = l_Lean_MessageData_ofFormat(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_915_, lean_object* v_macroStack_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; lean_object* v_scopes_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_opts_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_919_ = lean_st_ref_get(v___y_917_);
v_scopes_920_ = lean_ctor_get(v___x_919_, 2);
lean_inc(v_scopes_920_);
lean_dec(v___x_919_);
v___x_921_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_922_ = l_List_head_x21___redArg(v___x_921_, v_scopes_920_);
lean_dec(v_scopes_920_);
v_opts_923_ = lean_ctor_get(v___x_922_, 1);
lean_inc_ref(v_opts_923_);
lean_dec(v___x_922_);
v___x_924_ = l_Lean_Elab_pp_macroStack;
v___x_925_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_923_, v___x_924_);
lean_dec_ref(v_opts_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec(v_macroStack_916_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_msgData_915_);
return v___x_926_;
}
else
{
if (lean_obj_tag(v_macroStack_916_) == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_msgData_915_);
return v___x_927_;
}
else
{
lean_object* v_head_928_; lean_object* v_after_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_944_; 
v_head_928_ = lean_ctor_get(v_macroStack_916_, 0);
lean_inc(v_head_928_);
v_after_929_ = lean_ctor_get(v_head_928_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_head_928_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_head_928_, 0);
lean_dec(v_unused_945_);
v___x_931_ = v_head_928_;
v_isShared_932_ = v_isSharedCheck_944_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_after_929_);
lean_dec(v_head_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_944_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 7);
lean_ctor_set(v___x_931_, 1, v___x_933_);
lean_ctor_set(v___x_931_, 0, v_msgData_915_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_msgData_915_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_943_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_msgData_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_936_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_MessageData_ofSyntax(v_after_929_);
v___x_939_ = l_Lean_indentD(v___x_938_);
v_msgData_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_940_, 0, v___x_937_);
lean_ctor_set(v_msgData_940_, 1, v___x_939_);
v___x_941_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(v_msgData_940_, v_macroStack_916_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_946_, lean_object* v_macroStack_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_946_, v_macroStack_947_, v___y_948_);
lean_dec(v___y_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Elab_Command_getRef___redArg(v___y_952_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_macroStack_957_; lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v___x_955_);
v_macroStack_957_ = lean_ctor_get(v___y_952_, 4);
v___x_958_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msg_951_, v___y_953_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
lean_inc_n(v_macroStack_957_, 2);
v___x_960_ = l_Lean_Elab_getBetterRef(v_a_956_, v_macroStack_957_);
lean_dec(v_a_956_);
v___x_961_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_a_959_, v_macroStack_957_, v___y_953_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_970_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_960_);
lean_ctor_set(v___x_966_, 1, v_a_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v_msg_951_);
v_a_971_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_955_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_955_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(lean_object* v_ref_984_, lean_object* v_msg_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Elab_Command_getRef___redArg(v___y_986_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v_fileName_991_; lean_object* v_fileMap_992_; lean_object* v_currRecDepth_993_; lean_object* v_cmdPos_994_; lean_object* v_macroStack_995_; lean_object* v_quotContext_x3f_996_; lean_object* v_currMacroScope_997_; lean_object* v_snap_x3f_998_; lean_object* v_cancelTk_x3f_999_; uint8_t v_suppressElabErrors_1000_; lean_object* v_ref_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v___x_989_);
v_fileName_991_ = lean_ctor_get(v___y_986_, 0);
v_fileMap_992_ = lean_ctor_get(v___y_986_, 1);
v_currRecDepth_993_ = lean_ctor_get(v___y_986_, 2);
v_cmdPos_994_ = lean_ctor_get(v___y_986_, 3);
v_macroStack_995_ = lean_ctor_get(v___y_986_, 4);
v_quotContext_x3f_996_ = lean_ctor_get(v___y_986_, 5);
v_currMacroScope_997_ = lean_ctor_get(v___y_986_, 6);
v_snap_x3f_998_ = lean_ctor_get(v___y_986_, 8);
v_cancelTk_x3f_999_ = lean_ctor_get(v___y_986_, 9);
v_suppressElabErrors_1000_ = lean_ctor_get_uint8(v___y_986_, sizeof(void*)*10);
v_ref_1001_ = l_Lean_replaceRef(v_ref_984_, v_a_990_);
lean_dec(v_a_990_);
lean_inc(v_cancelTk_x3f_999_);
lean_inc(v_snap_x3f_998_);
lean_inc(v_currMacroScope_997_);
lean_inc(v_quotContext_x3f_996_);
lean_inc(v_macroStack_995_);
lean_inc(v_cmdPos_994_);
lean_inc(v_currRecDepth_993_);
lean_inc_ref(v_fileMap_992_);
lean_inc_ref(v_fileName_991_);
v___x_1002_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1002_, 0, v_fileName_991_);
lean_ctor_set(v___x_1002_, 1, v_fileMap_992_);
lean_ctor_set(v___x_1002_, 2, v_currRecDepth_993_);
lean_ctor_set(v___x_1002_, 3, v_cmdPos_994_);
lean_ctor_set(v___x_1002_, 4, v_macroStack_995_);
lean_ctor_set(v___x_1002_, 5, v_quotContext_x3f_996_);
lean_ctor_set(v___x_1002_, 6, v_currMacroScope_997_);
lean_ctor_set(v___x_1002_, 7, v_ref_1001_);
lean_ctor_set(v___x_1002_, 8, v_snap_x3f_998_);
lean_ctor_set(v___x_1002_, 9, v_cancelTk_x3f_999_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*10, v_suppressElabErrors_1000_);
v___x_1003_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_985_, v___x_1002_, v___y_987_);
lean_dec_ref(v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_msg_985_);
v_a_1004_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_989_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_989_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(lean_object* v_ref_1012_, lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1012_, v_msg_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v_ref_1012_);
return v_res_1017_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1021_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2);
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_box(1);
v___x_1025_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_1026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3);
v___x_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
lean_ctor_set(v___x_1027_, 2, v___x_1024_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(lean_object* v_tyName_1049_, lean_object* v_infos_1050_, lean_object* v_as_1051_, size_t v_sz_1052_, size_t v_i_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_a_1059_; uint8_t v___x_1063_; 
v___x_1063_ = lean_usize_dec_lt(v_i_1053_, v_sz_1052_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec(v_tyName_1049_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_b_1054_);
return v___x_1064_;
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_a_1065_ = lean_array_uget_borrowed(v_as_1051_, v_i_1053_);
v___x_1066_ = ((lean_object*)(l_Lake_DSL_declField___closed__1));
lean_inc(v_a_1065_);
v___x_1067_ = l_Lean_Syntax_isOfKind(v_a_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1);
v___x_1069_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_a_1065_, v___x_1068_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_dec_ref(v___x_1069_);
v_a_1059_ = v_b_1054_;
goto v___jp_1058_;
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_b_1054_);
lean_dec(v_tyName_1049_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = l_Lean_Syntax_getArg(v_a_1065_, v___x_1078_);
v___x_1080_ = l_Lean_TSyntax_getId(v___x_1079_);
lean_inc(v___x_1080_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
v___x_1082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4);
lean_inc(v_tyName_1049_);
lean_inc(v_a_1065_);
v___x_1083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1083_, 0, v_a_1065_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set(v___x_1083_, 2, v___x_1082_);
lean_ctor_set(v___x_1083_, 3, v_tyName_1049_);
v___x_1084_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v___x_1083_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1085_; 
lean_dec_ref(v___x_1084_);
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_infos_1050_, v___x_1080_);
if (lean_obj_tag(v___x_1085_) == 1)
{
lean_object* v_val_1086_; lean_object* v_realName_1087_; uint8_t v_canonical_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_val_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1086_);
lean_dec_ref(v___x_1085_);
v_realName_1087_ = lean_ctor_get(v_val_1086_, 1);
lean_inc(v_realName_1087_);
v_canonical_1088_ = lean_ctor_get_uint8(v_val_1086_, sizeof(void*)*2);
lean_dec(v_val_1086_);
v___x_1089_ = lean_unsigned_to_nat(2u);
v___x_1090_ = l_Lean_Syntax_getArg(v_a_1065_, v___x_1089_);
if (v_canonical_1088_ == 0)
{
if (v___x_1067_ == 0)
{
lean_dec(v___x_1080_);
goto v___jp_1091_;
}
else
{
uint8_t v___x_1094_; 
v___x_1094_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_realName_1087_, v_b_1054_);
if (v___x_1094_ == 0)
{
lean_dec(v___x_1080_);
goto v___jp_1091_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1095_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6);
lean_inc(v_realName_1087_);
v___x_1096_ = l_Lean_MessageData_ofName(v_realName_1087_);
lean_inc_ref(v___x_1096_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_MessageData_ofName(v___x_1080_);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1096_);
v___x_1105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1079_, v___x_1106_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref(v___x_1107_);
goto v___jp_1091_;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v___x_1090_);
lean_dec(v_realName_1087_);
lean_dec(v___x_1079_);
lean_dec(v_b_1054_);
lean_dec(v_tyName_1049_);
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1080_);
goto v___jp_1091_;
}
v___jp_1091_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1079_);
lean_ctor_set(v___x_1092_, 1, v___x_1090_);
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_realName_1087_, v___x_1092_, v_b_1054_);
v_a_1059_ = v___x_1093_;
goto v___jp_1058_;
}
}
else
{
lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v___x_1085_);
v___x_1116_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14);
v___x_1117_ = 0;
lean_inc(v_tyName_1049_);
v___x_1118_ = l_Lean_MessageData_ofConstName(v_tyName_1049_, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1116_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_MessageData_ofName(v___x_1080_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__18);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1079_, v___x_1125_, v___y_1055_, v___y_1056_);
lean_dec(v___x_1079_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_dec_ref(v___x_1126_);
v_a_1059_ = v_b_1054_;
goto v___jp_1058_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_b_1054_);
lean_dec(v_tyName_1049_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v___x_1080_);
lean_dec(v___x_1079_);
lean_dec(v_b_1054_);
lean_dec(v_tyName_1049_);
v_a_1135_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1084_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1084_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
v___jp_1058_:
{
size_t v___x_1060_; size_t v___x_1061_; 
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_add(v_i_1053_, v___x_1060_);
v_i_1053_ = v___x_1061_;
v_b_1054_ = v_a_1059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(lean_object* v_tyName_1143_, lean_object* v_infos_1144_, lean_object* v_as_1145_, lean_object* v_sz_1146_, lean_object* v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
size_t v_sz_boxed_1152_; size_t v_i_boxed_1153_; lean_object* v_res_1154_; 
v_sz_boxed_1152_ = lean_unbox_usize(v_sz_1146_);
lean_dec(v_sz_1146_);
v_i_boxed_1153_ = lean_unbox_usize(v_i_1147_);
lean_dec(v_i_1147_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1143_, v_infos_1144_, v_as_1145_, v_sz_boxed_1152_, v_i_boxed_1153_, v_b_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_as_1145_);
lean_dec(v_infos_1144_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object* v_tyName_1166_, lean_object* v_infos_1167_, lean_object* v_fs_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_m_1172_; size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v_m_1172_ = lean_box(1);
v_sz_1173_ = lean_array_size(v_fs_1168_);
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1166_, v_infos_1167_, v_fs_1168_, v_sz_1173_, v___x_1174_, v_m_1172_, v_a_1169_, v_a_1170_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1194_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v___x_1177_, v_a_1176_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1194_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1194_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1183_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
v___x_1184_ = lean_box(2);
v___x_1185_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2));
v___x_1186_ = l_Lean_Syntax_mkSep(v_a_1179_, v___x_1185_);
lean_dec(v_a_1179_);
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_mk_empty_array_with_capacity(v___x_1187_);
v___x_1189_ = lean_array_push(v___x_1188_, v___x_1186_);
v___x_1190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1184_);
lean_ctor_set(v___x_1190_, 1, v___x_1183_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1190_);
v___x_1192_ = v___x_1181_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1175_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1175_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(lean_object* v_tyName_1203_, lean_object* v_infos_1204_, lean_object* v_fs_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1203_, v_infos_1204_, v_fs_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec_ref(v_fs_1205_);
lean_dec(v_infos_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_object* v_00_u03b1_1210_, lean_object* v_ref_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1211_, v_msg_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_ref_1218_, lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(v_00_u03b1_1217_, v_ref_1218_, v_msg_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v_ref_1218_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(lean_object* v_init_1224_, lean_object* v_x_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_1224_, v_x_1225_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(lean_object* v_init_1230_, lean_object* v_x_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(v_init_1230_, v_x_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(lean_object* v_msgData_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_1236_, v___y_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(v_msgData_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_object* v_00_u03b1_1246_, lean_object* v_msg_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_msg_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(v_00_u03b1_1252_, v_msg_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(lean_object* v_t_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_1258_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(lean_object* v_t_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(v_t_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(lean_object* v_msgData_1268_, lean_object* v_macroStack_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_1268_, v_macroStack_1269_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1274_, lean_object* v_macroStack_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(v_msgData_1274_, v_macroStack_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v_env_1283_; lean_object* v___x_1284_; lean_object* v_mainModule_1285_; lean_object* v___x_1286_; 
v___x_1282_ = lean_st_ref_get(v___y_1280_);
v_env_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_env_1283_);
lean_dec(v___x_1282_);
v___x_1284_ = l_Lean_Environment_header(v_env_1283_);
lean_dec_ref(v_env_1283_);
v_mainModule_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_mainModule_1285_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_mainModule_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1287_);
lean_dec(v___y_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object* v___x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_a_1295_; lean_object* v_quotContext_x3f_1314_; 
v_quotContext_x3f_1314_ = lean_ctor_get(v___y_1291_, 5);
if (lean_obj_tag(v_quotContext_x3f_1314_) == 0)
{
lean_object* v___x_1315_; lean_object* v_a_1316_; 
v___x_1315_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1292_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1315_);
v_a_1295_ = v_a_1316_;
goto v___jp_1294_;
}
else
{
lean_object* v_val_1317_; 
v_val_1317_ = lean_ctor_get(v_quotContext_x3f_1314_, 0);
lean_inc(v_val_1317_);
v_a_1295_ = v_val_1317_;
goto v___jp_1294_;
}
v___jp_1294_:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1291_);
lean_dec_ref(v___y_1291_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1305_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = l_Lean_addMacroScope(v_a_1295_, v___x_1290_, v_a_1297_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1295_);
lean_dec(v___x_1290_);
v_a_1306_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1296_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1296_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object* v___x_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(v___x_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___f_1331_; lean_object* v___x_1332_; 
v___f_1331_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2));
v___x_1332_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___f_1331_, v___y_1328_, v___y_1329_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(lean_object* v_ref_1337_, uint8_t v_canonical_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = l_Lean_mkIdentFrom(v_ref_1337_, v_a_1343_, v_canonical_1338_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1342_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1342_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object* v_ref_1360_, lean_object* v_canonical_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v_canonical_boxed_1365_; lean_object* v_res_1366_; 
v_canonical_boxed_1365_ = lean_unbox(v_canonical_1361_);
v_res_1366_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_ref_1360_, v_canonical_boxed_1365_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v_ref_1360_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object* v_stx_x3f_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
if (lean_obj_tag(v_stx_x3f_1367_) == 0)
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Elab_Command_getRef___redArg(v_a_1368_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = 0;
v___x_1374_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_a_1372_, v___x_1373_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1372_);
return v___x_1374_;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1371_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1371_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v_val_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
v_val_1383_ = lean_ctor_get(v_stx_x3f_1367_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_stx_x3f_1367_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v_stx_x3f_1367_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_val_1383_);
lean_dec(v_stx_x3f_1367_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = l_Lake_DSL_expandIdentOrStrAsIdent(v_val_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object* v_stx_x3f_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lake_DSL_mkConfigDeclIdent(v_stx_x3f_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1404_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__6(void){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_instMonadEIO(lean_box(0));
return v___x_1411_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__7(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__6, &l_Lake_DSL_elabConfig___closed__6_once, _init_l_Lake_DSL_elabConfig___closed__6);
v___x_1413_ = l_StateRefT_x27_instMonad___redArg(v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__13(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1423_ = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
v___x_1424_ = l_Lean_Elab_Command_instMonadRefCommandElabM;
v___x_1425_ = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
v___x_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v___x_1424_);
lean_ctor_set(v___x_1426_, 2, v___x_1423_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__15(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__14));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object* v_tyName_1430_, lean_object* v_info_1431_, lean_object* v_id_1432_, lean_object* v_ty_1433_, lean_object* v_config_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v_whereInfo_1550_; lean_object* v_fs_1551_; lean_object* v_wds_x3f_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___x_1581_; lean_object* v_toApplicative_1582_; lean_object* v_toFunctor_1583_; lean_object* v_toSeq_1584_; lean_object* v_toSeqLeft_1585_; lean_object* v_toSeqRight_1586_; lean_object* v___f_1587_; lean_object* v___f_1588_; lean_object* v___f_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; lean_object* v___f_1592_; lean_object* v___f_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1581_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1582_ = lean_ctor_get(v___x_1581_, 0);
v_toFunctor_1583_ = lean_ctor_get(v_toApplicative_1582_, 0);
v_toSeq_1584_ = lean_ctor_get(v_toApplicative_1582_, 2);
v_toSeqLeft_1585_ = lean_ctor_get(v_toApplicative_1582_, 3);
v_toSeqRight_1586_ = lean_ctor_get(v_toApplicative_1582_, 4);
v___f_1587_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1588_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1583_, 2);
v___f_1589_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1589_, 0, v_toFunctor_1583_);
v___f_1590_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1590_, 0, v_toFunctor_1583_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___f_1589_);
lean_ctor_set(v___x_1591_, 1, v___f_1590_);
lean_inc(v_toSeqRight_1586_);
v___f_1592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1592_, 0, v_toSeqRight_1586_);
lean_inc(v_toSeqLeft_1585_);
v___f_1593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1593_, 0, v_toSeqLeft_1585_);
lean_inc(v_toSeq_1584_);
v___f_1594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1594_, 0, v_toSeq_1584_);
v___x_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1591_);
lean_ctor_set(v___x_1595_, 1, v___f_1587_);
lean_ctor_set(v___x_1595_, 2, v___f_1594_);
lean_ctor_set(v___x_1595_, 3, v___f_1593_);
lean_ctor_set(v___x_1595_, 4, v___f_1592_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v___f_1588_);
v___x_1597_ = ((lean_object*)(l_Lake_DSL_optConfig___closed__1));
lean_inc(v_config_1434_);
v___x_1598_ = l_Lean_Syntax_isOfKind(v_config_1434_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_4248__overap_1601_; lean_object* v___x_1602_; 
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1599_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1600_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_4248__overap_1601_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1599_, v_config_1434_, v___x_1600_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1602_ = lean_apply_3(v___x_4248__overap_1601_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = l_Lean_Syntax_getArg(v_config_1434_, v___x_1603_);
lean_inc(v___x_1604_);
v___x_1605_ = l_Lean_Syntax_matchesNull(v___x_1604_, v___x_1603_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1604_);
v___x_1607_ = l_Lean_Syntax_matchesNull(v___x_1604_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_4663__overap_1610_; lean_object* v___x_1611_; 
lean_dec(v___x_1604_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1608_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1609_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_4663__overap_1610_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1608_, v_config_1434_, v___x_1609_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1611_ = lean_apply_3(v___x_4663__overap_1610_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = l_Lean_Syntax_getArg(v___x_1604_, v___x_1603_);
lean_dec(v___x_1604_);
v___x_1613_ = ((lean_object*)(l_Lake_DSL_declValWhere___closed__1));
lean_inc(v___x_1612_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lake_DSL_declValStruct___closed__1));
lean_inc(v___x_1612_);
v___x_1616_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_4961__overap_1619_; lean_object* v___x_1620_; 
lean_dec(v___x_1612_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1617_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1618_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_4961__overap_1619_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1617_, v_config_1434_, v___x_1618_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1620_ = lean_apply_3(v___x_4961__overap_1619_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1621_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1603_);
v___x_1622_ = ((lean_object*)(l_Lake_DSL_structVal___closed__1));
lean_inc(v___x_1621_);
v___x_1623_ = l_Lean_Syntax_isOfKind(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_5059__overap_1626_; lean_object* v___x_1627_; 
lean_dec(v___x_1621_);
lean_dec(v___x_1612_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1624_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1625_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_5059__overap_1626_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1624_, v_config_1434_, v___x_1625_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1627_ = lean_apply_3(v___x_5059__overap_1626_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1628_ = l_Lean_Syntax_getArg(v___x_1621_, v___x_1606_);
v___x_1629_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1628_);
v___x_1630_ = l_Lean_Syntax_isOfKind(v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_5144__overap_1633_; lean_object* v___x_1634_; 
lean_dec(v___x_1628_);
lean_dec(v___x_1621_);
lean_dec(v___x_1612_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1631_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1632_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_5144__overap_1633_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1631_, v_config_1434_, v___x_1632_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1634_ = lean_apply_3(v___x_5144__overap_1633_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1634_;
}
else
{
lean_object* v_tk_1635_; lean_object* v___x_1636_; lean_object* v_wds_x3f_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v_tk_1635_ = l_Lean_Syntax_getArg(v___x_1621_, v___x_1603_);
lean_dec(v___x_1621_);
v___x_1636_ = l_Lean_Syntax_getArg(v___x_1628_, v___x_1603_);
lean_dec(v___x_1628_);
v___x_1644_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1606_);
lean_dec(v___x_1612_);
v___x_1645_ = l_Lean_Syntax_isNone(v___x_1644_);
if (v___x_1645_ == 0)
{
uint8_t v___x_1646_; 
lean_inc(v___x_1644_);
v___x_1646_ = l_Lean_Syntax_matchesNull(v___x_1644_, v___x_1606_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_5253__overap_1649_; lean_object* v___x_1650_; 
lean_dec(v___x_1644_);
lean_dec(v___x_1636_);
lean_dec(v_tk_1635_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1647_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1648_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_5253__overap_1649_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1647_, v_config_1434_, v___x_1648_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1650_ = lean_apply_3(v___x_5253__overap_1649_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1650_;
}
else
{
lean_object* v_wds_x3f_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_wds_x3f_1651_ = l_Lean_Syntax_getArg(v___x_1644_, v___x_1603_);
lean_dec(v___x_1644_);
v___x_1652_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1651_);
v___x_1653_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_5290__overap_1656_; lean_object* v___x_1657_; 
lean_dec(v_wds_x3f_1651_);
lean_dec(v___x_1636_);
lean_dec(v_tk_1635_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1654_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1655_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_5290__overap_1656_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1654_, v_config_1434_, v___x_1655_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1657_ = lean_apply_3(v___x_5290__overap_1656_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; 
lean_dec_ref(v___x_1596_);
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_wds_x3f_1651_);
v_wds_x3f_1638_ = v___x_1658_;
v___y_1639_ = v_a_1435_;
v___y_1640_ = v_a_1436_;
goto v___jp_1637_;
}
}
}
else
{
lean_object* v___x_1659_; 
lean_dec(v___x_1644_);
lean_dec_ref(v___x_1596_);
v___x_1659_ = lean_box(0);
v_wds_x3f_1638_ = v___x_1659_;
v___y_1639_ = v_a_1435_;
v___y_1640_ = v_a_1436_;
goto v___jp_1637_;
}
v___jp_1637_:
{
lean_object* v_fs_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_fs_1641_ = l_Lean_Syntax_getArgs(v___x_1636_);
lean_dec(v___x_1636_);
v___x_1642_ = l_Lean_Syntax_getHeadInfo(v_tk_1635_);
lean_dec(v_tk_1635_);
v___x_1643_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1641_);
lean_dec_ref(v_fs_1641_);
v_whereInfo_1550_ = v___x_1642_;
v_fs_1551_ = v___x_1643_;
v_wds_x3f_1552_ = v_wds_x3f_1638_;
v___y_1553_ = v___y_1639_;
v___y_1554_ = v___y_1640_;
goto v___jp_1549_;
}
}
}
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1660_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1606_);
v___x_1661_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1660_);
v___x_1662_ = l_Lean_Syntax_isOfKind(v___x_1660_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_5386__overap_1665_; lean_object* v___x_1666_; 
lean_dec(v___x_1660_);
lean_dec(v___x_1612_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1663_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1664_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_5386__overap_1665_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1663_, v_config_1434_, v___x_1664_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1666_ = lean_apply_3(v___x_5386__overap_1665_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1666_;
}
else
{
lean_object* v_tk_1667_; lean_object* v___x_1668_; lean_object* v_wds_x3f_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_tk_1667_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1603_);
v___x_1668_ = l_Lean_Syntax_getArg(v___x_1660_, v___x_1603_);
lean_dec(v___x_1660_);
v___x_1676_ = lean_unsigned_to_nat(2u);
v___x_1677_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1676_);
lean_dec(v___x_1612_);
v___x_1678_ = l_Lean_Syntax_isNone(v___x_1677_);
if (v___x_1678_ == 0)
{
uint8_t v___x_1679_; 
lean_inc(v___x_1677_);
v___x_1679_ = l_Lean_Syntax_matchesNull(v___x_1677_, v___x_1606_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_5496__overap_1682_; lean_object* v___x_1683_; 
lean_dec(v___x_1677_);
lean_dec(v___x_1668_);
lean_dec(v_tk_1667_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1680_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1681_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_5496__overap_1682_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1680_, v_config_1434_, v___x_1681_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1683_ = lean_apply_3(v___x_5496__overap_1682_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1683_;
}
else
{
lean_object* v_wds_x3f_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_wds_x3f_1684_ = l_Lean_Syntax_getArg(v___x_1677_, v___x_1603_);
lean_dec(v___x_1677_);
v___x_1685_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1684_);
v___x_1686_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1684_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_5533__overap_1689_; lean_object* v___x_1690_; 
lean_dec(v_wds_x3f_1684_);
lean_dec(v___x_1668_);
lean_dec(v_tk_1667_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
lean_dec(v_tyName_1430_);
v___x_1687_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1688_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_5533__overap_1689_ = l_Lean_throwErrorAt___redArg(v___x_1596_, v___x_1687_, v_config_1434_, v___x_1688_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
v___x_1690_ = lean_apply_3(v___x_5533__overap_1689_, v_a_1435_, v_a_1436_, lean_box(0));
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; 
lean_dec_ref(v___x_1596_);
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_wds_x3f_1684_);
v_wds_x3f_1670_ = v___x_1691_;
v___y_1671_ = v_a_1435_;
v___y_1672_ = v_a_1436_;
goto v___jp_1669_;
}
}
}
else
{
lean_object* v___x_1692_; 
lean_dec(v___x_1677_);
lean_dec_ref(v___x_1596_);
v___x_1692_ = lean_box(0);
v_wds_x3f_1670_ = v___x_1692_;
v___y_1671_ = v_a_1435_;
v___y_1672_ = v_a_1436_;
goto v___jp_1669_;
}
v___jp_1669_:
{
lean_object* v_fs_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_fs_1673_ = l_Lean_Syntax_getArgs(v___x_1668_);
lean_dec(v___x_1668_);
v___x_1674_ = l_Lean_Syntax_getHeadInfo(v_tk_1667_);
lean_dec(v_tk_1667_);
v___x_1675_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1673_);
lean_dec_ref(v_fs_1673_);
v_whereInfo_1550_ = v___x_1674_;
v_fs_1551_ = v___x_1675_;
v_wds_x3f_1552_ = v_wds_x3f_1670_;
v___y_1553_ = v___y_1671_;
v___y_1554_ = v___y_1672_;
goto v___jp_1549_;
}
}
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v___x_1604_);
lean_dec_ref(v___x_1596_);
v___x_1693_ = lean_box(2);
v___x_1694_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1695_ = lean_box(0);
v_whereInfo_1550_ = v___x_1693_;
v_fs_1551_ = v___x_1694_;
v_wds_x3f_1552_ = v___x_1695_;
v___y_1553_ = v_a_1435_;
v___y_1554_ = v_a_1436_;
goto v___jp_1549_;
}
}
v___jp_1438_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1447_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__0));
lean_inc_ref_n(v___y_1441_, 5);
lean_inc_ref_n(v___y_1443_, 6);
lean_inc_ref_n(v___y_1442_, 6);
v___x_1448_ = l_Lean_Name_mkStr4(v___y_1442_, v___y_1443_, v___y_1441_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__1));
v___x_1450_ = l_Lean_Name_mkStr4(v___y_1442_, v___y_1443_, v___y_1441_, v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
v___x_1452_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
lean_inc_n(v___y_1444_, 8);
v___x_1453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1444_);
lean_ctor_set(v___x_1453_, 1, v___x_1451_);
lean_ctor_set(v___x_1453_, 2, v___x_1452_);
lean_inc_ref_n(v___x_1453_, 8);
v___x_1454_ = l_Lean_Syntax_node7(v___y_1444_, v___x_1450_, v___x_1453_, v___x_1453_, v___x_1453_, v___x_1453_, v___x_1453_, v___x_1453_, v___x_1453_);
v___x_1455_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__2));
v___x_1456_ = l_Lean_Name_mkStr4(v___y_1442_, v___y_1443_, v___y_1441_, v___x_1455_);
v___x_1457_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__3));
v___x_1458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___y_1444_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__4));
v___x_1460_ = l_Lean_Name_mkStr4(v___y_1442_, v___y_1443_, v___y_1441_, v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
lean_inc_n(v___y_1446_, 2);
v___x_1462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1462_, 0, v___y_1446_);
lean_ctor_set(v___x_1462_, 1, v___x_1451_);
lean_ctor_set(v___x_1462_, 2, v___x_1461_);
v___x_1463_ = lean_unsigned_to_nat(2u);
v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1463_);
v___x_1465_ = lean_array_push(v___x_1464_, v_id_1432_);
v___x_1466_ = lean_array_push(v___x_1465_, v___x_1462_);
v___x_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1446_);
lean_ctor_set(v___x_1467_, 1, v___x_1460_);
lean_ctor_set(v___x_1467_, 2, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__5));
v___x_1469_ = l_Lean_Name_mkStr4(v___y_1442_, v___y_1443_, v___y_1441_, v___x_1468_);
v___x_1470_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__2));
v___x_1471_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__2));
v___x_1472_ = l_Lean_Name_mkStr4(v___y_1442_, v___y_1443_, v___x_1470_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__26));
v___x_1474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___y_1444_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_Syntax_node2(v___y_1444_, v___x_1472_, v___x_1474_, v_ty_1433_);
v___x_1476_ = l_Lean_Syntax_node1(v___y_1444_, v___x_1451_, v___x_1475_);
v___x_1477_ = l_Lean_Syntax_node2(v___y_1444_, v___x_1469_, v___x_1453_, v___x_1476_);
v___x_1478_ = l_Lean_Syntax_node5(v___y_1444_, v___x_1456_, v___x_1458_, v___x_1467_, v___x_1477_, v___y_1445_, v___x_1453_);
v___x_1479_ = l_Lean_Syntax_node2(v___y_1444_, v___x_1448_, v___x_1454_, v___x_1478_);
lean_inc(v___x_1479_);
v___x_1480_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_1480_, 0, v___x_1479_);
v___x_1481_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_1434_, v___x_1479_, v___x_1480_, v___y_1439_, v___y_1440_);
return v___x_1481_;
}
v___jp_1482_:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Elab_Command_getRef___redArg(v___y_1483_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1483_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; lean_object* v_toApplicative_1496_; lean_object* v_toFunctor_1497_; lean_object* v_toSeq_1498_; lean_object* v_toSeqLeft_1499_; lean_object* v_toSeqRight_1500_; lean_object* v___f_1501_; lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___f_1507_; lean_object* v___f_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_quotContext_x3f_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v___x_1494_);
v___x_1495_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1496_ = lean_ctor_get(v___x_1495_, 0);
v_toFunctor_1497_ = lean_ctor_get(v_toApplicative_1496_, 0);
v_toSeq_1498_ = lean_ctor_get(v_toApplicative_1496_, 2);
v_toSeqLeft_1499_ = lean_ctor_get(v_toApplicative_1496_, 3);
v_toSeqRight_1500_ = lean_ctor_get(v_toApplicative_1496_, 4);
v___f_1501_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1502_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1497_, 2);
v___f_1503_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1503_, 0, v_toFunctor_1497_);
v___f_1504_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1504_, 0, v_toFunctor_1497_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___f_1503_);
lean_ctor_set(v___x_1505_, 1, v___f_1504_);
lean_inc(v_toSeqRight_1500_);
v___f_1506_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1506_, 0, v_toSeqRight_1500_);
lean_inc(v_toSeqLeft_1499_);
v___f_1507_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1507_, 0, v_toSeqLeft_1499_);
lean_inc(v_toSeq_1498_);
v___f_1508_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1508_, 0, v_toSeq_1498_);
v___x_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1505_);
lean_ctor_set(v___x_1509_, 1, v___f_1501_);
lean_ctor_set(v___x_1509_, 2, v___f_1508_);
lean_ctor_set(v___x_1509_, 3, v___f_1507_);
lean_ctor_set(v___x_1509_, 4, v___f_1506_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___f_1502_);
v___x_1511_ = l_Lean_Elab_Command_instMonadEnvCommandElabM;
v_quotContext_x3f_1512_ = lean_ctor_get(v___y_1483_, 5);
v___x_1513_ = l_Lean_mkOptionalNode(v___y_1491_);
v___x_1514_ = lean_unsigned_to_nat(3u);
v___x_1515_ = lean_mk_empty_array_with_capacity(v___x_1514_);
v___x_1516_ = lean_array_push(v___x_1515_, v___y_1489_);
v___x_1517_ = lean_array_push(v___x_1516_, v___y_1490_);
v___x_1518_ = lean_array_push(v___x_1517_, v___x_1513_);
v___x_1519_ = lean_box(2);
lean_inc(v___y_1487_);
v___x_1520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v___y_1487_);
lean_ctor_set(v___x_1520_, 2, v___x_1518_);
v___x_1521_ = 0;
v___x_1522_ = l_Lean_SourceInfo_fromRef(v_a_1493_, v___x_1521_);
lean_dec(v_a_1493_);
if (lean_obj_tag(v_quotContext_x3f_1512_) == 0)
{
lean_object* v___x_4232__overap_1523_; lean_object* v___x_1524_; 
v___x_4232__overap_1523_ = l_Lean_getMainModule___redArg(v___x_1510_, v___x_1511_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
v___x_1524_ = lean_apply_3(v___x_4232__overap_1523_, v___y_1483_, v___y_1484_, lean_box(0));
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_dec_ref(v___x_1524_);
v___y_1439_ = v___y_1483_;
v___y_1440_ = v___y_1484_;
v___y_1441_ = v___y_1485_;
v___y_1442_ = v___y_1486_;
v___y_1443_ = v___y_1488_;
v___y_1444_ = v___x_1522_;
v___y_1445_ = v___x_1520_;
v___y_1446_ = v___x_1519_;
goto v___jp_1438_;
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v___x_1522_);
lean_dec_ref(v___x_1520_);
lean_dec(v_config_1434_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_dec_ref(v___x_1510_);
v___y_1439_ = v___y_1483_;
v___y_1440_ = v___y_1484_;
v___y_1441_ = v___y_1485_;
v___y_1442_ = v___y_1486_;
v___y_1443_ = v___y_1488_;
v___y_1444_ = v___x_1522_;
v___y_1445_ = v___x_1520_;
v___y_1446_ = v___x_1519_;
goto v___jp_1438_;
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_a_1493_);
lean_dec(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v_config_1434_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
v_a_1533_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1494_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1494_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v_config_1434_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
v_a_1541_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1492_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1492_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
v___jp_1549_:
{
lean_object* v_fieldMap_1555_; lean_object* v___x_1556_; 
v_fieldMap_1555_ = lean_ctor_get(v_info_1431_, 1);
v___x_1556_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1430_, v_fieldMap_1555_, v_fs_1551_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_fs_1551_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; lean_object* v_whereTk_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__10));
v_whereTk_1559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_1559_, 0, v_whereInfo_1550_);
lean_ctor_set(v_whereTk_1559_, 1, v___x_1558_);
v___x_1560_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__0));
v___x_1561_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__1));
v___x_1562_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__6));
v___x_1563_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__12));
if (lean_obj_tag(v_wds_x3f_1552_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_box(0);
v___y_1483_ = v___y_1553_;
v___y_1484_ = v___y_1554_;
v___y_1485_ = v___x_1562_;
v___y_1486_ = v___x_1560_;
v___y_1487_ = v___x_1563_;
v___y_1488_ = v___x_1561_;
v___y_1489_ = v_whereTk_1559_;
v___y_1490_ = v_a_1557_;
v___y_1491_ = v___x_1564_;
goto v___jp_1482_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_val_1565_ = lean_ctor_get(v_wds_x3f_1552_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_wds_x3f_1552_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v_wds_x3f_1552_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_val_1565_);
lean_dec(v_wds_x3f_1552_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_val_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
v___y_1483_ = v___y_1553_;
v___y_1484_ = v___y_1554_;
v___y_1485_ = v___x_1562_;
v___y_1486_ = v___x_1560_;
v___y_1487_ = v___x_1563_;
v___y_1488_ = v___x_1561_;
v___y_1489_ = v_whereTk_1559_;
v___y_1490_ = v_a_1557_;
v___y_1491_ = v___x_1570_;
goto v___jp_1482_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_wds_x3f_1552_);
lean_dec(v_whereInfo_1550_);
lean_dec(v_config_1434_);
lean_dec(v_ty_1433_);
lean_dec(v_id_1432_);
v_a_1573_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1556_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1556_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object* v_tyName_1696_, lean_object* v_info_1697_, lean_object* v_id_1698_, lean_object* v_ty_1699_, lean_object* v_config_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lake_DSL_elabConfig(v_tyName_1696_, v_info_1697_, v_id_1698_, v_ty_1699_, v_config_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec_ref(v_info_1697_);
return v_res_1704_;
}
}
lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_DeclUtil(builtin);
}
#ifdef __cplusplus
}
#endif
