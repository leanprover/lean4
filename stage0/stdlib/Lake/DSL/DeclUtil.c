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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM;
lean_object* l_Lean_getMainModule___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "redefined field '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "' ('"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "' is an alias of '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "')"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unknown '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "' field '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17;
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
lean_dec_ref_known(v_attrs_x3f_16_, 1);
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
v___x_425_ = l_Lean_SourceInfo_fromRef(v_ref_424_, v___x_423_);
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
v___x_481_ = l_Lean_SourceInfo_fromRef(v_ref_480_, v___x_479_);
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
lean_dec_ref_known(v_ty_x3f_461_, 1);
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
v___x_513_ = l_Array_mkArray0___redArg();
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
lean_dec_ref_known(v_x_529_, 5);
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
lean_dec_ref_known(v___x_564_, 1);
if (lean_obj_tag(v_val_566_) == 1)
{
uint8_t v_v_567_; 
v_v_567_ = lean_ctor_get_uint8(v_val_566_, 0);
lean_dec_ref_known(v_val_566_, 0);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t v_suppressElabErrors_574_, uint8_t v___y_575_, lean_object* v_x_576_){
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
return v___x_580_;
}
else
{
return v_suppressElabErrors_574_;
}
}
else
{
return v___y_575_;
}
}
else
{
return v___y_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_581_, lean_object* v___y_582_, lean_object* v_x_583_){
_start:
{
uint8_t v_suppressElabErrors_boxed_584_; uint8_t v___y_9000__boxed_585_; uint8_t v_res_586_; lean_object* v_r_587_; 
v_suppressElabErrors_boxed_584_ = lean_unbox(v_suppressElabErrors_581_);
v___y_9000__boxed_585_ = lean_unbox(v___y_582_);
v_res_586_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(v_suppressElabErrors_boxed_584_, v___y_9000__boxed_585_, v_x_583_);
lean_dec(v_x_583_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_593_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_593_, 10, v___x_591_);
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
lean_object* v___x_610_; lean_object* v_env_611_; uint8_t v___x_612_; lean_object* v_env_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_scopes_616_; lean_object* v___x_617_; lean_object* v_opts_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_610_ = lean_st_ref_get(v___y_608_);
v_env_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_611_);
lean_dec(v___x_610_);
v___x_612_ = 0;
v_env_613_ = l_Lean_Environment_setRecordingDeps(v_env_611_, v___x_612_);
v___x_614_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_615_ = lean_st_ref_get(v___y_608_);
v_scopes_616_ = lean_ctor_get(v___x_615_, 2);
lean_inc(v_scopes_616_);
lean_dec(v___x_615_);
v___x_617_ = l_List_head_x21___redArg(v___x_614_, v_scopes_616_);
lean_dec(v_scopes_616_);
v_opts_618_ = lean_ctor_get(v___x_617_, 1);
lean_inc_ref(v_opts_618_);
lean_dec(v___x_617_);
v___x_619_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_620_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5);
v___x_621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_621_, 0, v_env_613_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_ctor_set(v___x_621_, 3, v_opts_618_);
v___x_622_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_msgData_607_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_624_, v___y_625_);
lean_dec(v___y_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(lean_object* v_ref_628_, lean_object* v_msgData_629_, uint8_t v_severity_630_, uint8_t v_isSilent_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; uint8_t v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; uint8_t v___y_704_; lean_object* v___y_705_; uint8_t v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; uint8_t v___y_737_; uint8_t v___y_738_; uint8_t v___y_739_; uint8_t v___x_754_; uint8_t v___y_756_; uint8_t v___y_757_; uint8_t v___y_758_; uint8_t v___y_760_; uint8_t v___x_772_; 
v___x_754_ = 2;
v___x_772_ = l_Lean_instBEqMessageSeverity_beq(v_severity_630_, v___x_754_);
if (v___x_772_ == 0)
{
v___y_760_ = v___x_772_;
goto v___jp_759_;
}
else
{
uint8_t v___x_773_; 
lean_inc_ref(v_msgData_629_);
v___x_773_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_629_);
v___y_760_ = v___x_773_;
goto v___jp_759_;
}
v___jp_635_:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Elab_Command_getScope___redArg(v___y_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_currNamespace_646_; lean_object* v___x_647_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v_currNamespace_646_ = lean_ctor_get(v_a_645_, 2);
lean_inc(v_currNamespace_646_);
lean_dec(v_a_645_);
v___x_647_ = l_Lean_Elab_Command_getScope___redArg(v___y_643_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_683_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_683_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_683_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_683_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_openDecls_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_env_657_; lean_object* v_messages_658_; lean_object* v_scopes_659_; lean_object* v_usedQuotCtxts_660_; lean_object* v_nextMacroScope_661_; lean_object* v_maxRecDepth_662_; lean_object* v_ngen_663_; lean_object* v_auxDeclNGen_664_; lean_object* v_infoState_665_; lean_object* v_traceState_666_; lean_object* v_snapshotTasks_667_; lean_object* v_prevLinterStates_668_; lean_object* v_codeQualityEntryTasks_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_682_; 
v_openDecls_652_ = lean_ctor_get(v_a_648_, 3);
lean_inc(v_openDecls_652_);
lean_dec(v_a_648_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v_currNamespace_646_);
lean_ctor_set(v___x_653_, 1, v_openDecls_652_);
v___x_654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___y_639_);
lean_inc_ref(v___y_641_);
lean_inc_ref(v___y_638_);
v___x_655_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_655_, 0, v___y_638_);
lean_ctor_set(v___x_655_, 1, v___y_637_);
lean_ctor_set(v___x_655_, 2, v___y_636_);
lean_ctor_set(v___x_655_, 3, v___y_641_);
lean_ctor_set(v___x_655_, 4, v___x_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*5, v___y_640_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*5 + 1, v___y_642_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*5 + 2, v_isSilent_631_);
v___x_656_ = lean_st_ref_take(v___y_643_);
v_env_657_ = lean_ctor_get(v___x_656_, 0);
v_messages_658_ = lean_ctor_get(v___x_656_, 1);
v_scopes_659_ = lean_ctor_get(v___x_656_, 2);
v_usedQuotCtxts_660_ = lean_ctor_get(v___x_656_, 3);
v_nextMacroScope_661_ = lean_ctor_get(v___x_656_, 4);
v_maxRecDepth_662_ = lean_ctor_get(v___x_656_, 5);
v_ngen_663_ = lean_ctor_get(v___x_656_, 6);
v_auxDeclNGen_664_ = lean_ctor_get(v___x_656_, 7);
v_infoState_665_ = lean_ctor_get(v___x_656_, 8);
v_traceState_666_ = lean_ctor_get(v___x_656_, 9);
v_snapshotTasks_667_ = lean_ctor_get(v___x_656_, 10);
v_prevLinterStates_668_ = lean_ctor_get(v___x_656_, 11);
v_codeQualityEntryTasks_669_ = lean_ctor_get(v___x_656_, 12);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_682_ == 0)
{
v___x_671_ = v___x_656_;
v_isShared_672_ = v_isSharedCheck_682_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_codeQualityEntryTasks_669_);
lean_inc(v_prevLinterStates_668_);
lean_inc(v_snapshotTasks_667_);
lean_inc(v_traceState_666_);
lean_inc(v_infoState_665_);
lean_inc(v_auxDeclNGen_664_);
lean_inc(v_ngen_663_);
lean_inc(v_maxRecDepth_662_);
lean_inc(v_nextMacroScope_661_);
lean_inc(v_usedQuotCtxts_660_);
lean_inc(v_scopes_659_);
lean_inc(v_messages_658_);
lean_inc(v_env_657_);
lean_dec(v___x_656_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_682_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = lean_box(0);
v___x_674_ = l_Lean_MessageLog_add(v___x_655_, v_messages_658_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_674_);
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_env_657_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_scopes_659_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_usedQuotCtxts_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_nextMacroScope_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v_maxRecDepth_662_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_ngen_663_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v_auxDeclNGen_664_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v_infoState_665_);
lean_ctor_set(v_reuseFailAlloc_681_, 9, v_traceState_666_);
lean_ctor_set(v_reuseFailAlloc_681_, 10, v_snapshotTasks_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 11, v_prevLinterStates_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 12, v_codeQualityEntryTasks_669_);
v___x_676_ = v_reuseFailAlloc_681_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_st_ref_put(v___y_643_, v___x_676_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_673_);
v___x_679_ = v___x_650_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_673_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_currNamespace_646_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
v_a_684_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_647_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_647_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
v_a_692_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_644_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_644_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
v___jp_700_:
{
lean_object* v_fileName_706_; lean_object* v_fileMap_707_; uint8_t v_suppressElabErrors_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_727_; 
v_fileName_706_ = lean_ctor_get(v___y_632_, 0);
v_fileMap_707_ = lean_ctor_get(v___y_632_, 1);
v_suppressElabErrors_708_ = lean_ctor_get_uint8(v___y_632_, sizeof(void*)*10);
v___x_709_ = lean_box(v_suppressElabErrors_708_);
v___x_710_ = lean_box(v___y_701_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_711_, 0, v___x_709_);
lean_closure_set(v___f_711_, 1, v___x_710_);
v___x_712_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_629_);
v___x_713_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v___x_712_, v___y_633_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_727_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_727_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_727_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_inc_ref_n(v_fileMap_707_, 2);
v___x_718_ = l_Lean_FileMap_toPosition(v_fileMap_707_, v___y_702_);
lean_dec(v___y_702_);
v___x_719_ = l_Lean_FileMap_toPosition(v_fileMap_707_, v___y_705_);
lean_dec(v___y_705_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__9));
if (v_suppressElabErrors_708_ == 0)
{
lean_del_object(v___x_716_);
lean_dec_ref(v___f_711_);
v___y_636_ = v___x_720_;
v___y_637_ = v___x_718_;
v___y_638_ = v_fileName_706_;
v___y_639_ = v_a_714_;
v___y_640_ = v___y_703_;
v___y_641_ = v___x_721_;
v___y_642_ = v___y_704_;
v___y_643_ = v___y_633_;
goto v___jp_635_;
}
else
{
uint8_t v___x_722_; 
lean_inc(v_a_714_);
v___x_722_ = l_Lean_MessageData_hasTag(v___f_711_, v_a_714_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec_ref_known(v___x_720_, 1);
lean_dec_ref(v___x_718_);
lean_dec(v_a_714_);
v___x_723_ = lean_box(0);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_723_);
v___x_725_ = v___x_716_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_del_object(v___x_716_);
v___y_636_ = v___x_720_;
v___y_637_ = v___x_718_;
v___y_638_ = v_fileName_706_;
v___y_639_ = v_a_714_;
v___y_640_ = v___y_703_;
v___y_641_ = v___x_721_;
v___y_642_ = v___y_704_;
v___y_643_ = v___y_633_;
goto v___jp_635_;
}
}
}
}
v___jp_728_:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Syntax_getTailPos_x3f(v___y_730_, v___y_731_);
lean_dec(v___y_730_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_inc(v___y_733_);
v___y_701_ = v___y_729_;
v___y_702_ = v___y_733_;
v___y_703_ = v___y_731_;
v___y_704_ = v___y_732_;
v___y_705_ = v___y_733_;
goto v___jp_700_;
}
else
{
lean_object* v_val_735_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_734_, 1);
v___y_701_ = v___y_729_;
v___y_702_ = v___y_733_;
v___y_703_ = v___y_731_;
v___y_704_ = v___y_732_;
v___y_705_ = v_val_735_;
goto v___jp_700_;
}
}
v___jp_736_:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Elab_Command_getRef___redArg(v___y_632_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v_ref_742_; lean_object* v___x_743_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v_ref_742_ = l_Lean_replaceRef(v_ref_628_, v_a_741_);
lean_dec(v_a_741_);
v___x_743_ = l_Lean_Syntax_getPos_x3f(v_ref_742_, v___y_738_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_744_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___y_729_ = v___y_737_;
v___y_730_ = v_ref_742_;
v___y_731_ = v___y_738_;
v___y_732_ = v___y_739_;
v___y_733_ = v___x_744_;
goto v___jp_728_;
}
else
{
lean_object* v_val_745_; 
v_val_745_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v___x_743_, 1);
v___y_729_ = v___y_737_;
v___y_730_ = v_ref_742_;
v___y_731_ = v___y_738_;
v___y_732_ = v___y_739_;
v___y_733_ = v_val_745_;
goto v___jp_728_;
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_msgData_629_);
v_a_746_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_740_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_740_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
v___jp_755_:
{
if (v___y_758_ == 0)
{
v___y_737_ = v___y_756_;
v___y_738_ = v___y_757_;
v___y_739_ = v_severity_630_;
goto v___jp_736_;
}
else
{
v___y_737_ = v___y_756_;
v___y_738_ = v___y_757_;
v___y_739_ = v___x_754_;
goto v___jp_736_;
}
}
v___jp_759_:
{
if (v___y_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_scopes_763_; lean_object* v___x_764_; lean_object* v_opts_765_; uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_761_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_762_ = lean_st_ref_get(v___y_633_);
v_scopes_763_ = lean_ctor_get(v___x_762_, 2);
lean_inc(v_scopes_763_);
lean_dec(v___x_762_);
v___x_764_ = l_List_head_x21___redArg(v___x_761_, v_scopes_763_);
lean_dec(v_scopes_763_);
v_opts_765_ = lean_ctor_get(v___x_764_, 1);
lean_inc_ref(v_opts_765_);
lean_dec(v___x_764_);
v___x_766_ = 1;
v___x_767_ = l_Lean_instBEqMessageSeverity_beq(v_severity_630_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec_ref(v_opts_765_);
v___y_756_ = v___y_760_;
v___y_757_ = v___y_760_;
v___y_758_ = v___x_767_;
goto v___jp_755_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = l_Lean_warningAsError;
v___x_769_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_765_, v___x_768_);
lean_dec_ref(v_opts_765_);
v___y_756_ = v___y_760_;
v___y_757_ = v___y_760_;
v___y_758_ = v___x_769_;
goto v___jp_755_;
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_msgData_629_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(lean_object* v_ref_774_, lean_object* v_msgData_775_, lean_object* v_severity_776_, lean_object* v_isSilent_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
uint8_t v_severity_boxed_781_; uint8_t v_isSilent_boxed_782_; lean_object* v_res_783_; 
v_severity_boxed_781_ = lean_unbox(v_severity_776_);
v_isSilent_boxed_782_ = lean_unbox(v_isSilent_777_);
v_res_783_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_774_, v_msgData_775_, v_severity_boxed_781_, v_isSilent_boxed_782_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v_ref_774_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(lean_object* v_ref_784_, lean_object* v_msgData_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
uint8_t v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = 1;
v___x_790_ = 0;
v___x_791_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_784_, v_msgData_785_, v___x_789_, v___x_790_, v___y_786_, v___y_787_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(lean_object* v_ref_792_, lean_object* v_msgData_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v_ref_792_, v_msgData_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_ref_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(lean_object* v_t_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_infoState_802_; uint8_t v_enabled_803_; 
v___x_801_ = lean_st_ref_get(v___y_799_);
v_infoState_802_ = lean_ctor_get(v___x_801_, 8);
lean_inc_ref(v_infoState_802_);
lean_dec(v___x_801_);
v_enabled_803_ = lean_ctor_get_uint8(v_infoState_802_, sizeof(void*)*3);
lean_dec_ref(v_infoState_802_);
if (v_enabled_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v_t_798_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v_infoState_807_; lean_object* v_env_808_; lean_object* v_messages_809_; lean_object* v_scopes_810_; lean_object* v_usedQuotCtxts_811_; lean_object* v_nextMacroScope_812_; lean_object* v_maxRecDepth_813_; lean_object* v_ngen_814_; lean_object* v_auxDeclNGen_815_; lean_object* v_traceState_816_; lean_object* v_snapshotTasks_817_; lean_object* v_prevLinterStates_818_; lean_object* v_codeQualityEntryTasks_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_841_; 
v___x_806_ = lean_st_ref_take(v___y_799_);
v_infoState_807_ = lean_ctor_get(v___x_806_, 8);
v_env_808_ = lean_ctor_get(v___x_806_, 0);
v_messages_809_ = lean_ctor_get(v___x_806_, 1);
v_scopes_810_ = lean_ctor_get(v___x_806_, 2);
v_usedQuotCtxts_811_ = lean_ctor_get(v___x_806_, 3);
v_nextMacroScope_812_ = lean_ctor_get(v___x_806_, 4);
v_maxRecDepth_813_ = lean_ctor_get(v___x_806_, 5);
v_ngen_814_ = lean_ctor_get(v___x_806_, 6);
v_auxDeclNGen_815_ = lean_ctor_get(v___x_806_, 7);
v_traceState_816_ = lean_ctor_get(v___x_806_, 9);
v_snapshotTasks_817_ = lean_ctor_get(v___x_806_, 10);
v_prevLinterStates_818_ = lean_ctor_get(v___x_806_, 11);
v_codeQualityEntryTasks_819_ = lean_ctor_get(v___x_806_, 12);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_841_ == 0)
{
v___x_821_ = v___x_806_;
v_isShared_822_ = v_isSharedCheck_841_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_codeQualityEntryTasks_819_);
lean_inc(v_prevLinterStates_818_);
lean_inc(v_snapshotTasks_817_);
lean_inc(v_traceState_816_);
lean_inc(v_infoState_807_);
lean_inc(v_auxDeclNGen_815_);
lean_inc(v_ngen_814_);
lean_inc(v_maxRecDepth_813_);
lean_inc(v_nextMacroScope_812_);
lean_inc(v_usedQuotCtxts_811_);
lean_inc(v_scopes_810_);
lean_inc(v_messages_809_);
lean_inc(v_env_808_);
lean_dec(v___x_806_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_841_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v_enabled_823_; lean_object* v_assignment_824_; lean_object* v_lazyAssignment_825_; lean_object* v_trees_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_840_; 
v_enabled_823_ = lean_ctor_get_uint8(v_infoState_807_, sizeof(void*)*3);
v_assignment_824_ = lean_ctor_get(v_infoState_807_, 0);
v_lazyAssignment_825_ = lean_ctor_get(v_infoState_807_, 1);
v_trees_826_ = lean_ctor_get(v_infoState_807_, 2);
v_isSharedCheck_840_ = !lean_is_exclusive(v_infoState_807_);
if (v_isSharedCheck_840_ == 0)
{
v___x_828_ = v_infoState_807_;
v_isShared_829_ = v_isSharedCheck_840_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_trees_826_);
lean_inc(v_lazyAssignment_825_);
lean_inc(v_assignment_824_);
lean_dec(v_infoState_807_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_840_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_830_ = lean_box(0);
v___x_831_ = l_Lean_PersistentArray_push___redArg(v_trees_826_, v_t_798_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 2, v___x_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_assignment_824_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_lazyAssignment_825_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v___x_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_839_, sizeof(void*)*3, v_enabled_823_);
v___x_833_ = v_reuseFailAlloc_839_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 8, v___x_833_);
v___x_835_ = v___x_821_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_env_808_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_messages_809_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_scopes_810_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_usedQuotCtxts_811_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v_nextMacroScope_812_);
lean_ctor_set(v_reuseFailAlloc_838_, 5, v_maxRecDepth_813_);
lean_ctor_set(v_reuseFailAlloc_838_, 6, v_ngen_814_);
lean_ctor_set(v_reuseFailAlloc_838_, 7, v_auxDeclNGen_815_);
lean_ctor_set(v_reuseFailAlloc_838_, 8, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_838_, 9, v_traceState_816_);
lean_ctor_set(v_reuseFailAlloc_838_, 10, v_snapshotTasks_817_);
lean_ctor_set(v_reuseFailAlloc_838_, 11, v_prevLinterStates_818_);
lean_ctor_set(v_reuseFailAlloc_838_, 12, v_codeQualityEntryTasks_819_);
v___x_835_ = v_reuseFailAlloc_838_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_st_ref_put(v___y_799_, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_830_);
return v___x_837_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_t_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_842_, v___y_843_);
lean_dec(v___y_843_);
return v_res_845_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_unsigned_to_nat(32u);
v___x_847_ = lean_mk_empty_array_with_capacity(v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_849_ = ((size_t)5ULL);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_unsigned_to_nat(32u);
v___x_852_ = lean_mk_empty_array_with_capacity(v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0);
v___x_854_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_850_);
lean_ctor_set(v___x_854_, 3, v___x_850_);
lean_ctor_set_usize(v___x_854_, 4, v___x_849_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(lean_object* v_t_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v_infoState_860_; uint8_t v_enabled_861_; 
v___x_859_ = lean_st_ref_get(v___y_857_);
v_infoState_860_ = lean_ctor_get(v___x_859_, 8);
lean_inc_ref(v_infoState_860_);
lean_dec(v___x_859_);
v_enabled_861_ = lean_ctor_get_uint8(v_infoState_860_, sizeof(void*)*3);
lean_dec_ref(v_infoState_860_);
if (v_enabled_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v_t_855_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1);
v___x_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_865_, 0, v_t_855_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v___x_865_, v___y_857_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(lean_object* v_t_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v_t_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(lean_object* v_info_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_876_, 0, v_info_872_);
v___x_877_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v___x_876_, v___y_873_, v___y_874_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(lean_object* v_info_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v_info_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_882_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_box(1);
v___x_884_ = l_Lean_MessageData_ofFormat(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2));
v___x_889_ = l_Lean_MessageData_ofFormat(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
return v_x_890_;
}
else
{
lean_object* v_head_892_; lean_object* v_tail_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_915_; 
v_head_892_ = lean_ctor_get(v_x_891_, 0);
v_tail_893_ = lean_ctor_get(v_x_891_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_915_ == 0)
{
v___x_895_ = v_x_891_;
v_isShared_896_ = v_isSharedCheck_915_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_tail_893_);
lean_inc(v_head_892_);
lean_dec(v_x_891_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_915_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_before_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_913_; 
v_before_897_ = lean_ctor_get(v_head_892_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_head_892_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v_head_892_, 1);
lean_dec(v_unused_914_);
v___x_899_ = v_head_892_;
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_before_897_);
lean_dec(v_head_892_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 7);
lean_ctor_set(v___x_899_, 1, v___x_901_);
lean_ctor_set(v___x_899_, 0, v_x_890_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_x_890_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_912_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 7);
lean_ctor_set(v___x_895_, 1, v___x_904_);
lean_ctor_set(v___x_895_, 0, v___x_903_);
v___x_906_ = v___x_895_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_911_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = l_Lean_MessageData_ofSyntax(v_before_897_);
v___x_908_ = l_Lean_indentD(v___x_907_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_906_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v_x_890_ = v___x_909_;
v_x_891_ = v_tail_893_;
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
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_920_ = l_Lean_MessageData_ofFormat(v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_921_, lean_object* v_macroStack_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_scopes_927_; lean_object* v___x_928_; lean_object* v_opts_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_925_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_926_ = lean_st_ref_get(v___y_923_);
v_scopes_927_ = lean_ctor_get(v___x_926_, 2);
lean_inc(v_scopes_927_);
lean_dec(v___x_926_);
v___x_928_ = l_List_head_x21___redArg(v___x_925_, v_scopes_927_);
lean_dec(v_scopes_927_);
v_opts_929_ = lean_ctor_get(v___x_928_, 1);
lean_inc_ref(v_opts_929_);
lean_dec(v___x_928_);
v___x_930_ = l_Lean_Elab_pp_macroStack;
v___x_931_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_929_, v___x_930_);
lean_dec_ref(v_opts_929_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v_macroStack_922_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_msgData_921_);
return v___x_932_;
}
else
{
if (lean_obj_tag(v_macroStack_922_) == 0)
{
lean_object* v___x_933_; 
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_msgData_921_);
return v___x_933_;
}
else
{
lean_object* v_head_934_; lean_object* v_after_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_950_; 
v_head_934_ = lean_ctor_get(v_macroStack_922_, 0);
lean_inc(v_head_934_);
v_after_935_ = lean_ctor_get(v_head_934_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_head_934_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_head_934_, 0);
lean_dec(v_unused_951_);
v___x_937_ = v_head_934_;
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_after_935_);
lean_dec(v_head_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_938_ == 0)
{
lean_ctor_set_tag(v___x_937_, 7);
lean_ctor_set(v___x_937_, 1, v___x_939_);
lean_ctor_set(v___x_937_, 0, v_msgData_921_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_msgData_921_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_939_);
v___x_941_ = v_reuseFailAlloc_949_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_msgData_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_942_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_MessageData_ofSyntax(v_after_935_);
v___x_945_ = l_Lean_indentD(v___x_944_);
v_msgData_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_946_, 0, v___x_943_);
lean_ctor_set(v_msgData_946_, 1, v___x_945_);
v___x_947_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(v_msgData_946_, v_macroStack_922_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_952_, lean_object* v_macroStack_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_952_, v_macroStack_953_, v___y_954_);
lean_dec(v___y_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(lean_object* v_msg_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Elab_Command_getRef___redArg(v___y_958_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v_macroStack_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v_macroStack_963_ = lean_ctor_get(v___y_958_, 4);
v___x_964_ = l_Lean_Elab_getBetterRef(v_a_962_, v_macroStack_963_);
lean_dec(v_a_962_);
v___x_965_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msg_957_, v___y_959_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref(v___x_965_);
lean_inc(v_macroStack_963_);
v___x_967_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_a_966_, v_macroStack_963_, v___y_959_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_964_);
lean_ctor_set(v___x_972_, 1, v_a_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 1);
lean_ctor_set(v___x_970_, 0, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref(v_msg_957_);
v_a_977_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_961_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_961_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(lean_object* v_msg_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(lean_object* v_ref_990_, lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Elab_Command_getRef___redArg(v___y_992_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v_fileName_997_; lean_object* v_fileMap_998_; lean_object* v_currRecDepth_999_; lean_object* v_cmdPos_1000_; lean_object* v_macroStack_1001_; lean_object* v_quotContext_x3f_1002_; lean_object* v_currMacroScope_1003_; lean_object* v_snap_x3f_1004_; lean_object* v_cancelTk_x3f_1005_; uint8_t v_suppressElabErrors_1006_; lean_object* v_ref_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v_fileName_997_ = lean_ctor_get(v___y_992_, 0);
v_fileMap_998_ = lean_ctor_get(v___y_992_, 1);
v_currRecDepth_999_ = lean_ctor_get(v___y_992_, 2);
v_cmdPos_1000_ = lean_ctor_get(v___y_992_, 3);
v_macroStack_1001_ = lean_ctor_get(v___y_992_, 4);
v_quotContext_x3f_1002_ = lean_ctor_get(v___y_992_, 5);
v_currMacroScope_1003_ = lean_ctor_get(v___y_992_, 6);
v_snap_x3f_1004_ = lean_ctor_get(v___y_992_, 8);
v_cancelTk_x3f_1005_ = lean_ctor_get(v___y_992_, 9);
v_suppressElabErrors_1006_ = lean_ctor_get_uint8(v___y_992_, sizeof(void*)*10);
v_ref_1007_ = l_Lean_replaceRef(v_ref_990_, v_a_996_);
lean_dec(v_a_996_);
lean_inc(v_cancelTk_x3f_1005_);
lean_inc(v_snap_x3f_1004_);
lean_inc(v_currMacroScope_1003_);
lean_inc(v_quotContext_x3f_1002_);
lean_inc(v_macroStack_1001_);
lean_inc(v_cmdPos_1000_);
lean_inc(v_currRecDepth_999_);
lean_inc_ref(v_fileMap_998_);
lean_inc_ref(v_fileName_997_);
v___x_1008_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1008_, 0, v_fileName_997_);
lean_ctor_set(v___x_1008_, 1, v_fileMap_998_);
lean_ctor_set(v___x_1008_, 2, v_currRecDepth_999_);
lean_ctor_set(v___x_1008_, 3, v_cmdPos_1000_);
lean_ctor_set(v___x_1008_, 4, v_macroStack_1001_);
lean_ctor_set(v___x_1008_, 5, v_quotContext_x3f_1002_);
lean_ctor_set(v___x_1008_, 6, v_currMacroScope_1003_);
lean_ctor_set(v___x_1008_, 7, v_ref_1007_);
lean_ctor_set(v___x_1008_, 8, v_snap_x3f_1004_);
lean_ctor_set(v___x_1008_, 9, v_cancelTk_x3f_1005_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*10, v_suppressElabErrors_1006_);
v___x_1009_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_991_, v___x_1008_, v___y_993_);
lean_dec_ref_known(v___x_1008_, 10);
return v___x_1009_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v_msg_991_);
v_a_1010_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_995_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_995_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(lean_object* v_ref_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1018_, v_msg_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v_ref_1018_);
return v_res_1023_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = lean_box(1);
v___x_1030_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_1031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2);
v___x_1032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
lean_ctor_set(v___x_1032_, 2, v___x_1029_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(lean_object* v_tyName_1054_, lean_object* v_infos_1055_, lean_object* v_as_1056_, size_t v_sz_1057_, size_t v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_a_1064_; uint8_t v___x_1068_; 
v___x_1068_ = lean_usize_dec_lt(v_i_1058_, v_sz_1057_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec(v_tyName_1054_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_b_1059_);
return v___x_1069_;
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_a_1070_ = lean_array_uget_borrowed(v_as_1056_, v_i_1058_);
v___x_1071_ = ((lean_object*)(l_Lake_DSL_declField___closed__1));
lean_inc(v_a_1070_);
v___x_1072_ = l_Lean_Syntax_isOfKind(v_a_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1);
v___x_1074_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_a_1070_, v___x_1073_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_dec_ref_known(v___x_1074_, 1);
v_a_1064_ = v_b_1059_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_b_1059_);
lean_dec(v_tyName_1054_);
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = l_Lean_Syntax_getArg(v_a_1070_, v___x_1083_);
v___x_1085_ = lean_unsigned_to_nat(2u);
v___x_1086_ = l_Lean_Syntax_getArg(v_a_1070_, v___x_1085_);
v___x_1087_ = l_Lean_TSyntax_getId(v___x_1084_);
lean_inc(v___x_1087_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3);
lean_inc(v_tyName_1054_);
lean_inc(v_a_1070_);
v___x_1090_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1090_, 0, v_a_1070_);
lean_ctor_set(v___x_1090_, 1, v___x_1088_);
lean_ctor_set(v___x_1090_, 2, v___x_1089_);
lean_ctor_set(v___x_1090_, 3, v_tyName_1054_);
v___x_1091_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v___x_1090_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1092_; 
lean_dec_ref_known(v___x_1091_, 1);
v___x_1092_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_infos_1055_, v___x_1087_);
if (lean_obj_tag(v___x_1092_) == 1)
{
lean_object* v_val_1093_; lean_object* v_realName_1094_; uint8_t v_canonical_1095_; 
v_val_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v_realName_1094_ = lean_ctor_get(v_val_1093_, 1);
lean_inc(v_realName_1094_);
v_canonical_1095_ = lean_ctor_get_uint8(v_val_1093_, sizeof(void*)*2);
lean_dec(v_val_1093_);
if (v_canonical_1095_ == 0)
{
if (v___x_1072_ == 0)
{
lean_dec(v___x_1087_);
goto v___jp_1096_;
}
else
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_realName_1094_, v_b_1059_);
if (v___x_1099_ == 0)
{
lean_dec(v___x_1087_);
goto v___jp_1096_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1100_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5);
lean_inc(v_realName_1094_);
v___x_1101_ = l_Lean_MessageData_ofName(v_realName_1094_);
lean_inc_ref(v___x_1101_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_MessageData_ofName(v___x_1087_);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v___x_1101_);
v___x_1110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1084_, v___x_1111_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_dec_ref_known(v___x_1112_, 1);
goto v___jp_1096_;
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_realName_1094_);
lean_dec(v___x_1086_);
lean_dec(v___x_1084_);
lean_dec(v_b_1059_);
lean_dec(v_tyName_1054_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1087_);
goto v___jp_1096_;
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1084_);
lean_ctor_set(v___x_1097_, 1, v___x_1086_);
v___x_1098_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_realName_1094_, v___x_1097_, v_b_1059_);
v_a_1064_ = v___x_1098_;
goto v___jp_1063_;
}
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v___x_1092_);
lean_dec(v___x_1086_);
v___x_1121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13);
v___x_1122_ = 0;
lean_inc(v_tyName_1054_);
v___x_1123_ = l_Lean_MessageData_ofConstName(v_tyName_1054_, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1121_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_MessageData_ofName(v___x_1087_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1084_, v___x_1130_, v___y_1060_, v___y_1061_);
lean_dec(v___x_1084_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_dec_ref_known(v___x_1131_, 1);
v_a_1064_ = v_b_1059_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_b_1059_);
lean_dec(v_tyName_1054_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v___x_1087_);
lean_dec(v___x_1086_);
lean_dec(v___x_1084_);
lean_dec(v_b_1059_);
lean_dec(v_tyName_1054_);
v_a_1140_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1091_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1091_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
v___jp_1063_:
{
size_t v___x_1065_; size_t v___x_1066_; 
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1058_, v___x_1065_);
v_i_1058_ = v___x_1066_;
v_b_1059_ = v_a_1064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(lean_object* v_tyName_1148_, lean_object* v_infos_1149_, lean_object* v_as_1150_, lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1148_, v_infos_1149_, v_as_1150_, v_sz_boxed_1157_, v_i_boxed_1158_, v_b_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_as_1150_);
lean_dec(v_infos_1149_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object* v_tyName_1171_, lean_object* v_infos_1172_, lean_object* v_fs_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_m_1177_; size_t v_sz_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v_m_1177_ = lean_box(1);
v_sz_1178_ = lean_array_size(v_fs_1173_);
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1171_, v_infos_1172_, v_fs_1173_, v_sz_1178_, v___x_1179_, v_m_1177_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1199_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v___x_1182_, v_a_1181_);
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1188_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
v___x_1189_ = lean_box(2);
v___x_1190_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2));
v___x_1191_ = l_Lean_Syntax_mkSep(v_a_1184_, v___x_1190_);
lean_dec(v_a_1184_);
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_mk_empty_array_with_capacity(v___x_1192_);
v___x_1194_ = lean_array_push(v___x_1193_, v___x_1191_);
v___x_1195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v___x_1188_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1195_);
v___x_1197_ = v___x_1186_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1180_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1180_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(lean_object* v_tyName_1208_, lean_object* v_infos_1209_, lean_object* v_fs_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1208_, v_infos_1209_, v_fs_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec_ref(v_fs_1210_);
lean_dec(v_infos_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_object* v_00_u03b1_1215_, lean_object* v_ref_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1216_, v_msg_1217_, v___y_1218_, v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_ref_1223_, lean_object* v_msg_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(v_00_u03b1_1222_, v_ref_1223_, v_msg_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v_ref_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(lean_object* v_init_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_1229_, v_x_1230_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(lean_object* v_init_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(v_init_1235_, v_x_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(lean_object* v_msgData_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_1241_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(v_msgData_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_object* v_00_u03b1_1251_, lean_object* v_msg_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_1252_, v___y_1253_, v___y_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_msg_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(v_00_u03b1_1257_, v_msg_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(lean_object* v_t_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_1263_, v___y_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(lean_object* v_t_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(v_t_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(lean_object* v_msgData_1273_, lean_object* v_macroStack_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_1273_, v_macroStack_1274_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1279_, lean_object* v_macroStack_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(v_msgData_1279_, v_macroStack_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v_env_1288_; lean_object* v___x_1289_; lean_object* v_mainModule_1290_; lean_object* v___x_1291_; 
v___x_1287_ = lean_st_ref_get(v___y_1285_);
v_env_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc_ref(v_env_1288_);
lean_dec(v___x_1287_);
v___x_1289_ = l_Lean_Environment_header(v_env_1288_);
lean_dec_ref(v_env_1288_);
v_mainModule_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_mainModule_1290_);
lean_dec_ref(v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_mainModule_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1292_);
lean_dec(v___y_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object* v___x_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_a_1300_; lean_object* v_quotContext_x3f_1319_; 
v_quotContext_x3f_1319_ = lean_ctor_get(v___y_1296_, 5);
if (lean_obj_tag(v_quotContext_x3f_1319_) == 0)
{
lean_object* v___x_1320_; lean_object* v_a_1321_; 
v___x_1320_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1297_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1320_);
v_a_1300_ = v_a_1321_;
goto v___jp_1299_;
}
else
{
lean_object* v_val_1322_; 
v_val_1322_ = lean_ctor_get(v_quotContext_x3f_1319_, 0);
lean_inc(v_val_1322_);
v_a_1300_ = v_val_1322_;
goto v___jp_1299_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1296_);
lean_dec_ref(v___y_1296_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1310_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = l_Lean_addMacroScope(v_a_1300_, v___x_1295_, v_a_1302_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1300_);
lean_dec(v___x_1295_);
v_a_1311_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1301_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1301_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object* v___x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(v___x_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___f_1336_; lean_object* v___x_1337_; 
v___f_1336_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2));
v___x_1337_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___f_1336_, v___y_1333_, v___y_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(lean_object* v_ref_1342_, uint8_t v_canonical_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1356_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = l_Lean_mkIdentFrom(v_ref_1342_, v_a_1348_, v_canonical_1343_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_a_1357_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1347_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1347_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object* v_ref_1365_, lean_object* v_canonical_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_canonical_boxed_1370_; lean_object* v_res_1371_; 
v_canonical_boxed_1370_ = lean_unbox(v_canonical_1366_);
v_res_1371_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_ref_1365_, v_canonical_boxed_1370_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v_ref_1365_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object* v_stx_x3f_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
if (lean_obj_tag(v_stx_x3f_1372_) == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Elab_Command_getRef___redArg(v_a_1373_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = 0;
v___x_1379_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_a_1377_, v___x_1378_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1377_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1376_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1376_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_object* v_val_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1396_; 
v_val_1388_ = lean_ctor_get(v_stx_x3f_1372_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_stx_x3f_1372_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1390_ = v_stx_x3f_1372_;
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_val_1388_);
lean_dec(v_stx_x3f_1372_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = l_Lake_DSL_expandIdentOrStrAsIdent(v_val_1388_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set_tag(v___x_1390_, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1392_);
v___x_1394_ = v___x_1390_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object* v_stx_x3f_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lake_DSL_mkConfigDeclIdent(v_stx_x3f_1397_, v_a_1398_, v_a_1399_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1409_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__6(void){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_instMonadEIO___redArg();
return v___x_1416_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__7(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__6, &l_Lake_DSL_elabConfig___closed__6_once, _init_l_Lake_DSL_elabConfig___closed__6);
v___x_1418_ = l_StateRefT_x27_instMonad___redArg(v___x_1417_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__13(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1428_ = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
v___x_1429_ = l_Lean_Elab_Command_instMonadRefCommandElabM;
v___x_1430_ = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
v___x_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
lean_ctor_set(v___x_1431_, 2, v___x_1428_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__15(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__14));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object* v_tyName_1435_, lean_object* v_info_1436_, lean_object* v_id_1437_, lean_object* v_ty_1438_, lean_object* v_config_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v_whereInfo_1555_; lean_object* v_fs_1556_; lean_object* v_wds_x3f_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___x_1586_; lean_object* v_toApplicative_1587_; lean_object* v_toFunctor_1588_; lean_object* v_toSeq_1589_; lean_object* v_toSeqLeft_1590_; lean_object* v_toSeqRight_1591_; lean_object* v___f_1592_; lean_object* v___f_1593_; lean_object* v___f_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1586_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1587_ = lean_ctor_get(v___x_1586_, 0);
v_toFunctor_1588_ = lean_ctor_get(v_toApplicative_1587_, 0);
v_toSeq_1589_ = lean_ctor_get(v_toApplicative_1587_, 2);
v_toSeqLeft_1590_ = lean_ctor_get(v_toApplicative_1587_, 3);
v_toSeqRight_1591_ = lean_ctor_get(v_toApplicative_1587_, 4);
v___f_1592_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1593_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1588_, 2);
v___f_1594_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1594_, 0, v_toFunctor_1588_);
v___f_1595_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1595_, 0, v_toFunctor_1588_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___f_1594_);
lean_ctor_set(v___x_1596_, 1, v___f_1595_);
lean_inc(v_toSeqRight_1591_);
v___f_1597_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1597_, 0, v_toSeqRight_1591_);
lean_inc(v_toSeqLeft_1590_);
v___f_1598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1598_, 0, v_toSeqLeft_1590_);
lean_inc(v_toSeq_1589_);
v___f_1599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1599_, 0, v_toSeq_1589_);
v___x_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1596_);
lean_ctor_set(v___x_1600_, 1, v___f_1592_);
lean_ctor_set(v___x_1600_, 2, v___f_1599_);
lean_ctor_set(v___x_1600_, 3, v___f_1598_);
lean_ctor_set(v___x_1600_, 4, v___f_1597_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___f_1593_);
v___x_1602_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1603_ = ((lean_object*)(l_Lake_DSL_optConfig___closed__1));
lean_inc(v_config_1439_);
v___x_1604_ = l_Lean_Syntax_isOfKind(v_config_1439_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_2422__overap_1606_; lean_object* v___x_1607_; 
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1605_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2422__overap_1606_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1605_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1607_ = lean_apply_3(v___x_2422__overap_1606_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = l_Lean_Syntax_getArg(v_config_1439_, v___x_1608_);
lean_inc(v___x_1609_);
v___x_1610_ = l_Lean_Syntax_matchesNull(v___x_1609_, v___x_1608_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1609_);
v___x_1612_ = l_Lean_Syntax_matchesNull(v___x_1609_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_2424__overap_1614_; lean_object* v___x_1615_; 
lean_dec(v___x_1609_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1613_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2424__overap_1614_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1613_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1615_ = lean_apply_3(v___x_2424__overap_1614_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = l_Lean_Syntax_getArg(v___x_1609_, v___x_1608_);
lean_dec(v___x_1609_);
v___x_1617_ = ((lean_object*)(l_Lake_DSL_declValWhere___closed__1));
lean_inc(v___x_1616_);
v___x_1618_ = l_Lean_Syntax_isOfKind(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lake_DSL_declValStruct___closed__1));
lean_inc(v___x_1616_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v___x_1616_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_2426__overap_1622_; lean_object* v___x_1623_; 
lean_dec(v___x_1616_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1621_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2426__overap_1622_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1621_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1623_ = lean_apply_3(v___x_2426__overap_1622_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1624_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1608_);
v___x_1625_ = ((lean_object*)(l_Lake_DSL_structVal___closed__1));
lean_inc(v___x_1624_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v___x_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_2428__overap_1628_; lean_object* v___x_1629_; 
lean_dec(v___x_1624_);
lean_dec(v___x_1616_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1627_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2428__overap_1628_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1627_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1629_ = lean_apply_3(v___x_2428__overap_1628_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1630_ = l_Lean_Syntax_getArg(v___x_1624_, v___x_1611_);
v___x_1631_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1630_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_2430__overap_1634_; lean_object* v___x_1635_; 
lean_dec(v___x_1630_);
lean_dec(v___x_1624_);
lean_dec(v___x_1616_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1633_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2430__overap_1634_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1633_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1635_ = lean_apply_3(v___x_2430__overap_1634_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1635_;
}
else
{
lean_object* v_tk_1636_; lean_object* v___x_1637_; lean_object* v_wds_x3f_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v_tk_1636_ = l_Lean_Syntax_getArg(v___x_1624_, v___x_1608_);
lean_dec(v___x_1624_);
v___x_1637_ = l_Lean_Syntax_getArg(v___x_1630_, v___x_1608_);
lean_dec(v___x_1630_);
v___x_1645_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1611_);
lean_dec(v___x_1616_);
v___x_1646_ = l_Lean_Syntax_isNone(v___x_1645_);
if (v___x_1646_ == 0)
{
uint8_t v___x_1647_; 
lean_inc(v___x_1645_);
v___x_1647_ = l_Lean_Syntax_matchesNull(v___x_1645_, v___x_1611_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_2433__overap_1649_; lean_object* v___x_1650_; 
lean_dec(v___x_1645_);
lean_dec(v___x_1637_);
lean_dec(v_tk_1636_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1648_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2433__overap_1649_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1648_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1650_ = lean_apply_3(v___x_2433__overap_1649_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1650_;
}
else
{
lean_object* v_wds_x3f_1651_; 
v_wds_x3f_1651_ = l_Lean_Syntax_getArg(v___x_1645_, v___x_1608_);
lean_dec(v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1651_);
v___x_1655_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1651_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_2435__overap_1657_; lean_object* v___x_1658_; 
lean_dec(v_wds_x3f_1651_);
lean_dec(v___x_1637_);
lean_dec(v_tk_1636_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1656_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2435__overap_1657_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1656_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1658_ = lean_apply_3(v___x_2435__overap_1657_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1658_;
}
else
{
lean_dec_ref_known(v___x_1601_, 2);
goto v___jp_1652_;
}
}
else
{
lean_dec_ref_known(v___x_1601_, 2);
goto v___jp_1652_;
}
v___jp_1652_:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_wds_x3f_1651_);
v_wds_x3f_1639_ = v___x_1653_;
v___y_1640_ = v_a_1440_;
v___y_1641_ = v_a_1441_;
goto v___jp_1638_;
}
}
}
else
{
lean_object* v___x_1659_; 
lean_dec(v___x_1645_);
lean_dec_ref_known(v___x_1601_, 2);
v___x_1659_ = lean_box(0);
v_wds_x3f_1639_ = v___x_1659_;
v___y_1640_ = v_a_1440_;
v___y_1641_ = v_a_1441_;
goto v___jp_1638_;
}
v___jp_1638_:
{
lean_object* v_fs_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_fs_1642_ = l_Lean_Syntax_getArgs(v___x_1637_);
lean_dec(v___x_1637_);
v___x_1643_ = l_Lean_Syntax_getHeadInfo(v_tk_1636_);
lean_dec(v_tk_1636_);
v___x_1644_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1642_);
lean_dec_ref(v_fs_1642_);
v_whereInfo_1555_ = v___x_1643_;
v_fs_1556_ = v___x_1644_;
v_wds_x3f_1557_ = v_wds_x3f_1639_;
v___y_1558_ = v___y_1640_;
v___y_1559_ = v___y_1641_;
goto v___jp_1554_;
}
}
}
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1660_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1611_);
v___x_1661_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1660_);
v___x_1662_ = l_Lean_Syntax_isOfKind(v___x_1660_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_2437__overap_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1660_);
lean_dec(v___x_1616_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1663_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2437__overap_1664_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1663_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1665_ = lean_apply_3(v___x_2437__overap_1664_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1665_;
}
else
{
lean_object* v_tk_1666_; lean_object* v___x_1667_; lean_object* v_wds_x3f_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_tk_1666_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1608_);
v___x_1667_ = l_Lean_Syntax_getArg(v___x_1660_, v___x_1608_);
lean_dec(v___x_1660_);
v___x_1675_ = lean_unsigned_to_nat(2u);
v___x_1676_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1675_);
lean_dec(v___x_1616_);
v___x_1677_ = l_Lean_Syntax_isNone(v___x_1676_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; 
lean_inc(v___x_1676_);
v___x_1678_ = l_Lean_Syntax_matchesNull(v___x_1676_, v___x_1611_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_2440__overap_1680_; lean_object* v___x_1681_; 
lean_dec(v___x_1676_);
lean_dec(v___x_1667_);
lean_dec(v_tk_1666_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1679_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2440__overap_1680_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1679_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1681_ = lean_apply_3(v___x_2440__overap_1680_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1681_;
}
else
{
lean_object* v_wds_x3f_1682_; 
v_wds_x3f_1682_ = l_Lean_Syntax_getArg(v___x_1676_, v___x_1608_);
lean_dec(v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1682_);
v___x_1686_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1682_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_2442__overap_1688_; lean_object* v___x_1689_; 
lean_dec(v_wds_x3f_1682_);
lean_dec(v___x_1667_);
lean_dec(v_tk_1666_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
lean_dec(v_tyName_1435_);
v___x_1687_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2442__overap_1688_ = l_Lean_throwErrorAt___redArg(v___x_1601_, v___x_1602_, v_config_1439_, v___x_1687_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1689_ = lean_apply_3(v___x_2442__overap_1688_, v_a_1440_, v_a_1441_, lean_box(0));
return v___x_1689_;
}
else
{
lean_dec_ref_known(v___x_1601_, 2);
goto v___jp_1683_;
}
}
else
{
lean_dec_ref_known(v___x_1601_, 2);
goto v___jp_1683_;
}
v___jp_1683_:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_wds_x3f_1682_);
v_wds_x3f_1669_ = v___x_1684_;
v___y_1670_ = v_a_1440_;
v___y_1671_ = v_a_1441_;
goto v___jp_1668_;
}
}
}
else
{
lean_object* v___x_1690_; 
lean_dec(v___x_1676_);
lean_dec_ref_known(v___x_1601_, 2);
v___x_1690_ = lean_box(0);
v_wds_x3f_1669_ = v___x_1690_;
v___y_1670_ = v_a_1440_;
v___y_1671_ = v_a_1441_;
goto v___jp_1668_;
}
v___jp_1668_:
{
lean_object* v_fs_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_fs_1672_ = l_Lean_Syntax_getArgs(v___x_1667_);
lean_dec(v___x_1667_);
v___x_1673_ = l_Lean_Syntax_getHeadInfo(v_tk_1666_);
lean_dec(v_tk_1666_);
v___x_1674_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1672_);
lean_dec_ref(v_fs_1672_);
v_whereInfo_1555_ = v___x_1673_;
v_fs_1556_ = v___x_1674_;
v_wds_x3f_1557_ = v_wds_x3f_1669_;
v___y_1558_ = v___y_1670_;
v___y_1559_ = v___y_1671_;
goto v___jp_1554_;
}
}
}
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v___x_1609_);
lean_dec_ref_known(v___x_1601_, 2);
v___x_1691_ = lean_box(2);
v___x_1692_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1693_ = lean_box(0);
v_whereInfo_1555_ = v___x_1691_;
v_fs_1556_ = v___x_1692_;
v_wds_x3f_1557_ = v___x_1693_;
v___y_1558_ = v_a_1440_;
v___y_1559_ = v_a_1441_;
goto v___jp_1554_;
}
}
v___jp_1443_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1452_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__0));
lean_inc_ref_n(v___y_1450_, 5);
lean_inc_ref_n(v___y_1447_, 6);
lean_inc_ref_n(v___y_1448_, 6);
v___x_1453_ = l_Lean_Name_mkStr4(v___y_1448_, v___y_1447_, v___y_1450_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__1));
v___x_1455_ = l_Lean_Name_mkStr4(v___y_1448_, v___y_1447_, v___y_1450_, v___x_1454_);
v___x_1456_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
v___x_1457_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
lean_inc_n(v___y_1444_, 8);
v___x_1458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1458_, 0, v___y_1444_);
lean_ctor_set(v___x_1458_, 1, v___x_1456_);
lean_ctor_set(v___x_1458_, 2, v___x_1457_);
lean_inc_ref_n(v___x_1458_, 8);
v___x_1459_ = l_Lean_Syntax_node7(v___y_1444_, v___x_1455_, v___x_1458_, v___x_1458_, v___x_1458_, v___x_1458_, v___x_1458_, v___x_1458_, v___x_1458_);
v___x_1460_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__2));
v___x_1461_ = l_Lean_Name_mkStr4(v___y_1448_, v___y_1447_, v___y_1450_, v___x_1460_);
v___x_1462_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__3));
v___x_1463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___y_1444_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__4));
v___x_1465_ = l_Lean_Name_mkStr4(v___y_1448_, v___y_1447_, v___y_1450_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
lean_inc_n(v___y_1449_, 2);
v___x_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1449_);
lean_ctor_set(v___x_1467_, 1, v___x_1456_);
lean_ctor_set(v___x_1467_, 2, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(2u);
v___x_1469_ = lean_mk_empty_array_with_capacity(v___x_1468_);
v___x_1470_ = lean_array_push(v___x_1469_, v_id_1437_);
v___x_1471_ = lean_array_push(v___x_1470_, v___x_1467_);
v___x_1472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1449_);
lean_ctor_set(v___x_1472_, 1, v___x_1465_);
lean_ctor_set(v___x_1472_, 2, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__5));
v___x_1474_ = l_Lean_Name_mkStr4(v___y_1448_, v___y_1447_, v___y_1450_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__2));
v___x_1476_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__2));
v___x_1477_ = l_Lean_Name_mkStr4(v___y_1448_, v___y_1447_, v___x_1475_, v___x_1476_);
v___x_1478_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__26));
v___x_1479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___y_1444_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_node2(v___y_1444_, v___x_1477_, v___x_1479_, v_ty_1438_);
v___x_1481_ = l_Lean_Syntax_node1(v___y_1444_, v___x_1456_, v___x_1480_);
v___x_1482_ = l_Lean_Syntax_node2(v___y_1444_, v___x_1474_, v___x_1458_, v___x_1481_);
v___x_1483_ = l_Lean_Syntax_node5(v___y_1444_, v___x_1461_, v___x_1463_, v___x_1472_, v___x_1482_, v___y_1451_, v___x_1458_);
v___x_1484_ = l_Lean_Syntax_node2(v___y_1444_, v___x_1453_, v___x_1459_, v___x_1483_);
lean_inc(v___x_1484_);
v___x_1485_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_1485_, 0, v___x_1484_);
v___x_1486_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_1439_, v___x_1484_, v___x_1485_, v___y_1445_, v___y_1446_);
return v___x_1486_;
}
v___jp_1487_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1497_ = l_Lean_mkOptionalNode(v___y_1496_);
v___x_1498_ = lean_unsigned_to_nat(3u);
v___x_1499_ = lean_mk_empty_array_with_capacity(v___x_1498_);
v___x_1500_ = lean_array_push(v___x_1499_, v___y_1495_);
v___x_1501_ = lean_array_push(v___x_1500_, v___y_1494_);
v___x_1502_ = lean_array_push(v___x_1501_, v___x_1497_);
v___x_1503_ = lean_box(2);
lean_inc(v___y_1490_);
v___x_1504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___y_1490_);
lean_ctor_set(v___x_1504_, 2, v___x_1502_);
v___x_1505_ = l_Lean_Elab_Command_getRef___redArg(v___y_1488_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = 0;
v___x_1508_ = l_Lean_SourceInfo_fromRef(v_a_1506_, v___x_1507_);
lean_dec(v_a_1506_);
v___x_1509_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1488_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1510_; lean_object* v_toApplicative_1511_; lean_object* v_toFunctor_1512_; lean_object* v_toSeq_1513_; lean_object* v_toSeqLeft_1514_; lean_object* v_toSeqRight_1515_; lean_object* v___f_1516_; lean_object* v___f_1517_; lean_object* v___f_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; lean_object* v___f_1521_; lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_quotContext_x3f_1527_; 
lean_dec_ref_known(v___x_1509_, 1);
v___x_1510_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1511_ = lean_ctor_get(v___x_1510_, 0);
v_toFunctor_1512_ = lean_ctor_get(v_toApplicative_1511_, 0);
v_toSeq_1513_ = lean_ctor_get(v_toApplicative_1511_, 2);
v_toSeqLeft_1514_ = lean_ctor_get(v_toApplicative_1511_, 3);
v_toSeqRight_1515_ = lean_ctor_get(v_toApplicative_1511_, 4);
v___f_1516_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1517_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1512_, 2);
v___f_1518_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1518_, 0, v_toFunctor_1512_);
v___f_1519_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1519_, 0, v_toFunctor_1512_);
v___x_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___f_1518_);
lean_ctor_set(v___x_1520_, 1, v___f_1519_);
lean_inc(v_toSeqRight_1515_);
v___f_1521_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1521_, 0, v_toSeqRight_1515_);
lean_inc(v_toSeqLeft_1514_);
v___f_1522_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1522_, 0, v_toSeqLeft_1514_);
lean_inc(v_toSeq_1513_);
v___f_1523_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1523_, 0, v_toSeq_1513_);
v___x_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1520_);
lean_ctor_set(v___x_1524_, 1, v___f_1516_);
lean_ctor_set(v___x_1524_, 2, v___f_1523_);
lean_ctor_set(v___x_1524_, 3, v___f_1522_);
lean_ctor_set(v___x_1524_, 4, v___f_1521_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___f_1517_);
v___x_1526_ = l_Lean_Elab_Command_instMonadEnvCommandElabM;
v_quotContext_x3f_1527_ = lean_ctor_get(v___y_1488_, 5);
if (lean_obj_tag(v_quotContext_x3f_1527_) == 0)
{
lean_object* v___x_2408__overap_1528_; lean_object* v___x_1529_; 
v___x_2408__overap_1528_ = l_Lean_getMainModule___redArg(v___x_1525_, v___x_1526_);
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1488_);
v___x_1529_ = lean_apply_3(v___x_2408__overap_1528_, v___y_1488_, v___y_1489_, lean_box(0));
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_dec_ref_known(v___x_1529_, 1);
v___y_1444_ = v___x_1508_;
v___y_1445_ = v___y_1488_;
v___y_1446_ = v___y_1489_;
v___y_1447_ = v___y_1492_;
v___y_1448_ = v___y_1491_;
v___y_1449_ = v___x_1503_;
v___y_1450_ = v___y_1493_;
v___y_1451_ = v___x_1504_;
goto v___jp_1443_;
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v___x_1508_);
lean_dec_ref_known(v___x_1504_, 3);
lean_dec(v_config_1439_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1525_, 2);
v___y_1444_ = v___x_1508_;
v___y_1445_ = v___y_1488_;
v___y_1446_ = v___y_1489_;
v___y_1447_ = v___y_1492_;
v___y_1448_ = v___y_1491_;
v___y_1449_ = v___x_1503_;
v___y_1450_ = v___y_1493_;
v___y_1451_ = v___x_1504_;
goto v___jp_1443_;
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v___x_1508_);
lean_dec_ref_known(v___x_1504_, 3);
lean_dec(v_config_1439_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
v_a_1538_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1509_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1509_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref_known(v___x_1504_, 3);
lean_dec(v_config_1439_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
v_a_1546_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1505_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1505_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
v___jp_1554_:
{
lean_object* v_fieldMap_1560_; lean_object* v___x_1561_; lean_object* v_whereTk_1562_; lean_object* v___x_1563_; 
v_fieldMap_1560_ = lean_ctor_get(v_info_1436_, 1);
v___x_1561_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__10));
v_whereTk_1562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_1562_, 0, v_whereInfo_1555_);
lean_ctor_set(v_whereTk_1562_, 1, v___x_1561_);
v___x_1563_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1435_, v_fieldMap_1560_, v_fs_1556_, v___y_1558_, v___y_1559_);
lean_dec_ref(v_fs_1556_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__0));
v___x_1566_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__1));
v___x_1567_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__6));
v___x_1568_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__12));
if (lean_obj_tag(v_wds_x3f_1557_) == 0)
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_box(0);
v___y_1488_ = v___y_1558_;
v___y_1489_ = v___y_1559_;
v___y_1490_ = v___x_1568_;
v___y_1491_ = v___x_1565_;
v___y_1492_ = v___x_1566_;
v___y_1493_ = v___x_1567_;
v___y_1494_ = v_a_1564_;
v___y_1495_ = v_whereTk_1562_;
v___y_1496_ = v___x_1569_;
goto v___jp_1487_;
}
else
{
lean_object* v_val_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_val_1570_ = lean_ctor_get(v_wds_x3f_1557_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_wds_x3f_1557_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v_wds_x3f_1557_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_val_1570_);
lean_dec(v_wds_x3f_1557_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_val_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
v___y_1488_ = v___y_1558_;
v___y_1489_ = v___y_1559_;
v___y_1490_ = v___x_1568_;
v___y_1491_ = v___x_1565_;
v___y_1492_ = v___x_1566_;
v___y_1493_ = v___x_1567_;
v___y_1494_ = v_a_1564_;
v___y_1495_ = v_whereTk_1562_;
v___y_1496_ = v___x_1575_;
goto v___jp_1487_;
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref_known(v_whereTk_1562_, 2);
lean_dec(v_wds_x3f_1557_);
lean_dec(v_config_1439_);
lean_dec(v_ty_1438_);
lean_dec(v_id_1437_);
v_a_1578_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1563_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1563_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object* v_tyName_1694_, lean_object* v_info_1695_, lean_object* v_id_1696_, lean_object* v_ty_1697_, lean_object* v_config_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lake_DSL_elabConfig(v_tyName_1694_, v_info_1695_, v_id_1696_, v_ty_1697_, v_config_1698_, v_a_1699_, v_a_1700_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v_info_1695_);
return v_res_1702_;
}
}
lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
