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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_quotContext_434_; lean_object* v_currMacroScope_435_; lean_object* v_ref_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v_ty_x3f_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
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
v___x_439_ = l_Lean_SourceInfo_fromRef(v_ref_436_, v___x_421_);
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
lean_inc(v_currMacroScope_435_);
lean_inc(v_quotContext_434_);
v___x_447_ = l_Lean_addMacroScope(v_quotContext_434_, v___x_446_, v_currMacroScope_435_);
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
lean_ctor_set(v___x_459_, 1, v___y_437_);
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
v_quotContext_434_ = v_quotContext_464_;
v_currMacroScope_435_ = v_currMacroScope_465_;
v_ref_436_ = v_ref_466_;
v___y_437_ = v___y_463_;
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
v_quotContext_434_ = v_quotContext_472_;
v_currMacroScope_435_ = v_currMacroScope_473_;
v_ref_436_ = v_ref_474_;
v___y_437_ = v___y_463_;
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
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(lean_object* v_init_528_, lean_object* v_x_529_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_528_ = stack[0].m_obj;
lean_object* v_x_529_ = stack[1].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_528_, v_x_529_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___boxed(lean_object* v_init_556_, lean_object* v_x_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_556_, v_x_557_);
return v_res_559_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(lean_object* v_opts_560_, lean_object* v_opt_561_){
_start:
{
lean_object* v_name_562_; lean_object* v_defValue_563_; lean_object* v_map_564_; lean_object* v___x_565_; 
v_name_562_ = lean_ctor_get(v_opt_561_, 0);
v_defValue_563_ = lean_ctor_get(v_opt_561_, 1);
v_map_564_ = lean_ctor_get(v_opts_560_, 0);
v___x_565_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_564_, v_name_562_);
if (lean_obj_tag(v___x_565_) == 0)
{
uint8_t v___x_566_; 
v___x_566_ = lean_unbox(v_defValue_563_);
return v___x_566_;
}
else
{
lean_object* v_val_567_; 
v_val_567_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_565_, 1);
if (lean_obj_tag(v_val_567_) == 1)
{
uint8_t v_v_568_; 
v_v_568_ = lean_ctor_get_uint8(v_val_567_, 0);
lean_dec_ref_known(v_val_567_, 0);
return v_v_568_;
}
else
{
uint8_t v___x_569_; 
lean_dec(v_val_567_);
v___x_569_ = lean_unbox(v_defValue_563_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_560_ = stack[0].m_obj;
lean_object* v_opt_561_ = stack[1].m_obj;
uint8_t v_res_570_;
v_res_570_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_560_, v_opt_561_);
stack->m_num = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8___boxed(lean_object* v_opts_571_, lean_object* v_opt_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_571_, v_opt_572_);
lean_dec_ref(v_opt_572_);
lean_dec_ref(v_opts_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t v_suppressElabErrors_576_, uint8_t v___y_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 1)
{
lean_object* v_pre_579_; 
v_pre_579_ = lean_ctor_get(v_x_578_, 0);
if (lean_obj_tag(v_pre_579_) == 0)
{
lean_object* v_str_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_str_580_ = lean_ctor_get(v_x_578_, 1);
v___x_581_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0));
v___x_582_ = lean_string_dec_eq(v_str_580_, v___x_581_);
if (v___x_582_ == 0)
{
return v___x_582_;
}
else
{
return v_suppressElabErrors_576_;
}
}
else
{
return v___y_577_;
}
}
else
{
return v___y_577_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_576_ = stack[0].m_num;
uint8_t v___y_577_ = stack[1].m_num;
lean_object* v_x_578_ = stack[2].m_obj;
uint8_t v_res_583_;
v_res_583_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(v_suppressElabErrors_576_, v___y_577_, v_x_578_);
stack->m_num = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_584_, lean_object* v___y_585_, lean_object* v_x_586_){
_start:
{
uint8_t v_suppressElabErrors_boxed_587_; uint8_t v___y_9069__boxed_588_; uint8_t v_res_589_; lean_object* v_r_590_; 
v_suppressElabErrors_boxed_587_ = lean_unbox(v_suppressElabErrors_584_);
v___y_9069__boxed_588_ = lean_unbox(v___y_585_);
v_res_589_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(v_suppressElabErrors_boxed_587_, v___y_9069__boxed_588_, v_x_586_);
lean_dec(v_x_586_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_591_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_594_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_595_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
lean_ctor_set(v___x_597_, 2, v___x_596_);
lean_ctor_set(v___x_597_, 3, v___x_596_);
lean_ctor_set(v___x_597_, 4, v___x_595_);
lean_ctor_set(v___x_597_, 5, v___x_595_);
lean_ctor_set(v___x_597_, 6, v___x_595_);
lean_ctor_set(v___x_597_, 7, v___x_595_);
lean_ctor_set(v___x_597_, 8, v___x_595_);
lean_ctor_set(v___x_597_, 9, v___x_595_);
lean_ctor_set(v___x_597_, 10, v___x_595_);
lean_ctor_set(v___x_597_, 11, v___x_594_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_unsigned_to_nat(32u);
v___x_599_ = lean_mk_empty_array_with_capacity(v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = ((size_t)5ULL);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_unsigned_to_nat(32u);
v___x_604_ = lean_mk_empty_array_with_capacity(v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_606_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
lean_ctor_set(v___x_606_, 2, v___x_602_);
lean_ctor_set(v___x_606_, 3, v___x_602_);
lean_ctor_set_usize(v___x_606_, 4, v___x_601_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_607_ = lean_box(1);
v___x_608_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___x_607_);
return v___x_610_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; lean_object* v_env_615_; uint8_t v___x_616_; lean_object* v_env_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_scopes_620_; lean_object* v___x_621_; lean_object* v_opts_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_614_ = lean_st_ref_get(v___y_612_);
v_env_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_env_615_);
lean_dec(v___x_614_);
v___x_616_ = 0;
v_env_617_ = l_Lean_Environment_setRecordingDeps(v_env_615_, v___x_616_);
v___x_618_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_619_ = lean_st_ref_get(v___y_612_);
v_scopes_620_ = lean_ctor_get(v___x_619_, 2);
lean_inc(v_scopes_620_);
lean_dec(v___x_619_);
v___x_621_ = l_List_head_x21___redArg(v___x_618_, v_scopes_620_);
lean_dec(v_scopes_620_);
v_opts_622_ = lean_ctor_get(v___x_621_, 1);
lean_inc_ref(v_opts_622_);
lean_dec(v___x_621_);
v___x_623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__5);
v___x_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_625_, 0, v_env_617_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_ctor_set(v___x_625_, 3, v_opts_622_);
v___x_626_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_msgData_611_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_611_ = stack[0].m_obj;
lean_object* v___y_612_ = stack[1].m_obj;
lean_object* v_res_628_;
v_res_628_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_611_, v___y_612_);
stack->m_obj
 = v_res_628_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_629_, v___y_630_);
lean_dec(v___y_630_);
return v_res_632_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(lean_object* v_ref_633_, lean_object* v_msgData_634_, uint8_t v_severity_635_, uint8_t v_isSilent_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; uint8_t v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; uint8_t v___y_709_; lean_object* v___y_710_; uint8_t v___y_734_; uint8_t v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_738_; uint8_t v___y_742_; uint8_t v___y_743_; uint8_t v___y_744_; uint8_t v___x_759_; uint8_t v___y_761_; uint8_t v___y_762_; uint8_t v___y_763_; uint8_t v___y_765_; uint8_t v___x_777_; 
v___x_759_ = 2;
v___x_777_ = l_Lean_instBEqMessageSeverity_beq(v_severity_635_, v___x_759_);
if (v___x_777_ == 0)
{
v___y_765_ = v___x_777_;
goto v___jp_764_;
}
else
{
uint8_t v___x_778_; 
lean_inc_ref(v_msgData_634_);
v___x_778_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_634_);
v___y_765_ = v___x_778_;
goto v___jp_764_;
}
v___jp_640_:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Elab_Command_getScope___redArg(v___y_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v_currNamespace_651_; lean_object* v___x_652_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v_currNamespace_651_ = lean_ctor_get(v_a_650_, 2);
lean_inc(v_currNamespace_651_);
lean_dec(v_a_650_);
v___x_652_ = l_Lean_Elab_Command_getScope___redArg(v___y_648_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_688_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_688_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_688_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_688_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_openDecls_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_env_662_; lean_object* v_messages_663_; lean_object* v_scopes_664_; lean_object* v_usedQuotCtxts_665_; lean_object* v_nextMacroScope_666_; lean_object* v_maxRecDepth_667_; lean_object* v_ngen_668_; lean_object* v_auxDeclNGen_669_; lean_object* v_infoState_670_; lean_object* v_traceState_671_; lean_object* v_snapshotTasks_672_; lean_object* v_prevLinterStates_673_; lean_object* v_codeQualityEntryTasks_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_687_; 
v_openDecls_657_ = lean_ctor_get(v_a_653_, 3);
lean_inc(v_openDecls_657_);
lean_dec(v_a_653_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_currNamespace_651_);
lean_ctor_set(v___x_658_, 1, v_openDecls_657_);
v___x_659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___y_646_);
lean_inc_ref(v___y_642_);
lean_inc_ref(v___y_644_);
v___x_660_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_660_, 0, v___y_644_);
lean_ctor_set(v___x_660_, 1, v___y_641_);
lean_ctor_set(v___x_660_, 2, v___y_643_);
lean_ctor_set(v___x_660_, 3, v___y_642_);
lean_ctor_set(v___x_660_, 4, v___x_659_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*5, v___y_645_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*5 + 1, v___y_647_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*5 + 2, v_isSilent_636_);
v___x_661_ = lean_st_ref_take(v___y_648_);
v_env_662_ = lean_ctor_get(v___x_661_, 0);
v_messages_663_ = lean_ctor_get(v___x_661_, 1);
v_scopes_664_ = lean_ctor_get(v___x_661_, 2);
v_usedQuotCtxts_665_ = lean_ctor_get(v___x_661_, 3);
v_nextMacroScope_666_ = lean_ctor_get(v___x_661_, 4);
v_maxRecDepth_667_ = lean_ctor_get(v___x_661_, 5);
v_ngen_668_ = lean_ctor_get(v___x_661_, 6);
v_auxDeclNGen_669_ = lean_ctor_get(v___x_661_, 7);
v_infoState_670_ = lean_ctor_get(v___x_661_, 8);
v_traceState_671_ = lean_ctor_get(v___x_661_, 9);
v_snapshotTasks_672_ = lean_ctor_get(v___x_661_, 10);
v_prevLinterStates_673_ = lean_ctor_get(v___x_661_, 11);
v_codeQualityEntryTasks_674_ = lean_ctor_get(v___x_661_, 12);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_687_ == 0)
{
v___x_676_ = v___x_661_;
v_isShared_677_ = v_isSharedCheck_687_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_codeQualityEntryTasks_674_);
lean_inc(v_prevLinterStates_673_);
lean_inc(v_snapshotTasks_672_);
lean_inc(v_traceState_671_);
lean_inc(v_infoState_670_);
lean_inc(v_auxDeclNGen_669_);
lean_inc(v_ngen_668_);
lean_inc(v_maxRecDepth_667_);
lean_inc(v_nextMacroScope_666_);
lean_inc(v_usedQuotCtxts_665_);
lean_inc(v_scopes_664_);
lean_inc(v_messages_663_);
lean_inc(v_env_662_);
lean_dec(v___x_661_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_687_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_678_ = lean_box(0);
v___x_679_ = l_Lean_MessageLog_add(v___x_660_, v_messages_663_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___x_679_);
v___x_681_ = v___x_676_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_env_662_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_scopes_664_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_usedQuotCtxts_665_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_nextMacroScope_666_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_maxRecDepth_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_ngen_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v_auxDeclNGen_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_infoState_670_);
lean_ctor_set(v_reuseFailAlloc_686_, 9, v_traceState_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 10, v_snapshotTasks_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 11, v_prevLinterStates_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 12, v_codeQualityEntryTasks_674_);
v___x_681_ = v_reuseFailAlloc_686_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_st_ref_put(v___y_648_, v___x_681_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_678_);
v___x_684_ = v___x_655_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_678_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_currNamespace_651_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_641_);
v_a_689_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_652_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_652_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v___y_646_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_641_);
v_a_697_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_649_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_649_);
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
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
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
v___jp_705_:
{
lean_object* v_fileName_711_; lean_object* v_fileMap_712_; uint8_t v_suppressElabErrors_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_732_; 
v_fileName_711_ = lean_ctor_get(v___y_637_, 0);
v_fileMap_712_ = lean_ctor_get(v___y_637_, 1);
v_suppressElabErrors_713_ = lean_ctor_get_uint8(v___y_637_, sizeof(void*)*10);
v___x_714_ = lean_box(v_suppressElabErrors_713_);
v___x_715_ = lean_box(v___y_706_);
v___f_716_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_716_, 0, v___x_714_);
lean_closure_set(v___f_716_, 1, v___x_715_);
v___x_717_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_634_);
v___x_718_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v___x_717_, v___y_638_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_732_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc_ref_n(v_fileMap_712_, 2);
v___x_723_ = l_Lean_FileMap_toPosition(v_fileMap_712_, v___y_707_);
lean_dec(v___y_707_);
v___x_724_ = l_Lean_FileMap_toPosition(v_fileMap_712_, v___y_710_);
lean_dec(v___y_710_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__9));
if (v_suppressElabErrors_713_ == 0)
{
lean_del_object(v___x_721_);
lean_dec_ref(v___f_716_);
v___y_641_ = v___x_723_;
v___y_642_ = v___x_726_;
v___y_643_ = v___x_725_;
v___y_644_ = v_fileName_711_;
v___y_645_ = v___y_708_;
v___y_646_ = v_a_719_;
v___y_647_ = v___y_709_;
v___y_648_ = v___y_638_;
goto v___jp_640_;
}
else
{
uint8_t v___x_727_; 
lean_inc(v_a_719_);
v___x_727_ = l_Lean_MessageData_hasTag(v___f_716_, v_a_719_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_dec_ref_known(v___x_725_, 1);
lean_dec_ref(v___x_723_);
lean_dec(v_a_719_);
v___x_728_ = lean_box(0);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_728_);
v___x_730_ = v___x_721_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_del_object(v___x_721_);
v___y_641_ = v___x_723_;
v___y_642_ = v___x_726_;
v___y_643_ = v___x_725_;
v___y_644_ = v_fileName_711_;
v___y_645_ = v___y_708_;
v___y_646_ = v_a_719_;
v___y_647_ = v___y_709_;
v___y_648_ = v___y_638_;
goto v___jp_640_;
}
}
}
}
v___jp_733_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Syntax_getTailPos_x3f(v___y_736_, v___y_735_);
lean_dec(v___y_736_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_inc(v___y_738_);
v___y_706_ = v___y_734_;
v___y_707_ = v___y_738_;
v___y_708_ = v___y_735_;
v___y_709_ = v___y_737_;
v___y_710_ = v___y_738_;
goto v___jp_705_;
}
else
{
lean_object* v_val_740_; 
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_739_, 1);
v___y_706_ = v___y_734_;
v___y_707_ = v___y_738_;
v___y_708_ = v___y_735_;
v___y_709_ = v___y_737_;
v___y_710_ = v_val_740_;
goto v___jp_705_;
}
}
v___jp_741_:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Elab_Command_getRef___redArg(v___y_637_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_ref_747_; lean_object* v___x_748_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v_ref_747_ = l_Lean_replaceRef(v_ref_633_, v_a_746_);
lean_dec(v_a_746_);
v___x_748_ = l_Lean_Syntax_getPos_x3f(v_ref_747_, v___y_743_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___y_734_ = v___y_742_;
v___y_735_ = v___y_743_;
v___y_736_ = v_ref_747_;
v___y_737_ = v___y_744_;
v___y_738_ = v___x_749_;
goto v___jp_733_;
}
else
{
lean_object* v_val_750_; 
v_val_750_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v___x_748_, 1);
v___y_734_ = v___y_742_;
v___y_735_ = v___y_743_;
v___y_736_ = v_ref_747_;
v___y_737_ = v___y_744_;
v___y_738_ = v_val_750_;
goto v___jp_733_;
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_msgData_634_);
v_a_751_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_745_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_745_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
v___jp_760_:
{
if (v___y_763_ == 0)
{
v___y_742_ = v___y_761_;
v___y_743_ = v___y_762_;
v___y_744_ = v_severity_635_;
goto v___jp_741_;
}
else
{
v___y_742_ = v___y_761_;
v___y_743_ = v___y_762_;
v___y_744_ = v___x_759_;
goto v___jp_741_;
}
}
v___jp_764_:
{
if (v___y_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_scopes_768_; lean_object* v___x_769_; lean_object* v_opts_770_; uint8_t v___x_771_; uint8_t v___x_772_; 
v___x_766_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_767_ = lean_st_ref_get(v___y_638_);
v_scopes_768_ = lean_ctor_get(v___x_767_, 2);
lean_inc(v_scopes_768_);
lean_dec(v___x_767_);
v___x_769_ = l_List_head_x21___redArg(v___x_766_, v_scopes_768_);
lean_dec(v_scopes_768_);
v_opts_770_ = lean_ctor_get(v___x_769_, 1);
lean_inc_ref(v_opts_770_);
lean_dec(v___x_769_);
v___x_771_ = 1;
v___x_772_ = l_Lean_instBEqMessageSeverity_beq(v_severity_635_, v___x_771_);
if (v___x_772_ == 0)
{
lean_dec_ref(v_opts_770_);
v___y_761_ = v___y_765_;
v___y_762_ = v___y_765_;
v___y_763_ = v___x_772_;
goto v___jp_760_;
}
else
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = l_Lean_warningAsError;
v___x_774_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_770_, v___x_773_);
lean_dec_ref(v_opts_770_);
v___y_761_ = v___y_765_;
v___y_762_ = v___y_765_;
v___y_763_ = v___x_774_;
goto v___jp_760_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v_msgData_634_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_633_ = stack[0].m_obj;
lean_object* v_msgData_634_ = stack[1].m_obj;
uint8_t v_severity_635_ = stack[2].m_num;
uint8_t v_isSilent_636_ = stack[3].m_num;
lean_object* v___y_637_ = stack[4].m_obj;
lean_object* v___y_638_ = stack[5].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_633_, v_msgData_634_, v_severity_635_, v_isSilent_636_, v___y_637_, v___y_638_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(lean_object* v_ref_780_, lean_object* v_msgData_781_, lean_object* v_severity_782_, lean_object* v_isSilent_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v_severity_boxed_787_; uint8_t v_isSilent_boxed_788_; lean_object* v_res_789_; 
v_severity_boxed_787_ = lean_unbox(v_severity_782_);
v_isSilent_boxed_788_ = lean_unbox(v_isSilent_783_);
v_res_789_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_780_, v_msgData_781_, v_severity_boxed_787_, v_isSilent_boxed_788_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v_ref_780_);
return v_res_789_;
}
}
lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(lean_object* v_ref_790_, lean_object* v_msgData_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = 1;
v___x_796_ = 0;
v___x_797_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_790_, v_msgData_791_, v___x_795_, v___x_796_, v___y_792_, v___y_793_);
return v___x_797_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_790_ = stack[0].m_obj;
lean_object* v_msgData_791_ = stack[1].m_obj;
lean_object* v___y_792_ = stack[2].m_obj;
lean_object* v___y_793_ = stack[3].m_obj;
lean_object* v_res_798_;
v_res_798_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v_ref_790_, v_msgData_791_, v___y_792_, v___y_793_);
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(lean_object* v_ref_799_, lean_object* v_msgData_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v_ref_799_, v_msgData_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_ref_799_);
return v_res_804_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(lean_object* v_t_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; lean_object* v_infoState_809_; uint8_t v_enabled_810_; 
v___x_808_ = lean_st_ref_get(v___y_806_);
v_infoState_809_ = lean_ctor_get(v___x_808_, 8);
lean_inc_ref(v_infoState_809_);
lean_dec(v___x_808_);
v_enabled_810_ = lean_ctor_get_uint8(v_infoState_809_, sizeof(void*)*3);
lean_dec_ref(v_infoState_809_);
if (v_enabled_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref(v_t_805_);
v___x_811_ = lean_box(0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v_infoState_814_; lean_object* v_env_815_; lean_object* v_messages_816_; lean_object* v_scopes_817_; lean_object* v_usedQuotCtxts_818_; lean_object* v_nextMacroScope_819_; lean_object* v_maxRecDepth_820_; lean_object* v_ngen_821_; lean_object* v_auxDeclNGen_822_; lean_object* v_traceState_823_; lean_object* v_snapshotTasks_824_; lean_object* v_prevLinterStates_825_; lean_object* v_codeQualityEntryTasks_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_848_; 
v___x_813_ = lean_st_ref_take(v___y_806_);
v_infoState_814_ = lean_ctor_get(v___x_813_, 8);
v_env_815_ = lean_ctor_get(v___x_813_, 0);
v_messages_816_ = lean_ctor_get(v___x_813_, 1);
v_scopes_817_ = lean_ctor_get(v___x_813_, 2);
v_usedQuotCtxts_818_ = lean_ctor_get(v___x_813_, 3);
v_nextMacroScope_819_ = lean_ctor_get(v___x_813_, 4);
v_maxRecDepth_820_ = lean_ctor_get(v___x_813_, 5);
v_ngen_821_ = lean_ctor_get(v___x_813_, 6);
v_auxDeclNGen_822_ = lean_ctor_get(v___x_813_, 7);
v_traceState_823_ = lean_ctor_get(v___x_813_, 9);
v_snapshotTasks_824_ = lean_ctor_get(v___x_813_, 10);
v_prevLinterStates_825_ = lean_ctor_get(v___x_813_, 11);
v_codeQualityEntryTasks_826_ = lean_ctor_get(v___x_813_, 12);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_848_ == 0)
{
v___x_828_ = v___x_813_;
v_isShared_829_ = v_isSharedCheck_848_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_codeQualityEntryTasks_826_);
lean_inc(v_prevLinterStates_825_);
lean_inc(v_snapshotTasks_824_);
lean_inc(v_traceState_823_);
lean_inc(v_infoState_814_);
lean_inc(v_auxDeclNGen_822_);
lean_inc(v_ngen_821_);
lean_inc(v_maxRecDepth_820_);
lean_inc(v_nextMacroScope_819_);
lean_inc(v_usedQuotCtxts_818_);
lean_inc(v_scopes_817_);
lean_inc(v_messages_816_);
lean_inc(v_env_815_);
lean_dec(v___x_813_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_848_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v_enabled_830_; lean_object* v_assignment_831_; lean_object* v_lazyAssignment_832_; lean_object* v_trees_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_847_; 
v_enabled_830_ = lean_ctor_get_uint8(v_infoState_814_, sizeof(void*)*3);
v_assignment_831_ = lean_ctor_get(v_infoState_814_, 0);
v_lazyAssignment_832_ = lean_ctor_get(v_infoState_814_, 1);
v_trees_833_ = lean_ctor_get(v_infoState_814_, 2);
v_isSharedCheck_847_ = !lean_is_exclusive(v_infoState_814_);
if (v_isSharedCheck_847_ == 0)
{
v___x_835_ = v_infoState_814_;
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_trees_833_);
lean_inc(v_lazyAssignment_832_);
lean_inc(v_assignment_831_);
lean_dec(v_infoState_814_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_847_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = lean_box(0);
v___x_838_ = l_Lean_PersistentArray_push___redArg(v_trees_833_, v_t_805_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 2, v___x_838_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_assignment_831_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_lazyAssignment_832_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v___x_838_);
lean_ctor_set_uint8(v_reuseFailAlloc_846_, sizeof(void*)*3, v_enabled_830_);
v___x_840_ = v_reuseFailAlloc_846_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 8, v___x_840_);
v___x_842_ = v___x_828_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_env_815_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_messages_816_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_scopes_817_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_usedQuotCtxts_818_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_nextMacroScope_819_);
lean_ctor_set(v_reuseFailAlloc_845_, 5, v_maxRecDepth_820_);
lean_ctor_set(v_reuseFailAlloc_845_, 6, v_ngen_821_);
lean_ctor_set(v_reuseFailAlloc_845_, 7, v_auxDeclNGen_822_);
lean_ctor_set(v_reuseFailAlloc_845_, 8, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_845_, 9, v_traceState_823_);
lean_ctor_set(v_reuseFailAlloc_845_, 10, v_snapshotTasks_824_);
lean_ctor_set(v_reuseFailAlloc_845_, 11, v_prevLinterStates_825_);
lean_ctor_set(v_reuseFailAlloc_845_, 12, v_codeQualityEntryTasks_826_);
v___x_842_ = v_reuseFailAlloc_845_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_st_ref_put(v___y_806_, v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_837_);
return v___x_844_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_805_ = stack[0].m_obj;
lean_object* v___y_806_ = stack[1].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_805_, v___y_806_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_t_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_850_, v___y_851_);
lean_dec(v___y_851_);
return v_res_853_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_unsigned_to_nat(32u);
v___x_855_ = lean_mk_empty_array_with_capacity(v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_857_ = ((size_t)5ULL);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_unsigned_to_nat(32u);
v___x_860_ = lean_mk_empty_array_with_capacity(v___x_859_);
v___x_861_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0);
v___x_862_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
lean_ctor_set(v___x_862_, 2, v___x_858_);
lean_ctor_set(v___x_862_, 3, v___x_858_);
lean_ctor_set_usize(v___x_862_, 4, v___x_857_);
return v___x_862_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(lean_object* v_t_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_infoState_868_; uint8_t v_enabled_869_; 
v___x_867_ = lean_st_ref_get(v___y_865_);
v_infoState_868_ = lean_ctor_get(v___x_867_, 8);
lean_inc_ref(v_infoState_868_);
lean_dec(v___x_867_);
v_enabled_869_ = lean_ctor_get_uint8(v_infoState_868_, sizeof(void*)*3);
lean_dec_ref(v_infoState_868_);
if (v_enabled_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref(v_t_863_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1);
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v_t_863_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v___x_873_, v___y_865_);
return v___x_874_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_863_ = stack[0].m_obj;
lean_object* v___y_864_ = stack[1].m_obj;
lean_object* v___y_865_ = stack[2].m_obj;
lean_object* v_res_875_;
v_res_875_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v_t_863_, v___y_864_, v___y_865_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(lean_object* v_t_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v_t_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_880_;
}
}
lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(lean_object* v_info_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_885_, 0, v_info_881_);
v___x_886_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v___x_885_, v___y_882_, v___y_883_);
return v___x_886_;
}
}
LEAN_EXPORT void l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_881_ = stack[0].m_obj;
lean_object* v___y_882_ = stack[1].m_obj;
lean_object* v___y_883_ = stack[2].m_obj;
lean_object* v_res_887_;
v_res_887_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v_info_881_, v___y_882_, v___y_883_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(lean_object* v_info_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v_info_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_892_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_box(1);
v___x_894_ = l_Lean_MessageData_ofFormat(v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2));
v___x_899_ = l_Lean_MessageData_ofFormat(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
return v_x_900_;
}
else
{
lean_object* v_head_902_; lean_object* v_tail_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_925_; 
v_head_902_ = lean_ctor_get(v_x_901_, 0);
v_tail_903_ = lean_ctor_get(v_x_901_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_925_ == 0)
{
v___x_905_ = v_x_901_;
v_isShared_906_ = v_isSharedCheck_925_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_tail_903_);
lean_inc(v_head_902_);
lean_dec(v_x_901_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_925_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_before_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_923_; 
v_before_907_ = lean_ctor_get(v_head_902_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_head_902_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_head_902_, 1);
lean_dec(v_unused_924_);
v___x_909_ = v_head_902_;
v_isShared_910_ = v_isSharedCheck_923_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_before_907_);
lean_dec(v_head_902_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_923_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 7);
lean_ctor_set(v___x_909_, 1, v___x_911_);
lean_ctor_set(v___x_909_, 0, v_x_900_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_x_900_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_922_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3);
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 7);
lean_ctor_set(v___x_905_, 1, v___x_914_);
lean_ctor_set(v___x_905_, 0, v___x_913_);
v___x_916_ = v___x_905_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___x_914_);
v___x_916_ = v_reuseFailAlloc_921_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = l_Lean_MessageData_ofSyntax(v_before_907_);
v___x_918_ = l_Lean_indentD(v___x_917_);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v_x_900_ = v___x_919_;
v_x_901_ = v_tail_903_;
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
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_930_ = l_Lean_MessageData_ofFormat(v___x_929_);
return v___x_930_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_931_, lean_object* v_macroStack_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_scopes_937_; lean_object* v___x_938_; lean_object* v_opts_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_935_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_936_ = lean_st_ref_get(v___y_933_);
v_scopes_937_ = lean_ctor_get(v___x_936_, 2);
lean_inc(v_scopes_937_);
lean_dec(v___x_936_);
v___x_938_ = l_List_head_x21___redArg(v___x_935_, v_scopes_937_);
lean_dec(v_scopes_937_);
v_opts_939_ = lean_ctor_get(v___x_938_, 1);
lean_inc_ref(v_opts_939_);
lean_dec(v___x_938_);
v___x_940_ = l_Lean_Elab_pp_macroStack;
v___x_941_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_939_, v___x_940_);
lean_dec_ref(v_opts_939_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec(v_macroStack_932_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_msgData_931_);
return v___x_942_;
}
else
{
if (lean_obj_tag(v_macroStack_932_) == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_msgData_931_);
return v___x_943_;
}
else
{
lean_object* v_head_944_; lean_object* v_after_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_960_; 
v_head_944_ = lean_ctor_get(v_macroStack_932_, 0);
lean_inc(v_head_944_);
v_after_945_ = lean_ctor_get(v_head_944_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_head_944_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v_head_944_, 0);
lean_dec(v_unused_961_);
v___x_947_ = v_head_944_;
v_isShared_948_ = v_isSharedCheck_960_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_after_945_);
lean_dec(v_head_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_960_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 7);
lean_ctor_set(v___x_947_, 1, v___x_949_);
lean_ctor_set(v___x_947_, 0, v_msgData_931_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_msgData_931_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_959_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_msgData_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_952_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Lean_MessageData_ofSyntax(v_after_945_);
v___x_955_ = l_Lean_indentD(v___x_954_);
v_msgData_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_956_, 0, v___x_953_);
lean_ctor_set(v_msgData_956_, 1, v___x_955_);
v___x_957_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(v_msgData_956_, v_macroStack_932_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_931_ = stack[0].m_obj;
lean_object* v_macroStack_932_ = stack[1].m_obj;
lean_object* v___y_933_ = stack[2].m_obj;
lean_object* v_res_962_;
v_res_962_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_931_, v_macroStack_932_, v___y_933_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_963_, lean_object* v_macroStack_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_963_, v_macroStack_964_, v___y_965_);
lean_dec(v___y_965_);
return v_res_967_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Elab_Command_getRef___redArg(v___y_969_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v_macroStack_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___x_978_; lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v_macroStack_974_ = lean_ctor_get(v___y_969_, 4);
v___x_975_ = l_Lean_Elab_getBetterRef(v_a_973_, v_macroStack_974_);
lean_dec(v_a_973_);
v___x_976_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msg_968_, v___y_970_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref(v___x_976_);
lean_inc(v_macroStack_974_);
v___x_978_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_a_977_, v_macroStack_974_, v___y_970_);
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_975_);
lean_ctor_set(v___x_983_, 1, v_a_979_);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 1);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_msg_968_);
v_a_988_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_972_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_972_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_968_ = stack[0].m_obj;
lean_object* v___y_969_ = stack[1].m_obj;
lean_object* v___y_970_ = stack[2].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_968_, v___y_969_, v___y_970_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1001_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(lean_object* v_ref_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Elab_Command_getRef___redArg(v___y_1004_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v_fileName_1009_; lean_object* v_fileMap_1010_; lean_object* v_currRecDepth_1011_; lean_object* v_cmdPos_1012_; lean_object* v_macroStack_1013_; lean_object* v_quotContext_x3f_1014_; lean_object* v_currMacroScope_1015_; lean_object* v_snap_x3f_1016_; lean_object* v_cancelTk_x3f_1017_; uint8_t v_suppressElabErrors_1018_; lean_object* v_ref_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v_fileName_1009_ = lean_ctor_get(v___y_1004_, 0);
v_fileMap_1010_ = lean_ctor_get(v___y_1004_, 1);
v_currRecDepth_1011_ = lean_ctor_get(v___y_1004_, 2);
v_cmdPos_1012_ = lean_ctor_get(v___y_1004_, 3);
v_macroStack_1013_ = lean_ctor_get(v___y_1004_, 4);
v_quotContext_x3f_1014_ = lean_ctor_get(v___y_1004_, 5);
v_currMacroScope_1015_ = lean_ctor_get(v___y_1004_, 6);
v_snap_x3f_1016_ = lean_ctor_get(v___y_1004_, 8);
v_cancelTk_x3f_1017_ = lean_ctor_get(v___y_1004_, 9);
v_suppressElabErrors_1018_ = lean_ctor_get_uint8(v___y_1004_, sizeof(void*)*10);
v_ref_1019_ = l_Lean_replaceRef(v_ref_1002_, v_a_1008_);
lean_dec(v_a_1008_);
lean_inc(v_cancelTk_x3f_1017_);
lean_inc(v_snap_x3f_1016_);
lean_inc(v_currMacroScope_1015_);
lean_inc(v_quotContext_x3f_1014_);
lean_inc(v_macroStack_1013_);
lean_inc(v_cmdPos_1012_);
lean_inc(v_currRecDepth_1011_);
lean_inc_ref(v_fileMap_1010_);
lean_inc_ref(v_fileName_1009_);
v___x_1020_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1020_, 0, v_fileName_1009_);
lean_ctor_set(v___x_1020_, 1, v_fileMap_1010_);
lean_ctor_set(v___x_1020_, 2, v_currRecDepth_1011_);
lean_ctor_set(v___x_1020_, 3, v_cmdPos_1012_);
lean_ctor_set(v___x_1020_, 4, v_macroStack_1013_);
lean_ctor_set(v___x_1020_, 5, v_quotContext_x3f_1014_);
lean_ctor_set(v___x_1020_, 6, v_currMacroScope_1015_);
lean_ctor_set(v___x_1020_, 7, v_ref_1019_);
lean_ctor_set(v___x_1020_, 8, v_snap_x3f_1016_);
lean_ctor_set(v___x_1020_, 9, v_cancelTk_x3f_1017_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*10, v_suppressElabErrors_1018_);
v___x_1021_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_1003_, v___x_1020_, v___y_1005_);
lean_dec_ref_known(v___x_1020_, 10);
return v___x_1021_;
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_msg_1003_);
v_a_1022_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1007_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1007_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1002_ = stack[0].m_obj;
lean_object* v_msg_1003_ = stack[1].m_obj;
lean_object* v___y_1004_ = stack[2].m_obj;
lean_object* v___y_1005_ = stack[3].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1002_, v_msg_1003_, v___y_1004_, v___y_1005_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(lean_object* v_ref_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1031_, v_msg_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v_ref_1031_);
return v_res_1036_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_box(1);
v___x_1043_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_1044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2);
v___x_1045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1043_);
lean_ctor_set(v___x_1045_, 2, v___x_1042_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(lean_object* v_tyName_1067_, lean_object* v_infos_1068_, lean_object* v_as_1069_, size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_b_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_a_1077_; uint8_t v___x_1081_; 
v___x_1081_ = lean_usize_dec_lt(v_i_1071_, v_sz_1070_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v_tyName_1067_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_b_1072_);
return v___x_1082_;
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_a_1083_ = lean_array_uget_borrowed(v_as_1069_, v_i_1071_);
v___x_1084_ = ((lean_object*)(l_Lake_DSL_declField___closed__1));
lean_inc(v_a_1083_);
v___x_1085_ = l_Lean_Syntax_isOfKind(v_a_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1);
v___x_1087_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_a_1083_, v___x_1086_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_dec_ref_known(v___x_1087_, 1);
v_a_1077_ = v_b_1072_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_b_1072_);
lean_dec(v_tyName_1067_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = l_Lean_Syntax_getArg(v_a_1083_, v___x_1096_);
v___x_1098_ = lean_unsigned_to_nat(2u);
v___x_1099_ = l_Lean_Syntax_getArg(v_a_1083_, v___x_1098_);
v___x_1100_ = l_Lean_TSyntax_getId(v___x_1097_);
lean_inc(v___x_1100_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3);
lean_inc(v_tyName_1067_);
lean_inc(v_a_1083_);
v___x_1103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1103_, 0, v_a_1083_);
lean_ctor_set(v___x_1103_, 1, v___x_1101_);
lean_ctor_set(v___x_1103_, 2, v___x_1102_);
lean_ctor_set(v___x_1103_, 3, v_tyName_1067_);
v___x_1104_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v___x_1103_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1105_; 
lean_dec_ref_known(v___x_1104_, 1);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_infos_1068_, v___x_1100_);
if (lean_obj_tag(v___x_1105_) == 1)
{
lean_object* v_val_1106_; lean_object* v_realName_1107_; uint8_t v_canonical_1108_; 
v_val_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_realName_1107_ = lean_ctor_get(v_val_1106_, 1);
lean_inc(v_realName_1107_);
v_canonical_1108_ = lean_ctor_get_uint8(v_val_1106_, sizeof(void*)*2);
lean_dec(v_val_1106_);
if (v_canonical_1108_ == 0)
{
if (v___x_1085_ == 0)
{
lean_dec(v___x_1100_);
goto v___jp_1109_;
}
else
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_realName_1107_, v_b_1072_);
if (v___x_1112_ == 0)
{
lean_dec(v___x_1100_);
goto v___jp_1109_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1113_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5);
lean_inc(v_realName_1107_);
v___x_1114_ = l_Lean_MessageData_ofName(v_realName_1107_);
lean_inc_ref(v___x_1114_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_MessageData_ofName(v___x_1100_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v___x_1114_);
v___x_1123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1097_, v___x_1124_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_dec_ref_known(v___x_1125_, 1);
goto v___jp_1109_;
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_realName_1107_);
lean_dec(v___x_1099_);
lean_dec(v___x_1097_);
lean_dec(v_b_1072_);
lean_dec(v_tyName_1067_);
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
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
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
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
}
}
else
{
lean_dec(v___x_1100_);
goto v___jp_1109_;
}
v___jp_1109_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1097_);
lean_ctor_set(v___x_1110_, 1, v___x_1099_);
v___x_1111_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_realName_1107_, v___x_1110_, v_b_1072_);
v_a_1077_ = v___x_1111_;
goto v___jp_1076_;
}
}
else
{
lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v___x_1105_);
lean_dec(v___x_1099_);
v___x_1134_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13);
v___x_1135_ = 0;
lean_inc(v_tyName_1067_);
v___x_1136_ = l_Lean_MessageData_ofConstName(v_tyName_1067_, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1134_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_MessageData_ofName(v___x_1100_);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1097_, v___x_1143_, v___y_1073_, v___y_1074_);
lean_dec(v___x_1097_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_dec_ref_known(v___x_1144_, 1);
v_a_1077_ = v_b_1072_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_b_1072_);
lean_dec(v_tyName_1067_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v___x_1100_);
lean_dec(v___x_1099_);
lean_dec(v___x_1097_);
lean_dec(v_b_1072_);
lean_dec(v_tyName_1067_);
v_a_1153_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1104_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1104_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
v___jp_1076_:
{
size_t v___x_1078_; size_t v___x_1079_; 
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = lean_usize_add(v_i_1071_, v___x_1078_);
v_i_1071_ = v___x_1079_;
v_b_1072_ = v_a_1077_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_tyName_1067_ = stack[0].m_obj;
lean_object* v_infos_1068_ = stack[1].m_obj;
lean_object* v_as_1069_ = stack[2].m_obj;
size_t v_sz_1070_ = stack[3].m_num;
size_t v_i_1071_ = stack[4].m_num;
lean_object* v_b_1072_ = stack[5].m_obj;
lean_object* v___y_1073_ = stack[6].m_obj;
lean_object* v___y_1074_ = stack[7].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1067_, v_infos_1068_, v_as_1069_, v_sz_1070_, v_i_1071_, v_b_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(lean_object* v_tyName_1162_, lean_object* v_infos_1163_, lean_object* v_as_1164_, lean_object* v_sz_1165_, lean_object* v_i_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
size_t v_sz_boxed_1171_; size_t v_i_boxed_1172_; lean_object* v_res_1173_; 
v_sz_boxed_1171_ = lean_unbox_usize(v_sz_1165_);
lean_dec(v_sz_1165_);
v_i_boxed_1172_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1162_, v_infos_1163_, v_as_1164_, v_sz_boxed_1171_, v_i_boxed_1172_, v_b_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec_ref(v_as_1164_);
lean_dec(v_infos_1163_);
return v_res_1173_;
}
}
lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object* v_tyName_1185_, lean_object* v_infos_1186_, lean_object* v_fs_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_m_1191_; size_t v_sz_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v_m_1191_ = lean_box(1);
v_sz_1192_ = lean_array_size(v_fs_1187_);
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1185_, v_infos_1186_, v_fs_1187_, v_sz_1192_, v___x_1193_, v_m_1191_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1213_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1197_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v___x_1196_, v_a_1195_);
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1213_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1213_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1202_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
v___x_1203_ = lean_box(2);
v___x_1204_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2));
v___x_1205_ = l_Lean_Syntax_mkSep(v_a_1198_, v___x_1204_);
lean_dec(v_a_1198_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_mk_empty_array_with_capacity(v___x_1206_);
v___x_1208_ = lean_array_push(v___x_1207_, v___x_1205_);
v___x_1209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1203_);
lean_ctor_set(v___x_1209_, 1, v___x_1202_);
lean_ctor_set(v___x_1209_, 2, v___x_1208_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1209_);
v___x_1211_ = v___x_1200_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1214_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1194_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1194_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_tyName_1185_ = stack[0].m_obj;
lean_object* v_infos_1186_ = stack[1].m_obj;
lean_object* v_fs_1187_ = stack[2].m_obj;
lean_object* v_a_1188_ = stack[3].m_obj;
lean_object* v_a_1189_ = stack[4].m_obj;
lean_object* v_res_1222_;
v_res_1222_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1185_, v_infos_1186_, v_fs_1187_, v_a_1188_, v_a_1189_);
stack->m_obj
 = v_res_1222_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(lean_object* v_tyName_1223_, lean_object* v_infos_1224_, lean_object* v_fs_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1223_, v_infos_1224_, v_fs_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_fs_1225_);
lean_dec(v_infos_1224_);
return v_res_1229_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_object* v_00_u03b1_1230_, lean_object* v_ref_1231_, lean_object* v_msg_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1231_, v_msg_1232_, v___y_1233_, v___y_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1231_ = stack[1].m_obj;
lean_object* v_msg_1232_ = stack[2].m_obj;
lean_object* v___y_1233_ = stack[3].m_obj;
lean_object* v___y_1234_ = stack[4].m_obj;
lean_object* v_res_1237_;
v_res_1237_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_box(0), v_ref_1231_, v_msg_1232_, v___y_1233_, v___y_1234_);
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_ref_1239_, lean_object* v_msg_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(v_00_u03b1_1238_, v_ref_1239_, v_msg_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v_ref_1239_);
return v_res_1244_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(lean_object* v_init_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_1245_, v_x_1246_);
return v___x_1250_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1245_ = stack[0].m_obj;
lean_object* v_x_1246_ = stack[1].m_obj;
lean_object* v___y_1247_ = stack[2].m_obj;
lean_object* v___y_1248_ = stack[3].m_obj;
lean_object* v_res_1251_;
v_res_1251_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(v_init_1245_, v_x_1246_, v___y_1247_, v___y_1248_);
stack->m_obj
 = v_res_1251_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(lean_object* v_init_1252_, lean_object* v_x_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(v_init_1252_, v_x_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(lean_object* v_msgData_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_1258_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1258_ = stack[0].m_obj;
lean_object* v___y_1259_ = stack[1].m_obj;
lean_object* v___y_1260_ = stack[2].m_obj;
lean_object* v_res_1263_;
v_res_1263_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(v_msgData_1258_, v___y_1259_, v___y_1260_);
stack->m_obj
 = v_res_1263_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(v_msgData_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1268_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_object* v_00_u03b1_1269_, lean_object* v_msg_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1270_ = stack[1].m_obj;
lean_object* v___y_1271_ = stack[2].m_obj;
lean_object* v___y_1272_ = stack[3].m_obj;
lean_object* v_res_1275_;
v_res_1275_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_box(0), v_msg_1270_, v___y_1271_, v___y_1272_);
stack->m_obj
 = v_res_1275_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(v_00_u03b1_1276_, v_msg_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1281_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(lean_object* v_t_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_1282_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1282_ = stack[0].m_obj;
lean_object* v___y_1283_ = stack[1].m_obj;
lean_object* v___y_1284_ = stack[2].m_obj;
lean_object* v_res_1287_;
v_res_1287_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(v_t_1282_, v___y_1283_, v___y_1284_);
stack->m_obj
 = v_res_1287_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(lean_object* v_t_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(v_t_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1292_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(lean_object* v_msgData_1293_, lean_object* v_macroStack_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_1293_, v_macroStack_1294_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1293_ = stack[0].m_obj;
lean_object* v_macroStack_1294_ = stack[1].m_obj;
lean_object* v___y_1295_ = stack[2].m_obj;
lean_object* v___y_1296_ = stack[3].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(v_msgData_1293_, v_macroStack_1294_, v___y_1295_, v___y_1296_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1300_, lean_object* v_macroStack_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(v_msgData_1300_, v_macroStack_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1305_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_env_1309_; lean_object* v___x_1310_; lean_object* v_mainModule_1311_; lean_object* v___x_1312_; 
v___x_1308_ = lean_st_ref_get(v___y_1306_);
v_env_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_env_1309_);
lean_dec(v___x_1308_);
v___x_1310_ = l_Lean_Environment_header(v_env_1309_);
lean_dec_ref(v_env_1309_);
v_mainModule_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_mainModule_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_mainModule_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1306_ = stack[0].m_obj;
lean_object* v_res_1313_;
v_res_1313_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1306_);
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1314_);
lean_dec(v___y_1314_);
return v_res_1316_;
}
}
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object* v___x_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_a_1322_; lean_object* v_quotContext_x3f_1341_; 
v_quotContext_x3f_1341_ = lean_ctor_get(v___y_1318_, 5);
if (lean_obj_tag(v_quotContext_x3f_1341_) == 0)
{
lean_object* v___x_1342_; lean_object* v_a_1343_; 
v___x_1342_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1319_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v___x_1342_);
v_a_1322_ = v_a_1343_;
goto v___jp_1321_;
}
else
{
lean_object* v_val_1344_; 
v_val_1344_ = lean_ctor_get(v_quotContext_x3f_1341_, 0);
lean_inc(v_val_1344_);
v_a_1322_ = v_val_1344_;
goto v___jp_1321_;
}
v___jp_1321_:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1318_);
lean_dec_ref(v___y_1318_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = l_Lean_addMacroScope(v_a_1322_, v___x_1317_, v_a_1324_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1322_);
lean_dec(v___x_1317_);
v_a_1333_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1323_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1323_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1317_ = stack[0].m_obj;
lean_object* v___y_1318_ = stack[1].m_obj;
lean_object* v___y_1319_ = stack[2].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(v___x_1317_, v___y_1318_, v___y_1319_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object* v___x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(v___x_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
return v_res_1350_;
}
}
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___f_1359_; lean_object* v___x_1360_; 
v___f_1359_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2));
v___x_1360_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___f_1359_, v___y_1356_, v___y_1357_);
return v___x_1360_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1356_ = stack[0].m_obj;
lean_object* v___y_1357_ = stack[1].m_obj;
lean_object* v_res_1361_;
v_res_1361_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1356_, v___y_1357_);
stack->m_obj
 = v_res_1361_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1365_;
}
}
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(lean_object* v_ref_1366_, uint8_t v_canonical_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = l_Lean_mkIdentFrom(v_ref_1366_, v_a_1372_, v_canonical_1367_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1371_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1371_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1366_ = stack[0].m_obj;
uint8_t v_canonical_1367_ = stack[1].m_num;
lean_object* v___y_1368_ = stack[2].m_obj;
lean_object* v___y_1369_ = stack[3].m_obj;
lean_object* v_res_1389_;
v_res_1389_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_ref_1366_, v_canonical_1367_, v___y_1368_, v___y_1369_);
stack->m_obj
 = v_res_1389_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object* v_ref_1390_, lean_object* v_canonical_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_canonical_boxed_1395_; lean_object* v_res_1396_; 
v_canonical_boxed_1395_ = lean_unbox(v_canonical_1391_);
v_res_1396_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_ref_1390_, v_canonical_boxed_1395_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_ref_1390_);
return v_res_1396_;
}
}
lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object* v_stx_x3f_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
if (lean_obj_tag(v_stx_x3f_1397_) == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Elab_Command_getRef___redArg(v_a_1398_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = 0;
v___x_1404_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_a_1402_, v___x_1403_, v_a_1398_, v_a_1399_);
lean_dec(v_a_1402_);
return v___x_1404_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1401_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1401_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_val_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_val_1413_ = lean_ctor_get(v_stx_x3f_1397_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_stx_x3f_1397_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1415_ = v_stx_x3f_1397_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_val_1413_);
lean_dec(v_stx_x3f_1397_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = l_Lake_DSL_expandIdentOrStrAsIdent(v_val_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_DSL_mkConfigDeclIdent_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_x3f_1397_ = stack[0].m_obj;
lean_object* v_a_1398_ = stack[1].m_obj;
lean_object* v_a_1399_ = stack[2].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_Lake_DSL_mkConfigDeclIdent(v_stx_x3f_1397_, v_a_1398_, v_a_1399_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object* v_stx_x3f_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lake_DSL_mkConfigDeclIdent(v_stx_x3f_1423_, v_a_1424_, v_a_1425_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
return v_res_1427_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1428_ = stack[0].m_obj;
lean_object* v___y_1429_ = stack[1].m_obj;
lean_object* v_res_1432_;
v_res_1432_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(v___y_1428_, v___y_1429_);
stack->m_obj
 = v_res_1432_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1436_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__6(void){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_instMonadEIO___redArg();
return v___x_1443_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__7(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__6, &l_Lake_DSL_elabConfig___closed__6_once, _init_l_Lake_DSL_elabConfig___closed__6);
v___x_1445_ = l_StateRefT_x27_instMonad___redArg(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__13(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1455_ = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
v___x_1456_ = l_Lean_Elab_Command_instMonadRefCommandElabM;
v___x_1457_ = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
v___x_1458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v___x_1456_);
lean_ctor_set(v___x_1458_, 2, v___x_1455_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__15(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__14));
v___x_1461_ = l_Lean_stringToMessageData(v___x_1460_);
return v___x_1461_;
}
}
lean_object* l_Lake_DSL_elabConfig(lean_object* v_tyName_1462_, lean_object* v_info_1463_, lean_object* v_id_1464_, lean_object* v_ty_1465_, lean_object* v_config_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_whereInfo_1582_; lean_object* v_fs_1583_; lean_object* v_wds_x3f_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___x_1613_; lean_object* v_toApplicative_1614_; lean_object* v_toFunctor_1615_; lean_object* v_toSeq_1616_; lean_object* v_toSeqLeft_1617_; lean_object* v_toSeqRight_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___f_1624_; lean_object* v___f_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1613_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1614_ = lean_ctor_get(v___x_1613_, 0);
v_toFunctor_1615_ = lean_ctor_get(v_toApplicative_1614_, 0);
v_toSeq_1616_ = lean_ctor_get(v_toApplicative_1614_, 2);
v_toSeqLeft_1617_ = lean_ctor_get(v_toApplicative_1614_, 3);
v_toSeqRight_1618_ = lean_ctor_get(v_toApplicative_1614_, 4);
v___f_1619_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1620_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1615_, 2);
v___f_1621_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1621_, 0, v_toFunctor_1615_);
v___f_1622_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1622_, 0, v_toFunctor_1615_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___f_1621_);
lean_ctor_set(v___x_1623_, 1, v___f_1622_);
lean_inc(v_toSeqRight_1618_);
v___f_1624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1624_, 0, v_toSeqRight_1618_);
lean_inc(v_toSeqLeft_1617_);
v___f_1625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1625_, 0, v_toSeqLeft_1617_);
lean_inc(v_toSeq_1616_);
v___f_1626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1626_, 0, v_toSeq_1616_);
v___x_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1623_);
lean_ctor_set(v___x_1627_, 1, v___f_1619_);
lean_ctor_set(v___x_1627_, 2, v___f_1626_);
lean_ctor_set(v___x_1627_, 3, v___f_1625_);
lean_ctor_set(v___x_1627_, 4, v___f_1624_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
lean_ctor_set(v___x_1628_, 1, v___f_1620_);
v___x_1629_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1630_ = ((lean_object*)(l_Lake_DSL_optConfig___closed__1));
lean_inc(v_config_1466_);
v___x_1631_ = l_Lean_Syntax_isOfKind(v_config_1466_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_2422__overap_1633_; lean_object* v___x_1634_; 
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1632_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2422__overap_1633_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1632_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1634_ = lean_apply_3(v___x_2422__overap_1633_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = l_Lean_Syntax_getArg(v_config_1466_, v___x_1635_);
lean_inc(v___x_1636_);
v___x_1637_ = l_Lean_Syntax_matchesNull(v___x_1636_, v___x_1635_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1636_);
v___x_1639_ = l_Lean_Syntax_matchesNull(v___x_1636_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_2424__overap_1641_; lean_object* v___x_1642_; 
lean_dec(v___x_1636_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1640_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2424__overap_1641_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1640_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1642_ = lean_apply_3(v___x_2424__overap_1641_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1642_;
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = l_Lean_Syntax_getArg(v___x_1636_, v___x_1635_);
lean_dec(v___x_1636_);
v___x_1644_ = ((lean_object*)(l_Lake_DSL_declValWhere___closed__1));
lean_inc(v___x_1643_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_Lake_DSL_declValStruct___closed__1));
lean_inc(v___x_1643_);
v___x_1647_ = l_Lean_Syntax_isOfKind(v___x_1643_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_2426__overap_1649_; lean_object* v___x_1650_; 
lean_dec(v___x_1643_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1648_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2426__overap_1649_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1648_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1650_ = lean_apply_3(v___x_2426__overap_1649_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = l_Lean_Syntax_getArg(v___x_1643_, v___x_1635_);
v___x_1652_ = ((lean_object*)(l_Lake_DSL_structVal___closed__1));
lean_inc(v___x_1651_);
v___x_1653_ = l_Lean_Syntax_isOfKind(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_2428__overap_1655_; lean_object* v___x_1656_; 
lean_dec(v___x_1651_);
lean_dec(v___x_1643_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1654_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2428__overap_1655_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1654_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1656_ = lean_apply_3(v___x_2428__overap_1655_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1657_ = l_Lean_Syntax_getArg(v___x_1651_, v___x_1638_);
v___x_1658_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1657_);
v___x_1659_ = l_Lean_Syntax_isOfKind(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_2430__overap_1661_; lean_object* v___x_1662_; 
lean_dec(v___x_1657_);
lean_dec(v___x_1651_);
lean_dec(v___x_1643_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1660_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2430__overap_1661_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1660_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1662_ = lean_apply_3(v___x_2430__overap_1661_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1662_;
}
else
{
lean_object* v_tk_1663_; lean_object* v___x_1664_; lean_object* v_wds_x3f_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_tk_1663_ = l_Lean_Syntax_getArg(v___x_1651_, v___x_1635_);
lean_dec(v___x_1651_);
v___x_1664_ = l_Lean_Syntax_getArg(v___x_1657_, v___x_1635_);
lean_dec(v___x_1657_);
v___x_1672_ = l_Lean_Syntax_getArg(v___x_1643_, v___x_1638_);
lean_dec(v___x_1643_);
v___x_1673_ = l_Lean_Syntax_isNone(v___x_1672_);
if (v___x_1673_ == 0)
{
uint8_t v___x_1674_; 
lean_inc(v___x_1672_);
v___x_1674_ = l_Lean_Syntax_matchesNull(v___x_1672_, v___x_1638_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_2433__overap_1676_; lean_object* v___x_1677_; 
lean_dec(v___x_1672_);
lean_dec(v___x_1664_);
lean_dec(v_tk_1663_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1675_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2433__overap_1676_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1675_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1677_ = lean_apply_3(v___x_2433__overap_1676_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1677_;
}
else
{
lean_object* v_wds_x3f_1678_; 
v_wds_x3f_1678_ = l_Lean_Syntax_getArg(v___x_1672_, v___x_1635_);
lean_dec(v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1678_);
v___x_1682_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1678_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_2435__overap_1684_; lean_object* v___x_1685_; 
lean_dec(v_wds_x3f_1678_);
lean_dec(v___x_1664_);
lean_dec(v_tk_1663_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1683_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2435__overap_1684_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1683_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1685_ = lean_apply_3(v___x_2435__overap_1684_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1685_;
}
else
{
lean_dec_ref_known(v___x_1628_, 2);
goto v___jp_1679_;
}
}
else
{
lean_dec_ref_known(v___x_1628_, 2);
goto v___jp_1679_;
}
v___jp_1679_:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_wds_x3f_1678_);
v_wds_x3f_1666_ = v___x_1680_;
v___y_1667_ = v_a_1467_;
v___y_1668_ = v_a_1468_;
goto v___jp_1665_;
}
}
}
else
{
lean_object* v___x_1686_; 
lean_dec(v___x_1672_);
lean_dec_ref_known(v___x_1628_, 2);
v___x_1686_ = lean_box(0);
v_wds_x3f_1666_ = v___x_1686_;
v___y_1667_ = v_a_1467_;
v___y_1668_ = v_a_1468_;
goto v___jp_1665_;
}
v___jp_1665_:
{
lean_object* v_fs_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_fs_1669_ = l_Lean_Syntax_getArgs(v___x_1664_);
lean_dec(v___x_1664_);
v___x_1670_ = l_Lean_Syntax_getHeadInfo(v_tk_1663_);
lean_dec(v_tk_1663_);
v___x_1671_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1669_);
lean_dec_ref(v_fs_1669_);
v_whereInfo_1582_ = v___x_1670_;
v_fs_1583_ = v___x_1671_;
v_wds_x3f_1584_ = v_wds_x3f_1666_;
v___y_1585_ = v___y_1667_;
v___y_1586_ = v___y_1668_;
goto v___jp_1581_;
}
}
}
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1687_ = l_Lean_Syntax_getArg(v___x_1643_, v___x_1638_);
v___x_1688_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1687_);
v___x_1689_ = l_Lean_Syntax_isOfKind(v___x_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_2437__overap_1691_; lean_object* v___x_1692_; 
lean_dec(v___x_1687_);
lean_dec(v___x_1643_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1690_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2437__overap_1691_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1690_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1692_ = lean_apply_3(v___x_2437__overap_1691_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1692_;
}
else
{
lean_object* v_tk_1693_; lean_object* v___x_1694_; lean_object* v_wds_x3f_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v_tk_1693_ = l_Lean_Syntax_getArg(v___x_1643_, v___x_1635_);
v___x_1694_ = l_Lean_Syntax_getArg(v___x_1687_, v___x_1635_);
lean_dec(v___x_1687_);
v___x_1702_ = lean_unsigned_to_nat(2u);
v___x_1703_ = l_Lean_Syntax_getArg(v___x_1643_, v___x_1702_);
lean_dec(v___x_1643_);
v___x_1704_ = l_Lean_Syntax_isNone(v___x_1703_);
if (v___x_1704_ == 0)
{
uint8_t v___x_1705_; 
lean_inc(v___x_1703_);
v___x_1705_ = l_Lean_Syntax_matchesNull(v___x_1703_, v___x_1638_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_2440__overap_1707_; lean_object* v___x_1708_; 
lean_dec(v___x_1703_);
lean_dec(v___x_1694_);
lean_dec(v_tk_1693_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1706_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2440__overap_1707_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1706_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1708_ = lean_apply_3(v___x_2440__overap_1707_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1708_;
}
else
{
lean_object* v_wds_x3f_1709_; 
v_wds_x3f_1709_ = l_Lean_Syntax_getArg(v___x_1703_, v___x_1635_);
lean_dec(v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1709_);
v___x_1713_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1709_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_2442__overap_1715_; lean_object* v___x_1716_; 
lean_dec(v_wds_x3f_1709_);
lean_dec(v___x_1694_);
lean_dec(v_tk_1693_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
lean_dec(v_tyName_1462_);
v___x_1714_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2442__overap_1715_ = l_Lean_throwErrorAt___redArg(v___x_1628_, v___x_1629_, v_config_1466_, v___x_1714_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1716_ = lean_apply_3(v___x_2442__overap_1715_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1716_;
}
else
{
lean_dec_ref_known(v___x_1628_, 2);
goto v___jp_1710_;
}
}
else
{
lean_dec_ref_known(v___x_1628_, 2);
goto v___jp_1710_;
}
v___jp_1710_:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_wds_x3f_1709_);
v_wds_x3f_1696_ = v___x_1711_;
v___y_1697_ = v_a_1467_;
v___y_1698_ = v_a_1468_;
goto v___jp_1695_;
}
}
}
else
{
lean_object* v___x_1717_; 
lean_dec(v___x_1703_);
lean_dec_ref_known(v___x_1628_, 2);
v___x_1717_ = lean_box(0);
v_wds_x3f_1696_ = v___x_1717_;
v___y_1697_ = v_a_1467_;
v___y_1698_ = v_a_1468_;
goto v___jp_1695_;
}
v___jp_1695_:
{
lean_object* v_fs_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_fs_1699_ = l_Lean_Syntax_getArgs(v___x_1694_);
lean_dec(v___x_1694_);
v___x_1700_ = l_Lean_Syntax_getHeadInfo(v_tk_1693_);
lean_dec(v_tk_1693_);
v___x_1701_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1699_);
lean_dec_ref(v_fs_1699_);
v_whereInfo_1582_ = v___x_1700_;
v_fs_1583_ = v___x_1701_;
v_wds_x3f_1584_ = v_wds_x3f_1696_;
v___y_1585_ = v___y_1697_;
v___y_1586_ = v___y_1698_;
goto v___jp_1581_;
}
}
}
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec(v___x_1636_);
lean_dec_ref_known(v___x_1628_, 2);
v___x_1718_ = lean_box(2);
v___x_1719_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1720_ = lean_box(0);
v_whereInfo_1582_ = v___x_1718_;
v_fs_1583_ = v___x_1719_;
v_wds_x3f_1584_ = v___x_1720_;
v___y_1585_ = v_a_1467_;
v___y_1586_ = v_a_1468_;
goto v___jp_1581_;
}
}
v___jp_1470_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1479_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__0));
lean_inc_ref_n(v___y_1471_, 5);
lean_inc_ref_n(v___y_1473_, 6);
lean_inc_ref_n(v___y_1474_, 6);
v___x_1480_ = l_Lean_Name_mkStr4(v___y_1474_, v___y_1473_, v___y_1471_, v___x_1479_);
v___x_1481_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__1));
v___x_1482_ = l_Lean_Name_mkStr4(v___y_1474_, v___y_1473_, v___y_1471_, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
v___x_1484_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
lean_inc_n(v___y_1478_, 8);
v___x_1485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1478_);
lean_ctor_set(v___x_1485_, 1, v___x_1483_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_inc_ref_n(v___x_1485_, 8);
v___x_1486_ = l_Lean_Syntax_node7(v___y_1478_, v___x_1482_, v___x_1485_, v___x_1485_, v___x_1485_, v___x_1485_, v___x_1485_, v___x_1485_, v___x_1485_);
v___x_1487_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__2));
v___x_1488_ = l_Lean_Name_mkStr4(v___y_1474_, v___y_1473_, v___y_1471_, v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__3));
v___x_1490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1478_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__4));
v___x_1492_ = l_Lean_Name_mkStr4(v___y_1474_, v___y_1473_, v___y_1471_, v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
lean_inc_n(v___y_1477_, 2);
v___x_1494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1477_);
lean_ctor_set(v___x_1494_, 1, v___x_1483_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
v___x_1495_ = lean_unsigned_to_nat(2u);
v___x_1496_ = lean_mk_empty_array_with_capacity(v___x_1495_);
v___x_1497_ = lean_array_push(v___x_1496_, v_id_1464_);
v___x_1498_ = lean_array_push(v___x_1497_, v___x_1494_);
v___x_1499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1477_);
lean_ctor_set(v___x_1499_, 1, v___x_1492_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
v___x_1500_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__5));
v___x_1501_ = l_Lean_Name_mkStr4(v___y_1474_, v___y_1473_, v___y_1471_, v___x_1500_);
v___x_1502_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__2));
v___x_1503_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__2));
v___x_1504_ = l_Lean_Name_mkStr4(v___y_1474_, v___y_1473_, v___x_1502_, v___x_1503_);
v___x_1505_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__26));
v___x_1506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___y_1478_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_Syntax_node2(v___y_1478_, v___x_1504_, v___x_1506_, v_ty_1465_);
v___x_1508_ = l_Lean_Syntax_node1(v___y_1478_, v___x_1483_, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node2(v___y_1478_, v___x_1501_, v___x_1485_, v___x_1508_);
v___x_1510_ = l_Lean_Syntax_node5(v___y_1478_, v___x_1488_, v___x_1490_, v___x_1499_, v___x_1509_, v___y_1476_, v___x_1485_);
v___x_1511_ = l_Lean_Syntax_node2(v___y_1478_, v___x_1480_, v___x_1486_, v___x_1510_);
lean_inc(v___x_1511_);
v___x_1512_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_1466_, v___x_1511_, v___x_1512_, v___y_1475_, v___y_1472_);
return v___x_1513_;
}
v___jp_1514_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1524_ = l_Lean_mkOptionalNode(v___y_1523_);
v___x_1525_ = lean_unsigned_to_nat(3u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
v___x_1527_ = lean_array_push(v___x_1526_, v___y_1520_);
v___x_1528_ = lean_array_push(v___x_1527_, v___y_1518_);
v___x_1529_ = lean_array_push(v___x_1528_, v___x_1524_);
v___x_1530_ = lean_box(2);
lean_inc(v___y_1522_);
v___x_1531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___y_1522_);
lean_ctor_set(v___x_1531_, 2, v___x_1529_);
v___x_1532_ = l_Lean_Elab_Command_getRef___redArg(v___y_1521_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = 0;
v___x_1535_ = l_Lean_SourceInfo_fromRef(v_a_1533_, v___x_1534_);
lean_dec(v_a_1533_);
v___x_1536_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1521_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1537_; lean_object* v_toApplicative_1538_; lean_object* v_toFunctor_1539_; lean_object* v_toSeq_1540_; lean_object* v_toSeqLeft_1541_; lean_object* v_toSeqRight_1542_; lean_object* v___f_1543_; lean_object* v___f_1544_; lean_object* v___f_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; lean_object* v___f_1548_; lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_quotContext_x3f_1554_; 
lean_dec_ref_known(v___x_1536_, 1);
v___x_1537_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1538_ = lean_ctor_get(v___x_1537_, 0);
v_toFunctor_1539_ = lean_ctor_get(v_toApplicative_1538_, 0);
v_toSeq_1540_ = lean_ctor_get(v_toApplicative_1538_, 2);
v_toSeqLeft_1541_ = lean_ctor_get(v_toApplicative_1538_, 3);
v_toSeqRight_1542_ = lean_ctor_get(v_toApplicative_1538_, 4);
v___f_1543_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1544_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1539_, 2);
v___f_1545_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1545_, 0, v_toFunctor_1539_);
v___f_1546_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1546_, 0, v_toFunctor_1539_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___f_1545_);
lean_ctor_set(v___x_1547_, 1, v___f_1546_);
lean_inc(v_toSeqRight_1542_);
v___f_1548_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1548_, 0, v_toSeqRight_1542_);
lean_inc(v_toSeqLeft_1541_);
v___f_1549_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1549_, 0, v_toSeqLeft_1541_);
lean_inc(v_toSeq_1540_);
v___f_1550_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1550_, 0, v_toSeq_1540_);
v___x_1551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1547_);
lean_ctor_set(v___x_1551_, 1, v___f_1543_);
lean_ctor_set(v___x_1551_, 2, v___f_1550_);
lean_ctor_set(v___x_1551_, 3, v___f_1549_);
lean_ctor_set(v___x_1551_, 4, v___f_1548_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___f_1544_);
v___x_1553_ = l_Lean_Elab_Command_instMonadEnvCommandElabM;
v_quotContext_x3f_1554_ = lean_ctor_get(v___y_1521_, 5);
if (lean_obj_tag(v_quotContext_x3f_1554_) == 0)
{
lean_object* v___x_2408__overap_1555_; lean_object* v___x_1556_; 
v___x_2408__overap_1555_ = l_Lean_getMainModule___redArg(v___x_1552_, v___x_1553_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1521_);
v___x_1556_ = lean_apply_3(v___x_2408__overap_1555_, v___y_1521_, v___y_1517_, lean_box(0));
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_dec_ref_known(v___x_1556_, 1);
v___y_1471_ = v___y_1515_;
v___y_1472_ = v___y_1517_;
v___y_1473_ = v___y_1516_;
v___y_1474_ = v___y_1519_;
v___y_1475_ = v___y_1521_;
v___y_1476_ = v___x_1531_;
v___y_1477_ = v___x_1530_;
v___y_1478_ = v___x_1535_;
goto v___jp_1470_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v___x_1535_);
lean_dec_ref_known(v___x_1531_, 3);
lean_dec(v_config_1466_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1552_, 2);
v___y_1471_ = v___y_1515_;
v___y_1472_ = v___y_1517_;
v___y_1473_ = v___y_1516_;
v___y_1474_ = v___y_1519_;
v___y_1475_ = v___y_1521_;
v___y_1476_ = v___x_1531_;
v___y_1477_ = v___x_1530_;
v___y_1478_ = v___x_1535_;
goto v___jp_1470_;
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v___x_1535_);
lean_dec_ref_known(v___x_1531_, 3);
lean_dec(v_config_1466_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
v_a_1565_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1536_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1536_);
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
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref_known(v___x_1531_, 3);
lean_dec(v_config_1466_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
v_a_1573_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1532_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1532_);
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
v___jp_1581_:
{
lean_object* v_fieldMap_1587_; lean_object* v___x_1588_; lean_object* v_whereTk_1589_; lean_object* v___x_1590_; 
v_fieldMap_1587_ = lean_ctor_get(v_info_1463_, 1);
v___x_1588_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__10));
v_whereTk_1589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_1589_, 0, v_whereInfo_1582_);
lean_ctor_set(v_whereTk_1589_, 1, v___x_1588_);
v___x_1590_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1462_, v_fieldMap_1587_, v_fs_1583_, v___y_1585_, v___y_1586_);
lean_dec_ref(v_fs_1583_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__0));
v___x_1593_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__1));
v___x_1594_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__6));
v___x_1595_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__12));
if (lean_obj_tag(v_wds_x3f_1584_) == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_box(0);
v___y_1515_ = v___x_1594_;
v___y_1516_ = v___x_1593_;
v___y_1517_ = v___y_1586_;
v___y_1518_ = v_a_1591_;
v___y_1519_ = v___x_1592_;
v___y_1520_ = v_whereTk_1589_;
v___y_1521_ = v___y_1585_;
v___y_1522_ = v___x_1595_;
v___y_1523_ = v___x_1596_;
goto v___jp_1514_;
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_val_1597_ = lean_ctor_get(v_wds_x3f_1584_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_wds_x3f_1584_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v_wds_x3f_1584_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_val_1597_);
lean_dec(v_wds_x3f_1584_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
v___y_1515_ = v___x_1594_;
v___y_1516_ = v___x_1593_;
v___y_1517_ = v___y_1586_;
v___y_1518_ = v_a_1591_;
v___y_1519_ = v___x_1592_;
v___y_1520_ = v_whereTk_1589_;
v___y_1521_ = v___y_1585_;
v___y_1522_ = v___x_1595_;
v___y_1523_ = v___x_1602_;
goto v___jp_1514_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref_known(v_whereTk_1589_, 2);
lean_dec(v_wds_x3f_1584_);
lean_dec(v_config_1466_);
lean_dec(v_ty_1465_);
lean_dec(v_id_1464_);
v_a_1605_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1590_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1590_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_DSL_elabConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_tyName_1462_ = stack[0].m_obj;
lean_object* v_info_1463_ = stack[1].m_obj;
lean_object* v_id_1464_ = stack[2].m_obj;
lean_object* v_ty_1465_ = stack[3].m_obj;
lean_object* v_config_1466_ = stack[4].m_obj;
lean_object* v_a_1467_ = stack[5].m_obj;
lean_object* v_a_1468_ = stack[6].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l_Lake_DSL_elabConfig(v_tyName_1462_, v_info_1463_, v_id_1464_, v_ty_1465_, v_config_1466_, v_a_1467_, v_a_1468_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object* v_tyName_1722_, lean_object* v_info_1723_, lean_object* v_id_1724_, lean_object* v_ty_1725_, lean_object* v_config_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lake_DSL_elabConfig(v_tyName_1722_, v_info_1723_, v_id_1724_, v_ty_1725_, v_config_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec_ref(v_info_1723_);
return v_res_1730_;
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
