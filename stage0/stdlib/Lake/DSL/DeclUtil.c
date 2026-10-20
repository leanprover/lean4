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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(uint8_t v_suppressElabErrors_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_575_) == 1)
{
lean_object* v_pre_576_; 
v_pre_576_ = lean_ctor_get(v_x_575_, 0);
if (lean_obj_tag(v_pre_576_) == 0)
{
lean_object* v_str_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_str_577_ = lean_ctor_get(v_x_575_, 1);
v___x_578_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___closed__0));
v___x_579_ = lean_string_dec_eq(v_str_577_, v___x_578_);
if (v___x_579_ == 0)
{
return v___x_579_;
}
else
{
return v_suppressElabErrors_574_;
}
}
else
{
uint8_t v___x_580_; 
v___x_580_ = 0;
return v___x_580_;
}
}
else
{
uint8_t v___x_581_; 
v___x_581_ = 0;
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_582_, lean_object* v_x_583_){
_start:
{
uint8_t v_suppressElabErrors_boxed_584_; uint8_t v_res_585_; lean_object* v_r_586_; 
v_suppressElabErrors_boxed_584_ = lean_unbox(v_suppressElabErrors_582_);
v_res_585_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0(v_suppressElabErrors_boxed_584_, v_x_583_);
lean_dec(v_x_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_587_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_591_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_593_, 11, v___x_590_);
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
uint8_t v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; uint8_t v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; uint8_t v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; lean_object* v___y_730_; uint8_t v___y_734_; uint8_t v___y_735_; uint8_t v___x_750_; uint8_t v___y_752_; uint8_t v___x_762_; 
v___x_750_ = 2;
v___x_762_ = l_Lean_instBEqMessageSeverity_beq(v_severity_630_, v___x_750_);
if (v___x_762_ == 0)
{
v___y_752_ = v___x_762_;
goto v___jp_751_;
}
else
{
uint8_t v___x_763_; 
lean_inc_ref(v_msgData_629_);
v___x_763_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_629_);
if (v___x_763_ == 0)
{
v___y_752_ = v___x_763_;
goto v___jp_751_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v_msgData_629_);
v___x_764_ = lean_box(0);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
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
lean_ctor_set(v___x_654_, 1, v___y_637_);
lean_inc_ref(v___y_639_);
lean_inc_ref(v___y_641_);
v___x_655_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_655_, 0, v___y_641_);
lean_ctor_set(v___x_655_, 1, v___y_638_);
lean_ctor_set(v___x_655_, 2, v___y_640_);
lean_ctor_set(v___x_655_, 3, v___y_639_);
lean_ctor_set(v___x_655_, 4, v___x_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*5, v___y_642_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*5 + 1, v___y_636_);
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
lean_dec(v___y_640_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
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
lean_dec(v___y_640_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
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
lean_object* v_fileName_705_; lean_object* v_fileMap_706_; uint8_t v_suppressElabErrors_707_; lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_725_; 
v_fileName_705_ = lean_ctor_get(v___y_632_, 0);
v_fileMap_706_ = lean_ctor_get(v___y_632_, 1);
v_suppressElabErrors_707_ = lean_ctor_get_uint8(v___y_632_, sizeof(void*)*10);
v___x_708_ = lean_box(v_suppressElabErrors_707_);
v___f_709_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_709_, 0, v___x_708_);
v___x_710_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_629_);
v___x_711_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v___x_710_, v___y_633_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_725_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_725_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_725_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_inc_ref_n(v_fileMap_706_, 2);
v___x_716_ = l_Lean_FileMap_toPosition(v_fileMap_706_, v___y_702_);
lean_dec(v___y_702_);
v___x_717_ = l_Lean_FileMap_toPosition(v_fileMap_706_, v___y_704_);
lean_dec(v___y_704_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
v___x_719_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__9));
if (v_suppressElabErrors_707_ == 0)
{
lean_del_object(v___x_714_);
lean_dec_ref(v___f_709_);
v___y_636_ = v___y_701_;
v___y_637_ = v_a_712_;
v___y_638_ = v___x_716_;
v___y_639_ = v___x_719_;
v___y_640_ = v___x_718_;
v___y_641_ = v_fileName_705_;
v___y_642_ = v___y_703_;
v___y_643_ = v___y_633_;
goto v___jp_635_;
}
else
{
uint8_t v___x_720_; 
lean_inc(v_a_712_);
v___x_720_ = l_Lean_MessageData_hasTag(v___f_709_, v_a_712_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_723_; 
lean_dec_ref_known(v___x_718_, 1);
lean_dec_ref(v___x_716_);
lean_dec(v_a_712_);
v___x_721_ = lean_box(0);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_721_);
v___x_723_ = v___x_714_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_del_object(v___x_714_);
v___y_636_ = v___y_701_;
v___y_637_ = v_a_712_;
v___y_638_ = v___x_716_;
v___y_639_ = v___x_719_;
v___y_640_ = v___x_718_;
v___y_641_ = v_fileName_705_;
v___y_642_ = v___y_703_;
v___y_643_ = v___y_633_;
goto v___jp_635_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Syntax_getTailPos_x3f(v___y_728_, v___y_729_);
lean_dec(v___y_728_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_inc(v___y_730_);
v___y_701_ = v___y_727_;
v___y_702_ = v___y_730_;
v___y_703_ = v___y_729_;
v___y_704_ = v___y_730_;
goto v___jp_700_;
}
else
{
lean_object* v_val_732_; 
v_val_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v___x_731_, 1);
v___y_701_ = v___y_727_;
v___y_702_ = v___y_730_;
v___y_703_ = v___y_729_;
v___y_704_ = v_val_732_;
goto v___jp_700_;
}
}
v___jp_733_:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Elab_Command_getRef___redArg(v___y_632_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v_ref_738_; lean_object* v___x_739_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v_ref_738_ = l_Lean_replaceRef(v_ref_628_, v_a_737_);
lean_dec(v_a_737_);
v___x_739_ = l_Lean_Syntax_getPos_x3f(v_ref_738_, v___y_734_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___y_727_ = v___y_735_;
v___y_728_ = v_ref_738_;
v___y_729_ = v___y_734_;
v___y_730_ = v___x_740_;
goto v___jp_726_;
}
else
{
lean_object* v_val_741_; 
v_val_741_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v___x_739_, 1);
v___y_727_ = v___y_735_;
v___y_728_ = v_ref_738_;
v___y_729_ = v___y_734_;
v___y_730_ = v_val_741_;
goto v___jp_726_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_msgData_629_);
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
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_scopes_755_; lean_object* v___x_756_; lean_object* v_opts_757_; uint8_t v___x_758_; uint8_t v___x_759_; 
v___x_753_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_754_ = lean_st_ref_get(v___y_633_);
v_scopes_755_ = lean_ctor_get(v___x_754_, 2);
lean_inc(v_scopes_755_);
lean_dec(v___x_754_);
v___x_756_ = l_List_head_x21___redArg(v___x_753_, v_scopes_755_);
lean_dec(v_scopes_755_);
v_opts_757_ = lean_ctor_get(v___x_756_, 1);
lean_inc_ref(v_opts_757_);
lean_dec(v___x_756_);
v___x_758_ = 1;
v___x_759_ = l_Lean_instBEqMessageSeverity_beq(v_severity_630_, v___x_758_);
if (v___x_759_ == 0)
{
lean_dec_ref(v_opts_757_);
v___y_734_ = v___y_752_;
v___y_735_ = v_severity_630_;
goto v___jp_733_;
}
else
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = l_Lean_warningAsError;
v___x_761_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_757_, v___x_760_);
lean_dec_ref(v_opts_757_);
if (v___x_761_ == 0)
{
v___y_734_ = v___y_752_;
v___y_735_ = v_severity_630_;
goto v___jp_733_;
}
else
{
v___y_734_ = v___y_752_;
v___y_735_ = v___x_750_;
goto v___jp_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4___boxed(lean_object* v_ref_766_, lean_object* v_msgData_767_, lean_object* v_severity_768_, lean_object* v_isSilent_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v_severity_boxed_773_; uint8_t v_isSilent_boxed_774_; lean_object* v_res_775_; 
v_severity_boxed_773_ = lean_unbox(v_severity_768_);
v_isSilent_boxed_774_ = lean_unbox(v_isSilent_769_);
v_res_775_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_766_, v_msgData_767_, v_severity_boxed_773_, v_isSilent_boxed_774_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v_ref_766_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(lean_object* v_ref_776_, lean_object* v_msgData_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = 1;
v___x_782_ = 0;
v___x_783_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4(v_ref_776_, v_msgData_777_, v___x_781_, v___x_782_, v___y_778_, v___y_779_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2___boxed(lean_object* v_ref_784_, lean_object* v_msgData_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v_ref_784_, v_msgData_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v_ref_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(lean_object* v_t_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v_infoState_794_; uint8_t v_enabled_795_; 
v___x_793_ = lean_st_ref_get(v___y_791_);
v_infoState_794_ = lean_ctor_get(v___x_793_, 8);
lean_inc_ref(v_infoState_794_);
lean_dec(v___x_793_);
v_enabled_795_ = lean_ctor_get_uint8(v_infoState_794_, sizeof(void*)*3);
lean_dec_ref(v_infoState_794_);
if (v_enabled_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v_t_790_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v_infoState_799_; lean_object* v_env_800_; lean_object* v_messages_801_; lean_object* v_scopes_802_; lean_object* v_usedQuotCtxts_803_; lean_object* v_nextMacroScope_804_; lean_object* v_maxRecDepth_805_; lean_object* v_ngen_806_; lean_object* v_auxDeclNGen_807_; lean_object* v_traceState_808_; lean_object* v_snapshotTasks_809_; lean_object* v_prevLinterStates_810_; lean_object* v_codeQualityEntryTasks_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_833_; 
v___x_798_ = lean_st_ref_take(v___y_791_);
v_infoState_799_ = lean_ctor_get(v___x_798_, 8);
v_env_800_ = lean_ctor_get(v___x_798_, 0);
v_messages_801_ = lean_ctor_get(v___x_798_, 1);
v_scopes_802_ = lean_ctor_get(v___x_798_, 2);
v_usedQuotCtxts_803_ = lean_ctor_get(v___x_798_, 3);
v_nextMacroScope_804_ = lean_ctor_get(v___x_798_, 4);
v_maxRecDepth_805_ = lean_ctor_get(v___x_798_, 5);
v_ngen_806_ = lean_ctor_get(v___x_798_, 6);
v_auxDeclNGen_807_ = lean_ctor_get(v___x_798_, 7);
v_traceState_808_ = lean_ctor_get(v___x_798_, 9);
v_snapshotTasks_809_ = lean_ctor_get(v___x_798_, 10);
v_prevLinterStates_810_ = lean_ctor_get(v___x_798_, 11);
v_codeQualityEntryTasks_811_ = lean_ctor_get(v___x_798_, 12);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_833_ == 0)
{
v___x_813_ = v___x_798_;
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_codeQualityEntryTasks_811_);
lean_inc(v_prevLinterStates_810_);
lean_inc(v_snapshotTasks_809_);
lean_inc(v_traceState_808_);
lean_inc(v_infoState_799_);
lean_inc(v_auxDeclNGen_807_);
lean_inc(v_ngen_806_);
lean_inc(v_maxRecDepth_805_);
lean_inc(v_nextMacroScope_804_);
lean_inc(v_usedQuotCtxts_803_);
lean_inc(v_scopes_802_);
lean_inc(v_messages_801_);
lean_inc(v_env_800_);
lean_dec(v___x_798_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v_enabled_815_; lean_object* v_assignment_816_; lean_object* v_lazyAssignment_817_; lean_object* v_trees_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_832_; 
v_enabled_815_ = lean_ctor_get_uint8(v_infoState_799_, sizeof(void*)*3);
v_assignment_816_ = lean_ctor_get(v_infoState_799_, 0);
v_lazyAssignment_817_ = lean_ctor_get(v_infoState_799_, 1);
v_trees_818_ = lean_ctor_get(v_infoState_799_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_infoState_799_);
if (v_isSharedCheck_832_ == 0)
{
v___x_820_ = v_infoState_799_;
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_trees_818_);
lean_inc(v_lazyAssignment_817_);
lean_inc(v_assignment_816_);
lean_dec(v_infoState_799_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_822_ = lean_box(0);
v___x_823_ = l_Lean_PersistentArray_push___redArg(v_trees_818_, v_t_790_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 2, v___x_823_);
v___x_825_ = v___x_820_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_assignment_816_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_lazyAssignment_817_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___x_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3, v_enabled_815_);
v___x_825_ = v_reuseFailAlloc_831_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 8, v___x_825_);
v___x_827_ = v___x_813_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_env_800_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_messages_801_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_scopes_802_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_usedQuotCtxts_803_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_nextMacroScope_804_);
lean_ctor_set(v_reuseFailAlloc_830_, 5, v_maxRecDepth_805_);
lean_ctor_set(v_reuseFailAlloc_830_, 6, v_ngen_806_);
lean_ctor_set(v_reuseFailAlloc_830_, 7, v_auxDeclNGen_807_);
lean_ctor_set(v_reuseFailAlloc_830_, 8, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_830_, 9, v_traceState_808_);
lean_ctor_set(v_reuseFailAlloc_830_, 10, v_snapshotTasks_809_);
lean_ctor_set(v_reuseFailAlloc_830_, 11, v_prevLinterStates_810_);
lean_ctor_set(v_reuseFailAlloc_830_, 12, v_codeQualityEntryTasks_811_);
v___x_827_ = v_reuseFailAlloc_830_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_st_ref_put(v___y_791_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_822_);
return v___x_829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_t_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_834_, v___y_835_);
lean_dec(v___y_835_);
return v_res_837_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_unsigned_to_nat(32u);
v___x_839_ = lean_mk_empty_array_with_capacity(v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_841_ = ((size_t)5ULL);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_unsigned_to_nat(32u);
v___x_844_ = lean_mk_empty_array_with_capacity(v___x_843_);
v___x_845_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__0);
v___x_846_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
lean_ctor_set(v___x_846_, 2, v___x_842_);
lean_ctor_set(v___x_846_, 3, v___x_842_);
lean_ctor_set_usize(v___x_846_, 4, v___x_841_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(lean_object* v_t_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_infoState_852_; uint8_t v_enabled_853_; 
v___x_851_ = lean_st_ref_get(v___y_849_);
v_infoState_852_ = lean_ctor_get(v___x_851_, 8);
lean_inc_ref(v_infoState_852_);
lean_dec(v___x_851_);
v_enabled_853_ = lean_ctor_get_uint8(v_infoState_852_, sizeof(void*)*3);
lean_dec_ref(v_infoState_852_);
if (v_enabled_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec_ref(v_t_847_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___closed__1);
v___x_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_857_, 0, v_t_847_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v___x_857_, v___y_849_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2___boxed(lean_object* v_t_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v_t_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(lean_object* v_info_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_868_, 0, v_info_864_);
v___x_869_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2(v___x_868_, v___y_865_, v___y_866_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1___boxed(lean_object* v_info_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v_info_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_874_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_box(1);
v___x_876_ = l_Lean_MessageData_ofFormat(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__2));
v___x_881_ = l_Lean_MessageData_ofFormat(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
return v_x_882_;
}
else
{
lean_object* v_head_884_; lean_object* v_tail_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_907_; 
v_head_884_ = lean_ctor_get(v_x_883_, 0);
v_tail_885_ = lean_ctor_get(v_x_883_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_907_ == 0)
{
v___x_887_ = v_x_883_;
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_tail_885_);
lean_inc(v_head_884_);
lean_dec(v_x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_before_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_905_; 
v_before_889_ = lean_ctor_get(v_head_884_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_head_884_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v_head_884_, 1);
lean_dec(v_unused_906_);
v___x_891_ = v_head_884_;
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_before_889_);
lean_dec(v_head_884_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 7);
lean_ctor_set(v___x_891_, 1, v___x_893_);
lean_ctor_set(v___x_891_, 0, v_x_882_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_x_882_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_893_);
v___x_895_ = v_reuseFailAlloc_904_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__3);
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 7);
lean_ctor_set(v___x_887_, 1, v___x_896_);
lean_ctor_set(v___x_887_, 0, v___x_895_);
v___x_898_ = v___x_887_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_896_);
v___x_898_ = v_reuseFailAlloc_903_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = l_Lean_MessageData_ofSyntax(v_before_889_);
v___x_900_ = l_Lean_indentD(v___x_899_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_898_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v_x_882_ = v___x_901_;
v_x_883_ = v_tail_885_;
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
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_912_ = l_Lean_MessageData_ofFormat(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_913_, lean_object* v_macroStack_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_scopes_919_; lean_object* v___x_920_; lean_object* v_opts_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_917_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_918_ = lean_st_ref_get(v___y_915_);
v_scopes_919_ = lean_ctor_get(v___x_918_, 2);
lean_inc(v_scopes_919_);
lean_dec(v___x_918_);
v___x_920_ = l_List_head_x21___redArg(v___x_917_, v_scopes_919_);
lean_dec(v_scopes_919_);
v_opts_921_ = lean_ctor_get(v___x_920_, 1);
lean_inc_ref(v_opts_921_);
lean_dec(v___x_920_);
v___x_922_ = l_Lean_Elab_pp_macroStack;
v___x_923_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2_spec__4_spec__8(v_opts_921_, v___x_922_);
lean_dec_ref(v_opts_921_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec(v_macroStack_914_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_msgData_913_);
return v___x_924_;
}
else
{
if (lean_obj_tag(v_macroStack_914_) == 0)
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v_msgData_913_);
return v___x_925_;
}
else
{
lean_object* v_head_926_; lean_object* v_after_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_942_; 
v_head_926_ = lean_ctor_get(v_macroStack_914_, 0);
lean_inc(v_head_926_);
v_after_927_ = lean_ctor_get(v_head_926_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_head_926_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v_head_926_, 0);
lean_dec(v_unused_943_);
v___x_929_ = v_head_926_;
v_isShared_930_ = v_isSharedCheck_942_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_after_927_);
lean_dec(v_head_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_942_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7___closed__0);
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 7);
lean_ctor_set(v___x_929_, 1, v___x_931_);
lean_ctor_set(v___x_929_, 0, v_msgData_913_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_msgData_913_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_941_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_msgData_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_934_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_MessageData_ofSyntax(v_after_927_);
v___x_937_ = l_Lean_indentD(v___x_936_);
v_msgData_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_938_, 0, v___x_935_);
lean_ctor_set(v_msgData_938_, 1, v___x_937_);
v___x_939_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2_spec__7(v_msgData_938_, v_macroStack_914_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_944_, lean_object* v_macroStack_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_944_, v_macroStack_945_, v___y_946_);
lean_dec(v___y_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Elab_Command_getRef___redArg(v___y_950_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_macroStack_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v_macroStack_955_ = lean_ctor_get(v___y_950_, 4);
v___x_956_ = l_Lean_Elab_getBetterRef(v_a_954_, v_macroStack_955_);
lean_dec(v_a_954_);
v___x_957_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msg_949_, v___y_951_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
lean_inc(v_macroStack_955_);
v___x_959_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_a_958_, v_macroStack_955_, v___y_951_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_956_);
lean_ctor_set(v___x_964_, 1, v_a_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_msg_949_);
v_a_969_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_953_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_953_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg___boxed(lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(lean_object* v_ref_982_, lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Elab_Command_getRef___redArg(v___y_984_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_fileName_989_; lean_object* v_fileMap_990_; lean_object* v_currRecDepth_991_; lean_object* v_cmdPos_992_; lean_object* v_macroStack_993_; lean_object* v_quotContext_x3f_994_; lean_object* v_currMacroScope_995_; lean_object* v_snap_x3f_996_; lean_object* v_cancelTk_x3f_997_; uint8_t v_suppressElabErrors_998_; lean_object* v_ref_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v_fileName_989_ = lean_ctor_get(v___y_984_, 0);
v_fileMap_990_ = lean_ctor_get(v___y_984_, 1);
v_currRecDepth_991_ = lean_ctor_get(v___y_984_, 2);
v_cmdPos_992_ = lean_ctor_get(v___y_984_, 3);
v_macroStack_993_ = lean_ctor_get(v___y_984_, 4);
v_quotContext_x3f_994_ = lean_ctor_get(v___y_984_, 5);
v_currMacroScope_995_ = lean_ctor_get(v___y_984_, 6);
v_snap_x3f_996_ = lean_ctor_get(v___y_984_, 8);
v_cancelTk_x3f_997_ = lean_ctor_get(v___y_984_, 9);
v_suppressElabErrors_998_ = lean_ctor_get_uint8(v___y_984_, sizeof(void*)*10);
v_ref_999_ = l_Lean_replaceRef(v_ref_982_, v_a_988_);
lean_dec(v_a_988_);
lean_inc(v_cancelTk_x3f_997_);
lean_inc(v_snap_x3f_996_);
lean_inc(v_currMacroScope_995_);
lean_inc(v_quotContext_x3f_994_);
lean_inc(v_macroStack_993_);
lean_inc(v_cmdPos_992_);
lean_inc(v_currRecDepth_991_);
lean_inc_ref(v_fileMap_990_);
lean_inc_ref(v_fileName_989_);
v___x_1000_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1000_, 0, v_fileName_989_);
lean_ctor_set(v___x_1000_, 1, v_fileMap_990_);
lean_ctor_set(v___x_1000_, 2, v_currRecDepth_991_);
lean_ctor_set(v___x_1000_, 3, v_cmdPos_992_);
lean_ctor_set(v___x_1000_, 4, v_macroStack_993_);
lean_ctor_set(v___x_1000_, 5, v_quotContext_x3f_994_);
lean_ctor_set(v___x_1000_, 6, v_currMacroScope_995_);
lean_ctor_set(v___x_1000_, 7, v_ref_999_);
lean_ctor_set(v___x_1000_, 8, v_snap_x3f_996_);
lean_ctor_set(v___x_1000_, 9, v_cancelTk_x3f_997_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*10, v_suppressElabErrors_998_);
v___x_1001_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_983_, v___x_1000_, v___y_985_);
lean_dec_ref_known(v___x_1000_, 10);
return v___x_1001_;
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_msg_983_);
v_a_1002_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_987_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_987_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg___boxed(lean_object* v_ref_1010_, lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1010_, v_msg_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v_ref_1010_);
return v_res_1015_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__0));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = lean_box(1);
v___x_1022_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_1023_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__2);
v___x_1024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
lean_ctor_set(v___x_1024_, 2, v___x_1021_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__4));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__6));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__8));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__10));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__12));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__14));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__16));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(lean_object* v_tyName_1046_, lean_object* v_infos_1047_, lean_object* v_as_1048_, size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_a_1056_; uint8_t v___x_1060_; 
v___x_1060_ = lean_usize_dec_lt(v_i_1050_, v_sz_1049_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v_tyName_1046_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_b_1051_);
return v___x_1061_;
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_a_1062_ = lean_array_uget_borrowed(v_as_1048_, v_i_1050_);
v___x_1063_ = ((lean_object*)(l_Lake_DSL_declField___closed__1));
lean_inc(v_a_1062_);
v___x_1064_ = l_Lean_Syntax_isOfKind(v_a_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__1);
v___x_1066_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_a_1062_, v___x_1065_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_dec_ref_known(v___x_1066_, 1);
v_a_1056_ = v_b_1051_;
goto v___jp_1055_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_b_1051_);
lean_dec(v_tyName_1046_);
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = l_Lean_Syntax_getArg(v_a_1062_, v___x_1075_);
v___x_1077_ = lean_unsigned_to_nat(2u);
v___x_1078_ = l_Lean_Syntax_getArg(v_a_1062_, v___x_1077_);
v___x_1079_ = l_Lean_TSyntax_getId(v___x_1076_);
lean_inc(v___x_1079_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
v___x_1081_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__3);
lean_inc(v_tyName_1046_);
lean_inc(v_a_1062_);
v___x_1082_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1082_, 0, v_a_1062_);
lean_ctor_set(v___x_1082_, 1, v___x_1080_);
lean_ctor_set(v___x_1082_, 2, v___x_1081_);
lean_ctor_set(v___x_1082_, 3, v_tyName_1046_);
v___x_1083_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1(v___x_1082_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref_known(v___x_1083_, 1);
v___x_1084_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_infos_1047_, v___x_1079_);
if (lean_obj_tag(v___x_1084_) == 1)
{
lean_object* v_val_1085_; lean_object* v_realName_1086_; uint8_t v_canonical_1087_; 
v_val_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v_realName_1086_ = lean_ctor_get(v_val_1085_, 1);
lean_inc(v_realName_1086_);
v_canonical_1087_ = lean_ctor_get_uint8(v_val_1085_, sizeof(void*)*2);
lean_dec(v_val_1085_);
if (v_canonical_1087_ == 0)
{
uint8_t v___x_1091_; 
v___x_1091_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_realName_1086_, v_b_1051_);
if (v___x_1091_ == 0)
{
lean_dec(v___x_1079_);
goto v___jp_1088_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1092_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__5);
lean_inc(v_realName_1086_);
v___x_1093_ = l_Lean_MessageData_ofName(v_realName_1086_);
lean_inc_ref(v___x_1093_);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__7);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_MessageData_ofName(v___x_1079_);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__9);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___x_1093_);
v___x_1102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__11);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1076_, v___x_1103_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref_known(v___x_1104_, 1);
goto v___jp_1088_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_realName_1086_);
lean_dec(v___x_1078_);
lean_dec(v___x_1076_);
lean_dec(v_b_1051_);
lean_dec(v_tyName_1046_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
else
{
lean_dec(v___x_1079_);
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1076_);
lean_ctor_set(v___x_1089_, 1, v___x_1078_);
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_realName_1086_, v___x_1089_, v_b_1051_);
v_a_1056_ = v___x_1090_;
goto v___jp_1055_;
}
}
else
{
lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v___x_1084_);
lean_dec(v___x_1078_);
v___x_1113_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__13);
v___x_1114_ = 0;
lean_inc(v_tyName_1046_);
v___x_1115_ = l_Lean_MessageData_ofConstName(v_tyName_1046_, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1113_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__15);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_MessageData_ofName(v___x_1079_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___closed__17);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__2(v___x_1076_, v___x_1122_, v___y_1052_, v___y_1053_);
lean_dec(v___x_1076_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_dec_ref_known(v___x_1123_, 1);
v_a_1056_ = v_b_1051_;
goto v___jp_1055_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v_b_1051_);
lean_dec(v_tyName_1046_);
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v___x_1079_);
lean_dec(v___x_1078_);
lean_dec(v___x_1076_);
lean_dec(v_b_1051_);
lean_dec(v_tyName_1046_);
v_a_1132_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1083_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1083_);
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
v___jp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1050_, v___x_1057_);
v_i_1050_ = v___x_1058_;
v_b_1051_ = v_a_1056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3___boxed(lean_object* v_tyName_1140_, lean_object* v_infos_1141_, lean_object* v_as_1142_, lean_object* v_sz_1143_, lean_object* v_i_1144_, lean_object* v_b_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
size_t v_sz_boxed_1149_; size_t v_i_boxed_1150_; lean_object* v_res_1151_; 
v_sz_boxed_1149_ = lean_unbox_usize(v_sz_1143_);
lean_dec(v_sz_1143_);
v_i_boxed_1150_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1140_, v_infos_1141_, v_as_1142_, v_sz_boxed_1149_, v_i_boxed_1150_, v_b_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_as_1142_);
lean_dec(v_infos_1141_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object* v_tyName_1163_, lean_object* v_infos_1164_, lean_object* v_fs_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_m_1169_; size_t v_sz_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
v_m_1169_ = lean_box(1);
v_sz_1170_ = lean_array_size(v_fs_1165_);
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__3(v_tyName_1163_, v_infos_1164_, v_fs_1165_, v_sz_1170_, v___x_1171_, v_m_1169_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1191_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v___x_1174_, v_a_1173_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1191_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1191_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1180_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
v___x_1181_ = lean_box(2);
v___x_1182_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__2));
v___x_1183_ = l_Lean_Syntax_mkSep(v_a_1176_, v___x_1182_);
lean_dec(v_a_1176_);
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_mk_empty_array_with_capacity(v___x_1184_);
v___x_1186_ = lean_array_push(v___x_1185_, v___x_1183_);
v___x_1187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1181_);
lean_ctor_set(v___x_1187_, 1, v___x_1180_);
lean_ctor_set(v___x_1187_, 2, v___x_1186_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1187_);
v___x_1189_ = v___x_1178_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1172_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1172_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___boxed(lean_object* v_tyName_1200_, lean_object* v_infos_1201_, lean_object* v_fs_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1200_, v_infos_1201_, v_fs_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec_ref(v_fs_1202_);
lean_dec(v_infos_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(lean_object* v_00_u03b1_1207_, lean_object* v_ref_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___redArg(v_ref_1208_, v_msg_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_ref_1215_, lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0(v_00_u03b1_1214_, v_ref_1215_, v_msg_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v_ref_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(lean_object* v_init_1221_, lean_object* v_x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg(v_init_1221_, v_x_1222_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___boxed(lean_object* v_init_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4(v_init_1227_, v_x_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(lean_object* v_msgData_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___redArg(v_msgData_1233_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__1(v_msgData_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(lean_object* v_00_u03b1_1243_, lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___redArg(v_msg_1244_, v___y_1245_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0(v_00_u03b1_1249_, v_msg_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(lean_object* v_t_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___redArg(v_t_1255_, v___y_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5___boxed(lean_object* v_t_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__1_spec__2_spec__5(v_t_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(lean_object* v_msgData_1265_, lean_object* v_macroStack_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___redArg(v_msgData_1265_, v_macroStack_1266_, v___y_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1271_, lean_object* v_macroStack_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__0_spec__0_spec__2(v_msgData_1271_, v_macroStack_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v_env_1280_; lean_object* v___x_1281_; lean_object* v_mainModule_1282_; lean_object* v___x_1283_; 
v___x_1279_ = lean_st_ref_get(v___y_1277_);
v_env_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_ref(v_env_1280_);
lean_dec(v___x_1279_);
v___x_1281_ = l_Lean_Environment_header(v_env_1280_);
lean_dec_ref(v_env_1280_);
v_mainModule_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_mainModule_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_mainModule_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1284_);
lean_dec(v___y_1284_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(lean_object* v___x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_a_1292_; lean_object* v_quotContext_x3f_1311_; 
v_quotContext_x3f_1311_ = lean_ctor_get(v___y_1288_, 5);
if (lean_obj_tag(v_quotContext_x3f_1311_) == 0)
{
lean_object* v___x_1312_; lean_object* v_a_1313_; 
v___x_1312_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1289_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref(v___x_1312_);
v_a_1292_ = v_a_1313_;
goto v___jp_1291_;
}
else
{
lean_object* v_val_1314_; 
v_val_1314_ = lean_ctor_get(v_quotContext_x3f_1311_, 0);
lean_inc(v_val_1314_);
v_a_1292_ = v_val_1314_;
goto v___jp_1291_;
}
v___jp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1288_);
lean_dec_ref(v___y_1288_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1302_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = l_Lean_addMacroScope(v_a_1292_, v___x_1287_, v_a_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_a_1292_);
lean_dec(v___x_1287_);
v_a_1303_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1293_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1293_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0___boxed(lean_object* v___x_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___lam__0(v___x_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___f_1328_; lean_object* v___x_1329_; 
v___f_1328_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___closed__2));
v___x_1329_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___f_1328_, v___y_1325_, v___y_1326_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0___boxed(lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(lean_object* v_ref_1334_, uint8_t v_canonical_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0(v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1348_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = l_Lean_mkIdentFrom(v_ref_1334_, v_a_1340_, v_canonical_1335_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1344_);
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1339_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1339_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0___boxed(lean_object* v_ref_1357_, lean_object* v_canonical_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v_canonical_boxed_1362_; lean_object* v_res_1363_; 
v_canonical_boxed_1362_ = lean_unbox(v_canonical_1358_);
v_res_1363_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_ref_1357_, v_canonical_boxed_1362_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_ref_1357_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object* v_stx_x3f_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
if (lean_obj_tag(v_stx_x3f_1364_) == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Elab_Command_getRef___redArg(v_a_1365_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = 0;
v___x_1371_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0(v_a_1369_, v___x_1370_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1369_);
return v___x_1371_;
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1368_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1368_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
v_val_1380_ = lean_ctor_get(v_stx_x3f_1364_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_stx_x3f_1364_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1382_ = v_stx_x3f_1364_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v_stx_x3f_1364_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = l_Lake_DSL_expandIdentOrStrAsIdent(v_val_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
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
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent___boxed(lean_object* v_stx_x3f_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lake_DSL_mkConfigDeclIdent(v_stx_x3f_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___redArg(v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_getMainModule___at___00Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lake_DSL_mkConfigDeclIdent_spec__0_spec__0_spec__1(v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
return v_res_1401_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__6(void){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_instMonadEIO___redArg();
return v___x_1408_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__7(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__6, &l_Lake_DSL_elabConfig___closed__6_once, _init_l_Lake_DSL_elabConfig___closed__6);
v___x_1410_ = l_StateRefT_x27_instMonad___redArg(v___x_1409_);
return v___x_1410_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__13(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1420_ = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM;
v___x_1421_ = l_Lean_Elab_Command_instMonadRefCommandElabM;
v___x_1422_ = l_Lean_Elab_Command_instMonadExceptOfExceptionCommandElabM;
v___x_1423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v___x_1421_);
lean_ctor_set(v___x_1423_, 2, v___x_1420_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__15(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__14));
v___x_1426_ = l_Lean_stringToMessageData(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object* v_tyName_1427_, lean_object* v_info_1428_, lean_object* v_id_1429_, lean_object* v_ty_1430_, lean_object* v_config_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v_whereInfo_1547_; lean_object* v_fs_1548_; lean_object* v_wds_x3f_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___x_1578_; lean_object* v_toApplicative_1579_; lean_object* v_toFunctor_1580_; lean_object* v_toSeq_1581_; lean_object* v_toSeqLeft_1582_; lean_object* v_toSeqRight_1583_; lean_object* v___f_1584_; lean_object* v___f_1585_; lean_object* v___f_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; lean_object* v___f_1589_; lean_object* v___f_1590_; lean_object* v___f_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1578_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1579_ = lean_ctor_get(v___x_1578_, 0);
v_toFunctor_1580_ = lean_ctor_get(v_toApplicative_1579_, 0);
v_toSeq_1581_ = lean_ctor_get(v_toApplicative_1579_, 2);
v_toSeqLeft_1582_ = lean_ctor_get(v_toApplicative_1579_, 3);
v_toSeqRight_1583_ = lean_ctor_get(v_toApplicative_1579_, 4);
v___f_1584_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1585_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1580_, 2);
v___f_1586_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1586_, 0, v_toFunctor_1580_);
v___f_1587_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1587_, 0, v_toFunctor_1580_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___f_1586_);
lean_ctor_set(v___x_1588_, 1, v___f_1587_);
lean_inc(v_toSeqRight_1583_);
v___f_1589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1589_, 0, v_toSeqRight_1583_);
lean_inc(v_toSeqLeft_1582_);
v___f_1590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1590_, 0, v_toSeqLeft_1582_);
lean_inc(v_toSeq_1581_);
v___f_1591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1591_, 0, v_toSeq_1581_);
v___x_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1588_);
lean_ctor_set(v___x_1592_, 1, v___f_1584_);
lean_ctor_set(v___x_1592_, 2, v___f_1591_);
lean_ctor_set(v___x_1592_, 3, v___f_1590_);
lean_ctor_set(v___x_1592_, 4, v___f_1589_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___f_1585_);
v___x_1594_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__13, &l_Lake_DSL_elabConfig___closed__13_once, _init_l_Lake_DSL_elabConfig___closed__13);
v___x_1595_ = ((lean_object*)(l_Lake_DSL_optConfig___closed__1));
lean_inc(v_config_1431_);
v___x_1596_ = l_Lean_Syntax_isOfKind(v_config_1431_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_2416__overap_1598_; lean_object* v___x_1599_; 
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1597_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2416__overap_1598_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1597_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1599_ = lean_apply_3(v___x_2416__overap_1598_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = l_Lean_Syntax_getArg(v_config_1431_, v___x_1600_);
lean_inc(v___x_1601_);
v___x_1602_ = l_Lean_Syntax_matchesNull(v___x_1601_, v___x_1600_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1601_);
v___x_1604_ = l_Lean_Syntax_matchesNull(v___x_1601_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_2418__overap_1606_; lean_object* v___x_1607_; 
lean_dec(v___x_1601_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1605_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2418__overap_1606_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1605_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1607_ = lean_apply_3(v___x_2418__overap_1606_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = l_Lean_Syntax_getArg(v___x_1601_, v___x_1600_);
lean_dec(v___x_1601_);
v___x_1609_ = ((lean_object*)(l_Lake_DSL_declValWhere___closed__1));
lean_inc(v___x_1608_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = ((lean_object*)(l_Lake_DSL_declValStruct___closed__1));
lean_inc(v___x_1608_);
v___x_1612_ = l_Lean_Syntax_isOfKind(v___x_1608_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_2420__overap_1614_; lean_object* v___x_1615_; 
lean_dec(v___x_1608_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1613_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2420__overap_1614_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1613_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1615_ = lean_apply_3(v___x_2420__overap_1614_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1600_);
v___x_1617_ = ((lean_object*)(l_Lake_DSL_structVal___closed__1));
lean_inc(v___x_1616_);
v___x_1618_ = l_Lean_Syntax_isOfKind(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_2422__overap_1620_; lean_object* v___x_1621_; 
lean_dec(v___x_1616_);
lean_dec(v___x_1608_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1619_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2422__overap_1620_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1619_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1621_ = lean_apply_3(v___x_2422__overap_1620_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1622_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1603_);
v___x_1623_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1622_);
v___x_1624_ = l_Lean_Syntax_isOfKind(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_2424__overap_1626_; lean_object* v___x_1627_; 
lean_dec(v___x_1622_);
lean_dec(v___x_1616_);
lean_dec(v___x_1608_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1625_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2424__overap_1626_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1625_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1627_ = lean_apply_3(v___x_2424__overap_1626_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1627_;
}
else
{
lean_object* v_tk_1628_; lean_object* v___x_1629_; lean_object* v_wds_x3f_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_tk_1628_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1600_);
lean_dec(v___x_1616_);
v___x_1629_ = l_Lean_Syntax_getArg(v___x_1622_, v___x_1600_);
lean_dec(v___x_1622_);
v___x_1637_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1603_);
lean_dec(v___x_1608_);
v___x_1638_ = l_Lean_Syntax_isNone(v___x_1637_);
if (v___x_1638_ == 0)
{
uint8_t v___x_1639_; 
lean_inc(v___x_1637_);
v___x_1639_ = l_Lean_Syntax_matchesNull(v___x_1637_, v___x_1603_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_2427__overap_1641_; lean_object* v___x_1642_; 
lean_dec(v___x_1637_);
lean_dec(v___x_1629_);
lean_dec(v_tk_1628_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1640_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2427__overap_1641_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1640_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1642_ = lean_apply_3(v___x_2427__overap_1641_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1642_;
}
else
{
lean_object* v_wds_x3f_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v_wds_x3f_1643_ = l_Lean_Syntax_getArg(v___x_1637_, v___x_1600_);
lean_dec(v___x_1637_);
v___x_1644_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1643_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_2429__overap_1647_; lean_object* v___x_1648_; 
lean_dec(v_wds_x3f_1643_);
lean_dec(v___x_1629_);
lean_dec(v_tk_1628_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1646_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2429__overap_1647_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1646_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1648_ = lean_apply_3(v___x_2429__overap_1647_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; 
lean_dec_ref_known(v___x_1593_, 2);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_wds_x3f_1643_);
v_wds_x3f_1631_ = v___x_1649_;
v___y_1632_ = v_a_1432_;
v___y_1633_ = v_a_1433_;
goto v___jp_1630_;
}
}
}
else
{
lean_object* v___x_1650_; 
lean_dec(v___x_1637_);
lean_dec_ref_known(v___x_1593_, 2);
v___x_1650_ = lean_box(0);
v_wds_x3f_1631_ = v___x_1650_;
v___y_1632_ = v_a_1432_;
v___y_1633_ = v_a_1433_;
goto v___jp_1630_;
}
v___jp_1630_:
{
lean_object* v_fs_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_fs_1634_ = l_Lean_Syntax_getArgs(v___x_1629_);
lean_dec(v___x_1629_);
v___x_1635_ = l_Lean_Syntax_getHeadInfo(v_tk_1628_);
lean_dec(v_tk_1628_);
v___x_1636_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1634_);
lean_dec_ref(v_fs_1634_);
v_whereInfo_1547_ = v___x_1635_;
v_fs_1548_ = v___x_1636_;
v_wds_x3f_1549_ = v_wds_x3f_1631_;
v___y_1550_ = v___y_1632_;
v___y_1551_ = v___y_1633_;
goto v___jp_1546_;
}
}
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1603_);
v___x_1652_ = ((lean_object*)(l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields___closed__0));
lean_inc(v___x_1651_);
v___x_1653_ = l_Lean_Syntax_isOfKind(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_2431__overap_1655_; lean_object* v___x_1656_; 
lean_dec(v___x_1651_);
lean_dec(v___x_1608_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1654_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2431__overap_1655_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1654_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1656_ = lean_apply_3(v___x_2431__overap_1655_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1656_;
}
else
{
lean_object* v_tk_1657_; lean_object* v___x_1658_; lean_object* v_wds_x3f_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_tk_1657_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1600_);
v___x_1658_ = l_Lean_Syntax_getArg(v___x_1651_, v___x_1600_);
lean_dec(v___x_1651_);
v___x_1666_ = lean_unsigned_to_nat(2u);
v___x_1667_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1666_);
lean_dec(v___x_1608_);
v___x_1668_ = l_Lean_Syntax_isNone(v___x_1667_);
if (v___x_1668_ == 0)
{
uint8_t v___x_1669_; 
lean_inc(v___x_1667_);
v___x_1669_ = l_Lean_Syntax_matchesNull(v___x_1667_, v___x_1603_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_2434__overap_1671_; lean_object* v___x_1672_; 
lean_dec(v___x_1667_);
lean_dec(v___x_1658_);
lean_dec(v_tk_1657_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1670_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2434__overap_1671_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1670_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1672_ = lean_apply_3(v___x_2434__overap_1671_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1672_;
}
else
{
lean_object* v_wds_x3f_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_wds_x3f_1673_ = l_Lean_Syntax_getArg(v___x_1667_, v___x_1600_);
lean_dec(v___x_1667_);
v___x_1674_ = ((lean_object*)(l_Lake_DSL_declValDo___closed__12));
lean_inc(v_wds_x3f_1673_);
v___x_1675_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_2436__overap_1677_; lean_object* v___x_1678_; 
lean_dec(v_wds_x3f_1673_);
lean_dec(v___x_1658_);
lean_dec(v_tk_1657_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
lean_dec(v_tyName_1427_);
v___x_1676_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__15, &l_Lake_DSL_elabConfig___closed__15_once, _init_l_Lake_DSL_elabConfig___closed__15);
v___x_2436__overap_1677_ = l_Lean_throwErrorAt___redArg(v___x_1593_, v___x_1594_, v_config_1431_, v___x_1676_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
v___x_1678_ = lean_apply_3(v___x_2436__overap_1677_, v_a_1432_, v_a_1433_, lean_box(0));
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; 
lean_dec_ref_known(v___x_1593_, 2);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_wds_x3f_1673_);
v_wds_x3f_1660_ = v___x_1679_;
v___y_1661_ = v_a_1432_;
v___y_1662_ = v_a_1433_;
goto v___jp_1659_;
}
}
}
else
{
lean_object* v___x_1680_; 
lean_dec(v___x_1667_);
lean_dec_ref_known(v___x_1593_, 2);
v___x_1680_ = lean_box(0);
v_wds_x3f_1660_ = v___x_1680_;
v___y_1661_ = v_a_1432_;
v___y_1662_ = v_a_1433_;
goto v___jp_1659_;
}
v___jp_1659_:
{
lean_object* v_fs_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_fs_1663_ = l_Lean_Syntax_getArgs(v___x_1658_);
lean_dec(v___x_1658_);
v___x_1664_ = l_Lean_Syntax_getHeadInfo(v_tk_1657_);
lean_dec(v_tk_1657_);
v___x_1665_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_1663_);
lean_dec_ref(v_fs_1663_);
v_whereInfo_1547_ = v___x_1664_;
v_fs_1548_ = v___x_1665_;
v_wds_x3f_1549_ = v_wds_x3f_1660_;
v___y_1550_ = v___y_1661_;
v___y_1551_ = v___y_1662_;
goto v___jp_1546_;
}
}
}
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v___x_1601_);
lean_dec_ref_known(v___x_1593_, 2);
v___x_1681_ = lean_box(2);
v___x_1682_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
v___x_1683_ = lean_box(0);
v_whereInfo_1547_ = v___x_1681_;
v_fs_1548_ = v___x_1682_;
v_wds_x3f_1549_ = v___x_1683_;
v___y_1550_ = v_a_1432_;
v___y_1551_ = v_a_1433_;
goto v___jp_1546_;
}
}
v___jp_1435_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1444_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__0));
lean_inc_ref_n(v___y_1441_, 5);
lean_inc_ref_n(v___y_1443_, 6);
lean_inc_ref_n(v___y_1439_, 6);
v___x_1445_ = l_Lean_Name_mkStr4(v___y_1439_, v___y_1443_, v___y_1441_, v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__1));
v___x_1447_ = l_Lean_Name_mkStr4(v___y_1439_, v___y_1443_, v___y_1441_, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__28));
v___x_1449_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields_spec__4___redArg___closed__5);
lean_inc_n(v___y_1437_, 8);
v___x_1450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1450_, 0, v___y_1437_);
lean_ctor_set(v___x_1450_, 1, v___x_1448_);
lean_ctor_set(v___x_1450_, 2, v___x_1449_);
lean_inc_ref_n(v___x_1450_, 8);
v___x_1451_ = l_Lean_Syntax_node7(v___y_1437_, v___x_1447_, v___x_1450_, v___x_1450_, v___x_1450_, v___x_1450_, v___x_1450_, v___x_1450_, v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__2));
v___x_1453_ = l_Lean_Name_mkStr4(v___y_1439_, v___y_1443_, v___y_1441_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__3));
v___x_1455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___y_1437_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__4));
v___x_1457_ = l_Lean_Name_mkStr4(v___y_1439_, v___y_1443_, v___y_1441_, v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__5));
lean_inc_n(v___y_1436_, 2);
v___x_1459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1459_, 0, v___y_1436_);
lean_ctor_set(v___x_1459_, 1, v___x_1448_);
lean_ctor_set(v___x_1459_, 2, v___x_1458_);
v___x_1460_ = lean_unsigned_to_nat(2u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1460_);
v___x_1462_ = lean_array_push(v___x_1461_, v_id_1429_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1459_);
v___x_1464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___y_1436_);
lean_ctor_set(v___x_1464_, 1, v___x_1457_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__5));
v___x_1466_ = l_Lean_Name_mkStr4(v___y_1439_, v___y_1443_, v___y_1441_, v___x_1465_);
v___x_1467_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__2));
v___x_1468_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__2));
v___x_1469_ = l_Lean_Name_mkStr4(v___y_1439_, v___y_1443_, v___x_1467_, v___x_1468_);
v___x_1470_ = ((lean_object*)(l_Lake_DSL_expandOptSimpleBinder___closed__26));
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1437_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_Syntax_node2(v___y_1437_, v___x_1469_, v___x_1471_, v_ty_1430_);
v___x_1473_ = l_Lean_Syntax_node1(v___y_1437_, v___x_1448_, v___x_1472_);
v___x_1474_ = l_Lean_Syntax_node2(v___y_1437_, v___x_1466_, v___x_1450_, v___x_1473_);
v___x_1475_ = l_Lean_Syntax_node5(v___y_1437_, v___x_1453_, v___x_1455_, v___x_1464_, v___x_1474_, v___y_1442_, v___x_1450_);
v___x_1476_ = l_Lean_Syntax_node2(v___y_1437_, v___x_1445_, v___x_1451_, v___x_1475_);
lean_inc(v___x_1476_);
v___x_1477_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_1477_, 0, v___x_1476_);
v___x_1478_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_1431_, v___x_1476_, v___x_1477_, v___y_1440_, v___y_1438_);
return v___x_1478_;
}
v___jp_1479_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1489_ = l_Lean_mkOptionalNode(v___y_1488_);
v___x_1490_ = lean_unsigned_to_nat(3u);
v___x_1491_ = lean_mk_empty_array_with_capacity(v___x_1490_);
v___x_1492_ = lean_array_push(v___x_1491_, v___y_1484_);
v___x_1493_ = lean_array_push(v___x_1492_, v___y_1482_);
v___x_1494_ = lean_array_push(v___x_1493_, v___x_1489_);
v___x_1495_ = lean_box(2);
lean_inc(v___y_1480_);
v___x_1496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___y_1480_);
lean_ctor_set(v___x_1496_, 2, v___x_1494_);
v___x_1497_ = l_Lean_Elab_Command_getRef___redArg(v___y_1486_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = 0;
v___x_1500_ = l_Lean_SourceInfo_fromRef(v_a_1498_, v___x_1499_);
lean_dec(v_a_1498_);
v___x_1501_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1486_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1502_; lean_object* v_toApplicative_1503_; lean_object* v_toFunctor_1504_; lean_object* v_toSeq_1505_; lean_object* v_toSeqLeft_1506_; lean_object* v_toSeqRight_1507_; lean_object* v___f_1508_; lean_object* v___f_1509_; lean_object* v___f_1510_; lean_object* v___f_1511_; lean_object* v___x_1512_; lean_object* v___f_1513_; lean_object* v___f_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_quotContext_x3f_1519_; 
lean_dec_ref_known(v___x_1501_, 1);
v___x_1502_ = lean_obj_once(&l_Lake_DSL_elabConfig___closed__7, &l_Lake_DSL_elabConfig___closed__7_once, _init_l_Lake_DSL_elabConfig___closed__7);
v_toApplicative_1503_ = lean_ctor_get(v___x_1502_, 0);
v_toFunctor_1504_ = lean_ctor_get(v_toApplicative_1503_, 0);
v_toSeq_1505_ = lean_ctor_get(v_toApplicative_1503_, 2);
v_toSeqLeft_1506_ = lean_ctor_get(v_toApplicative_1503_, 3);
v_toSeqRight_1507_ = lean_ctor_get(v_toApplicative_1503_, 4);
v___f_1508_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__8));
v___f_1509_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__9));
lean_inc_ref_n(v_toFunctor_1504_, 2);
v___f_1510_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1510_, 0, v_toFunctor_1504_);
v___f_1511_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1511_, 0, v_toFunctor_1504_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___f_1510_);
lean_ctor_set(v___x_1512_, 1, v___f_1511_);
lean_inc(v_toSeqRight_1507_);
v___f_1513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1513_, 0, v_toSeqRight_1507_);
lean_inc(v_toSeqLeft_1506_);
v___f_1514_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1514_, 0, v_toSeqLeft_1506_);
lean_inc(v_toSeq_1505_);
v___f_1515_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1515_, 0, v_toSeq_1505_);
v___x_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1512_);
lean_ctor_set(v___x_1516_, 1, v___f_1508_);
lean_ctor_set(v___x_1516_, 2, v___f_1515_);
lean_ctor_set(v___x_1516_, 3, v___f_1514_);
lean_ctor_set(v___x_1516_, 4, v___f_1513_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___f_1509_);
v___x_1518_ = l_Lean_Elab_Command_instMonadEnvCommandElabM;
v_quotContext_x3f_1519_ = lean_ctor_get(v___y_1486_, 5);
if (lean_obj_tag(v_quotContext_x3f_1519_) == 0)
{
lean_object* v___x_2402__overap_1520_; lean_object* v___x_1521_; 
v___x_2402__overap_1520_ = l_Lean_getMainModule___redArg(v___x_1517_, v___x_1518_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1486_);
v___x_1521_ = lean_apply_3(v___x_2402__overap_1520_, v___y_1486_, v___y_1481_, lean_box(0));
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_dec_ref_known(v___x_1521_, 1);
v___y_1436_ = v___x_1495_;
v___y_1437_ = v___x_1500_;
v___y_1438_ = v___y_1481_;
v___y_1439_ = v___y_1483_;
v___y_1440_ = v___y_1486_;
v___y_1441_ = v___y_1485_;
v___y_1442_ = v___x_1496_;
v___y_1443_ = v___y_1487_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v___x_1500_);
lean_dec_ref_known(v___x_1496_, 3);
lean_dec(v_config_1431_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1517_, 2);
v___y_1436_ = v___x_1495_;
v___y_1437_ = v___x_1500_;
v___y_1438_ = v___y_1481_;
v___y_1439_ = v___y_1483_;
v___y_1440_ = v___y_1486_;
v___y_1441_ = v___y_1485_;
v___y_1442_ = v___x_1496_;
v___y_1443_ = v___y_1487_;
goto v___jp_1435_;
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v___x_1500_);
lean_dec_ref_known(v___x_1496_, 3);
lean_dec(v_config_1431_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
v_a_1530_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1501_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1501_);
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
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref_known(v___x_1496_, 3);
lean_dec(v_config_1431_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
v_a_1538_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1497_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1497_);
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
v___jp_1546_:
{
lean_object* v_fieldMap_1552_; lean_object* v___x_1553_; lean_object* v_whereTk_1554_; lean_object* v___x_1555_; 
v_fieldMap_1552_ = lean_ctor_get(v_info_1428_, 1);
v___x_1553_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__10));
v_whereTk_1554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_1554_, 0, v_whereInfo_1547_);
lean_ctor_set(v_whereTk_1554_, 1, v___x_1553_);
v___x_1555_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_1427_, v_fieldMap_1552_, v_fs_1548_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_fs_1548_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__0));
v___x_1558_ = ((lean_object*)(l_Lake_DSL_expandAttrs___closed__1));
v___x_1559_ = ((lean_object*)(l_Lake_DSL_simpleDeclSig___closed__6));
v___x_1560_ = ((lean_object*)(l_Lake_DSL_elabConfig___closed__12));
if (lean_obj_tag(v_wds_x3f_1549_) == 0)
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_box(0);
v___y_1480_ = v___x_1560_;
v___y_1481_ = v___y_1551_;
v___y_1482_ = v_a_1556_;
v___y_1483_ = v___x_1557_;
v___y_1484_ = v_whereTk_1554_;
v___y_1485_ = v___x_1559_;
v___y_1486_ = v___y_1550_;
v___y_1487_ = v___x_1558_;
v___y_1488_ = v___x_1561_;
goto v___jp_1479_;
}
else
{
lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
v_val_1562_ = lean_ctor_get(v_wds_x3f_1549_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_wds_x3f_1549_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v_wds_x3f_1549_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_dec(v_wds_x3f_1549_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_val_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
v___y_1480_ = v___x_1560_;
v___y_1481_ = v___y_1551_;
v___y_1482_ = v_a_1556_;
v___y_1483_ = v___x_1557_;
v___y_1484_ = v_whereTk_1554_;
v___y_1485_ = v___x_1559_;
v___y_1486_ = v___y_1550_;
v___y_1487_ = v___x_1558_;
v___y_1488_ = v___x_1567_;
goto v___jp_1479_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref_known(v_whereTk_1554_, 2);
lean_dec(v_wds_x3f_1549_);
lean_dec(v_config_1431_);
lean_dec(v_ty_1430_);
lean_dec(v_id_1429_);
v_a_1570_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1555_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1555_);
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
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object* v_tyName_1684_, lean_object* v_info_1685_, lean_object* v_id_1686_, lean_object* v_ty_1687_, lean_object* v_config_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lake_DSL_elabConfig(v_tyName_1684_, v_info_1685_, v_id_1686_, v_ty_1687_, v_config_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec_ref(v_info_1685_);
return v_res_1692_;
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
