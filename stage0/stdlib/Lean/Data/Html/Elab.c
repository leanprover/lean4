// Lean compiler output
// Module: Lean.Data.Html.Elab
// Imports: public meta import Init.Data.String.Modify public meta import Lean.Data.Html.Syntax public meta import Lean.Elab.Term import Lean.Data.Html.Basic
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t l_Lean_Html_isVoidElement(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Html_Syntax_decodeCharacterReferences(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Html_Syntax_TextCommentsView_getSyntax(lean_object*);
lean_object* l_Lean_Html_Syntax_TextCommentsView_getText(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value;
static const lean_string_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Html"};
static const lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value;
static const lean_string_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "element"};
static const lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 57, 84, 135, 110, 77, 53, 20)}};
static const lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4_value;
static const lean_array_object l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_Element_checkNamesMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Replace with start tag"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__0_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1;
static const lean_string_object l_Lean_Html_Syntax_Element_checkNamesMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Mismatched end tag, expected `"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3;
static const lean_string_object l_Lean_Html_Syntax_Element_checkNamesMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` but got `"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__4_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5;
static const lean_string_object l_Lean_Html_Syntax_Element_checkNamesMatch___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__6_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Void element `"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__0_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1;
static const lean_string_object l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` cannot have children or an end tag"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__2_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3;
static const lean_string_object l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/>"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__4 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__4_value;
static const lean_string_object l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Make it self-closing"};
static const lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__5 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__5_value;
static const lean_ctor_object l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__5_value)}};
static const lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__6 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__6_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7;
static const lean_string_object l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8 = (const lean_object*)&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8_value;
static lean_once_cell_t l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "interp"};
static const lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 205, 174, 42, 121, 171, 225, 181)}};
static const lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1_value;
static const lean_string_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "interpMany"};
static const lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__2 = (const lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__2_value;
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 8, 45, 111, 253, 122, 157, 183)}};
static const lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3 = (const lean_object*)&l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrName"};
static const lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 74, 103, 252, 182, 26, 187, 163)}};
static const lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__7 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__7_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__11 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__11_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__16 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__16_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__17 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__17_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__18 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__18_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__16_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__17_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__18_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ForIn.toArray"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__22 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__22_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__23 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__23_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__22_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__23_value),LEAN_SCALAR_PTR_LITERAL(3, 252, 72, 244, 54, 203, 98, 113)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__25 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__25_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__27 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__27_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__16_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__17_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__27_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "term_×_"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__34 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__34_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__34_value),LEAN_SCALAR_PTR_LITERAL(45, 89, 233, 57, 172, 127, 134, 63)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__37 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__37_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__38_value_aux_0),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 111, 143, 134, 134, 69, 118, 12)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__38 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__38_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__38_value)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__39 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__39_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__40 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__40_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__39_value),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__40_value)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__41 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__41_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__37_value),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__41_value)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "×"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__45 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__45_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__45_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "push"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 153, 248, 33, 206, 118, 72, 33)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 158, 104, 153, 219, 225, 201, 192)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 216, 1, 122, 187, 158, 244, 211)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "comment"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 54, 202, 118, 199, 75, 185, 39)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__0 = (const lean_object*)&l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__0_value),((lean_object*)&l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__0_value)}};
static const lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1 = (const lean_object*)&l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofArray"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__1_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 154, 81, 219, 71, 112, 39, 96)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3;
static const lean_string_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "empty"};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__4 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__4_value;
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 213, 175, 81, 170, 125, 252, 200)}};
static const lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5 = (const lean_object*)&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5_value;
static lean_once_cell_t l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 132, 38, 126, 255, 196, 59, 29)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 210, 74, 251, 7, 54, 231, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofCollection"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 101, 33, 160, 88, 74, 41, 14)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 125, 219, 152, 153, 142, 178, 202)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Html.ofCollection"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 71, 43, 183, 83, 210, 150, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "html%"};
static const lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 150, 207, 200, 122, 44, 247, 128)}};
static const lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(64, 220, 71, 125, 15, 201, 233, 195)}};
static const lean_ctor_object l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 105, 154, 121, 168, 129, 109, 37)}};
static const lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(lean_object* v_s_1_, lean_object* v_p_2_){
_start:
{
lean_object* v___y_4_; lean_object* v___y_5_; uint32_t v___y_9_; lean_object* v___x_21_; uint8_t v_decide_22_; 
v___x_21_ = lean_string_utf8_byte_size(v_s_1_);
v_decide_22_ = lean_nat_dec_eq(v_p_2_, v___x_21_);
if (v_decide_22_ == 0)
{
uint32_t v___x_23_; uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_23_ = lean_string_utf8_get_fast(v_s_1_, v_p_2_);
v___x_24_ = 65;
v___x_25_ = lean_uint32_dec_le(v___x_24_, v___x_23_);
if (v___x_25_ == 0)
{
v___y_9_ = v___x_23_;
goto v___jp_8_;
}
else
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 90;
v___x_27_ = lean_uint32_dec_le(v___x_23_, v___x_26_);
if (v___x_27_ == 0)
{
v___y_9_ = v___x_23_;
goto v___jp_8_;
}
else
{
uint32_t v___x_28_; uint32_t v___x_29_; 
v___x_28_ = 32;
v___x_29_ = lean_uint32_add(v___x_23_, v___x_28_);
v___y_9_ = v___x_29_;
goto v___jp_8_;
}
}
}
else
{
lean_dec(v_p_2_);
return v_s_1_;
}
v___jp_3_:
{
lean_object* v___x_6_; 
v___x_6_ = lean_nat_add(v_p_2_, v___y_5_);
lean_dec(v_p_2_);
v_s_1_ = v___y_4_;
v_p_2_ = v___x_6_;
goto _start;
}
v___jp_8_:
{
lean_object* v___x_10_; uint32_t v___x_11_; uint8_t v___x_12_; 
lean_inc(v_p_2_);
v___x_10_ = lean_string_utf8_set(v_s_1_, v_p_2_, v___y_9_);
v___x_11_ = 127;
v___x_12_ = lean_uint32_dec_le(v___y_9_, v___x_11_);
if (v___x_12_ == 0)
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 2047;
v___x_14_ = lean_uint32_dec_le(v___y_9_, v___x_13_);
if (v___x_14_ == 0)
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 65535;
v___x_16_ = lean_uint32_dec_le(v___y_9_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(4u);
v___y_4_ = v___x_10_;
v___y_5_ = v___x_17_;
goto v___jp_3_;
}
else
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(3u);
v___y_4_ = v___x_10_;
v___y_5_ = v___x_18_;
goto v___jp_3_;
}
}
else
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(2u);
v___y_4_ = v___x_10_;
v___y_5_ = v___x_19_;
goto v___jp_3_;
}
}
else
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(1u);
v___y_4_ = v___x_10_;
v___y_5_ = v___x_20_;
goto v___jp_3_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box(0);
v___x_31_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___boxed(lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(size_t v_sz_38_, size_t v_i_39_, lean_object* v_bs_40_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = lean_usize_dec_lt(v_i_39_, v_sz_38_);
if (v___x_41_ == 0)
{
return v_bs_40_;
}
else
{
lean_object* v_v_42_; lean_object* v___x_43_; lean_object* v_bs_x27_44_; size_t v___x_45_; size_t v___x_46_; lean_object* v___x_47_; 
v_v_42_ = lean_array_uget(v_bs_40_, v_i_39_);
v___x_43_ = lean_unsigned_to_nat(0u);
v_bs_x27_44_ = lean_array_uset(v_bs_40_, v_i_39_, v___x_43_);
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_add(v_i_39_, v___x_45_);
v___x_47_ = lean_array_uset(v_bs_x27_44_, v_i_39_, v_v_42_);
v_i_39_ = v___x_46_;
v_bs_40_ = v___x_47_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1___boxed(lean_object* v_sz_49_, lean_object* v_i_50_, lean_object* v_bs_51_){
_start:
{
size_t v_sz_boxed_52_; size_t v_i_boxed_53_; lean_object* v_res_54_; 
v_sz_boxed_52_ = lean_unbox_usize(v_sz_49_);
lean_dec(v_sz_49_);
v_i_boxed_53_ = lean_unbox_usize(v_i_50_);
lean_dec(v_i_50_);
v_res_54_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_boxed_52_, v_i_boxed_53_, v_bs_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(lean_object* v_stx_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
lean_inc(v_stx_66_);
v___x_70_ = l_Lean_Syntax_getKind(v_stx_66_);
v___x_71_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_72_ = lean_name_eq(v___x_70_, v___x_71_);
lean_dec(v___x_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec(v_stx_66_);
v___x_73_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; size_t v_sz_77_; size_t v___x_78_; lean_object* v_attrs_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_startTag_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_74_);
v___x_76_ = l_Lean_Syntax_getArgs(v___x_75_);
lean_dec(v___x_75_);
v_sz_77_ = lean_array_size(v___x_76_);
v___x_78_ = ((size_t)0ULL);
v_attrs_79_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_77_, v___x_78_, v___x_76_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_82_);
v___x_84_ = lean_unsigned_to_nat(3u);
v___x_85_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_84_);
v_startTag_86_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_86_, 0, v___x_81_);
lean_ctor_set(v_startTag_86_, 1, v___x_83_);
lean_ctor_set(v_startTag_86_, 2, v_attrs_79_);
lean_ctor_set(v_startTag_86_, 3, v___x_85_);
v___x_87_ = l_Lean_Syntax_getNumArgs(v_stx_66_);
v___x_88_ = lean_unsigned_to_nat(4u);
v___x_89_ = lean_nat_dec_eq(v___x_87_, v___x_88_);
lean_dec(v___x_87_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_endTag_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_90_ = lean_unsigned_to_nat(5u);
v___x_91_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(6u);
v___x_93_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_92_);
v___x_94_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5));
v___x_95_ = lean_unsigned_to_nat(7u);
v___x_96_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_95_);
v_endTag_97_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_97_, 0, v___x_91_);
lean_ctor_set(v_endTag_97_, 1, v___x_93_);
lean_ctor_set(v_endTag_97_, 2, v___x_94_);
lean_ctor_set(v_endTag_97_, 3, v___x_96_);
v___x_98_ = l_Lean_Syntax_getArg(v_stx_66_, v___x_88_);
lean_dec(v_stx_66_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_endTag_97_);
v___x_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_101_, 0, v_startTag_86_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_stx_66_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v_startTag_86_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___boxed(lean_object* v_stx_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_110_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_111_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
lean_ctor_set(v___x_116_, 2, v___x_115_);
lean_ctor_set(v___x_116_, 3, v___x_115_);
lean_ctor_set(v___x_116_, 4, v___x_114_);
lean_ctor_set(v___x_116_, 5, v___x_114_);
lean_ctor_set(v___x_116_, 6, v___x_114_);
lean_ctor_set(v___x_116_, 7, v___x_114_);
lean_ctor_set(v___x_116_, 8, v___x_114_);
lean_ctor_set(v___x_116_, 9, v___x_114_);
lean_ctor_set(v___x_116_, 10, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_unsigned_to_nat(32u);
v___x_118_ = lean_mk_empty_array_with_capacity(v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4(void){
_start:
{
size_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_120_ = ((size_t)5ULL);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_unsigned_to_nat(32u);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
v___x_124_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3);
v___x_125_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
lean_ctor_set(v___x_125_, 2, v___x_121_);
lean_ctor_set(v___x_125_, 3, v___x_121_);
lean_ctor_set_usize(v___x_125_, 4, v___x_120_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_box(1);
v___x_127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4);
v___x_128_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(lean_object* v_msgData_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_toCold_135_; lean_object* v_env_136_; lean_object* v_options_137_; uint8_t v___x_138_; lean_object* v_env_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_134_ = lean_st_ref_get(v___y_132_);
v_toCold_135_ = lean_ctor_get(v___y_131_, 0);
v_env_136_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_env_136_);
lean_dec(v___x_134_);
v_options_137_ = lean_ctor_get(v_toCold_135_, 2);
v___x_138_ = 0;
v_env_139_ = l_Lean_Environment_setRecordingDeps(v_env_136_, v___x_138_);
v___x_140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2);
v___x_141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5);
lean_inc_ref(v_options_137_);
v___x_142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_142_, 0, v_env_139_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
lean_ctor_set(v___x_142_, 2, v___x_141_);
lean_ctor_set(v___x_142_, 3, v_options_137_);
v___x_143_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_msgData_130_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___boxed(lean_object* v_msgData_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(v_msgData_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(lean_object* v_msg_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_ref_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_ref_154_ = lean_ctor_get(v___y_151_, 2);
v___x_155_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(v_msg_150_, v___y_151_, v___y_152_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_inc(v_ref_154_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_ref_154_);
lean_ctor_set(v___x_160_, 1, v_a_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 1);
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg___boxed(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(lean_object* v_ref_170_, lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_toCold_175_; lean_object* v_currRecDepth_176_; lean_object* v_ref_177_; uint16_t v_optionFlags_178_; uint8_t v_suppressElabErrors_179_; uint8_t v_checkDeprecated_180_; uint8_t v_isRecordingDeps_181_; lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_toCold_175_ = lean_ctor_get(v___y_172_, 0);
v_currRecDepth_176_ = lean_ctor_get(v___y_172_, 1);
v_ref_177_ = lean_ctor_get(v___y_172_, 2);
v_optionFlags_178_ = lean_ctor_get_uint16(v___y_172_, sizeof(void*)*3);
v_suppressElabErrors_179_ = lean_ctor_get_uint8(v___y_172_, sizeof(void*)*3 + 2);
v_checkDeprecated_180_ = lean_ctor_get_uint8(v___y_172_, sizeof(void*)*3 + 3);
v_isRecordingDeps_181_ = lean_ctor_get_uint8(v___y_172_, sizeof(void*)*3 + 4);
v_ref_182_ = l_Lean_replaceRef(v_ref_170_, v_ref_177_);
lean_inc(v_currRecDepth_176_);
lean_inc_ref(v_toCold_175_);
v___x_183_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_183_, 0, v_toCold_175_);
lean_ctor_set(v___x_183_, 1, v_currRecDepth_176_);
lean_ctor_set(v___x_183_, 2, v_ref_182_);
lean_ctor_set_uint16(v___x_183_, sizeof(void*)*3, v_optionFlags_178_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3 + 2, v_suppressElabErrors_179_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3 + 3, v_checkDeprecated_180_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3 + 4, v_isRecordingDeps_181_);
v___x_184_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_171_, v___x_183_, v___y_173_);
lean_dec_ref_known(v___x_183_, 3);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg___boxed(lean_object* v_ref_185_, lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_ref_185_, v_msg_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v_ref_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(lean_object* v_x_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
if (lean_obj_tag(v_x_191_) == 1)
{
lean_object* v_args_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_args_195_ = lean_ctor_get(v_x_191_, 2);
v___x_196_ = lean_array_get_size(v_args_195_);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_dec_eq(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_199_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_array_fget_borrowed(v_args_195_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 2)
{
lean_object* v_val_202_; lean_object* v___x_203_; 
v_val_202_ = lean_ctor_get(v___x_201_, 1);
lean_inc_ref(v_val_202_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_val_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_204_;
}
}
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg___boxed(lean_object* v_x_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_x_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v_x_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(lean_object* v_a_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_a_211_, v___y_212_, v___y_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1___boxed(lean_object* v_a_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(v_a_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v_a_216_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__0));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__2));
v___x_226_ = l_Lean_stringToMessageData(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__4));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__6));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch(lean_object* v_stx_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_320_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_320_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_320_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_320_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_endTag_x3f_242_; 
v_endTag_x3f_242_ = lean_ctor_get(v_a_238_, 2);
lean_inc(v_endTag_x3f_242_);
if (lean_obj_tag(v_endTag_x3f_242_) == 1)
{
lean_object* v_startTag_243_; lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_240_);
v_startTag_243_ = lean_ctor_get(v_a_238_, 0);
lean_inc_ref(v_startTag_243_);
lean_dec(v_a_238_);
v_val_244_ = lean_ctor_get(v_endTag_x3f_242_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_endTag_x3f_242_);
if (v_isSharedCheck_315_ == 0)
{
v___x_246_ = v_endTag_x3f_242_;
v_isShared_247_ = v_isSharedCheck_315_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v_endTag_x3f_242_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_315_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_name_248_; lean_object* v___x_249_; 
v_name_248_ = lean_ctor_get(v_startTag_243_, 1);
lean_inc(v_name_248_);
lean_dec_ref(v_startTag_243_);
v___x_249_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_248_, v_a_234_, v_a_235_);
lean_dec(v_name_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v_name_251_; lean_object* v___x_252_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v_name_251_ = lean_ctor_get(v_val_244_, 1);
lean_inc(v_name_251_);
lean_dec(v_val_244_);
v___x_252_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_251_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_298_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_298_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_298_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_298_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_257_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_253_);
v___x_258_ = l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(v_a_253_, v___x_257_);
lean_inc(v_a_250_);
v___x_259_ = l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(v_a_250_, v___x_257_);
v___x_260_ = lean_string_dec_eq(v___x_258_, v___x_259_);
lean_dec_ref(v___x_259_);
lean_dec_ref(v___x_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
lean_del_object(v___x_255_);
v___x_261_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1);
lean_inc(v_a_250_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v_a_250_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_ctor_set(v___x_264_, 2, v___x_263_);
lean_ctor_set(v___x_264_, 3, v___x_263_);
lean_ctor_set(v___x_264_, 4, v___x_263_);
lean_ctor_set(v___x_264_, 5, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_263_);
lean_ctor_set(v___x_266_, 2, v___x_263_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*3, v___x_265_);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_mk_empty_array_with_capacity(v___x_267_);
v___x_269_ = lean_array_push(v___x_268_, v___x_266_);
lean_inc(v_name_251_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v_name_251_);
v___x_271_ = v___x_246_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_name_251_);
v___x_271_ = v_reuseFailAlloc_293_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_MessageData_hint(v___x_261_, v___x_269_, v___x_271_, v___x_263_, v___x_260_, v_a_234_, v_a_235_);
lean_dec_ref(v___x_269_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
v___x_274_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3);
v___x_275_ = l_Lean_stringToMessageData(v_a_250_);
v___x_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_stringToMessageData(v_a_253_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_a_273_);
v___x_284_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_name_251_, v___x_283_, v_a_234_, v_a_235_);
lean_dec(v_name_251_);
return v___x_284_;
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v_a_253_);
lean_dec(v_name_251_);
lean_dec(v_a_250_);
v_a_285_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_272_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_272_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec(v_a_253_);
lean_dec(v_name_251_);
lean_dec(v_a_250_);
lean_del_object(v___x_246_);
v___x_294_ = lean_box(0);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_294_);
v___x_296_ = v___x_255_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
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
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_name_251_);
lean_dec(v_a_250_);
lean_del_object(v___x_246_);
v_a_299_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_252_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_252_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
v_a_307_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_249_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_249_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v_endTag_x3f_242_);
lean_dec(v_a_238_);
v___x_316_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_316_);
v___x_318_ = v___x_240_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
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
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_237_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_237_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___boxed(lean_object* v_stx_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(lean_object* v_00_u03b1_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b1_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(v_00_u03b1_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(lean_object* v_00_u03b1_344_, lean_object* v_ref_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_ref_345_, v_msg_346_, v___y_347_, v___y_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___boxed(lean_object* v_00_u03b1_351_, lean_object* v_ref_352_, lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(v_00_u03b1_351_, v_ref_352_, v_msg_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v_ref_352_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3(lean_object* v_k_358_, lean_object* v_x_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_x_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___boxed(lean_object* v_k_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3(v_k_364_, v_x_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v_x_365_);
lean_dec(v_k_364_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___boxed(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6(v_00_u03b1_376_, v_msg_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_381_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__0));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__2));
v___x_387_ = l_Lean_stringToMessageData(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__6));
v___x_393_ = l_Lean_MessageData_ofFormat(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren(lean_object* v_stx_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
lean_inc(v_stx_397_);
v___x_401_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_490_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_490_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_490_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_490_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_children_x3f_406_; 
v_children_x3f_406_ = lean_ctor_get(v_a_402_, 1);
if (lean_obj_tag(v_children_x3f_406_) == 1)
{
lean_object* v_startTag_407_; lean_object* v_lt_408_; lean_object* v_name_409_; lean_object* v_gt_410_; lean_object* v___x_411_; 
lean_del_object(v___x_404_);
v_startTag_407_ = lean_ctor_get(v_a_402_, 0);
lean_inc_ref(v_startTag_407_);
lean_dec(v_a_402_);
v_lt_408_ = lean_ctor_get(v_startTag_407_, 0);
lean_inc(v_lt_408_);
v_name_409_ = lean_ctor_get(v_startTag_407_, 1);
lean_inc(v_name_409_);
v_gt_410_ = lean_ctor_get(v_startTag_407_, 3);
lean_inc(v_gt_410_);
lean_dec_ref(v_startTag_407_);
v___x_411_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_409_, v_a_398_, v_a_399_);
lean_dec(v_name_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_477_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_477_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_477_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_477_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_hint_417_; lean_object* v___y_418_; lean_object* v___y_419_; uint8_t v___x_427_; 
lean_inc(v_a_412_);
v___x_427_ = l_Lean_Html_isVoidElement(v_a_412_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_dec(v_a_412_);
lean_dec(v_gt_410_);
lean_dec(v_lt_408_);
lean_dec(v_stx_397_);
v___x_428_ = lean_box(0);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_428_);
v___x_430_ = v___x_414_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
uint8_t v___x_432_; lean_object* v___x_433_; 
lean_del_object(v___x_414_);
v___x_432_ = 0;
v___x_433_ = l_Lean_Syntax_getPos_x3f(v_lt_408_, v___x_432_);
lean_dec(v_lt_408_);
if (lean_obj_tag(v___x_433_) == 1)
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_475_; 
v_val_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_475_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_475_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_475_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Syntax_getPos_x3f(v_gt_410_, v___x_432_);
lean_dec(v_gt_410_);
if (lean_obj_tag(v___x_438_) == 1)
{
lean_object* v_toCold_439_; lean_object* v_fileMap_440_; lean_object* v_val_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_473_; 
v_toCold_439_ = lean_ctor_get(v_a_398_, 0);
v_fileMap_440_ = lean_ctor_get(v_toCold_439_, 1);
v_val_441_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_473_ == 0)
{
v___x_443_ = v___x_438_;
v_isShared_444_ = v_isSharedCheck_473_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_val_441_);
lean_dec(v___x_438_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_473_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_source_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v_source_445_ = lean_ctor_get(v_fileMap_440_, 0);
v___x_446_ = lean_string_utf8_extract(v_source_445_, v_val_434_, v_val_441_);
lean_dec(v_val_441_);
lean_dec(v_val_434_);
v___x_447_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__4));
v___x_448_ = lean_string_append(v___x_446_, v___x_447_);
v___x_449_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_448_);
v___x_451_ = v___x_436_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_448_);
v___x_451_ = v_reuseFailAlloc_472_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_452_ = lean_box(0);
v___x_453_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
lean_ctor_set(v___x_453_, 3, v___x_452_);
lean_ctor_set(v___x_453_, 4, v___x_452_);
lean_ctor_set(v___x_453_, 5, v___x_452_);
v___x_454_ = 0;
v___x_455_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_452_);
lean_ctor_set(v___x_455_, 2, v___x_452_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*3, v___x_454_);
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_mk_empty_array_with_capacity(v___x_456_);
v___x_458_ = lean_array_push(v___x_457_, v___x_455_);
lean_inc(v_stx_397_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_stx_397_);
v___x_460_ = v___x_443_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_stx_397_);
v___x_460_ = v_reuseFailAlloc_471_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_MessageData_hint(v___x_449_, v___x_458_, v___x_460_, v___x_452_, v___x_432_, v_a_398_, v_a_399_);
lean_dec_ref(v___x_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v_hint_417_ = v_a_462_;
v___y_418_ = v_a_398_;
v___y_419_ = v_a_399_;
goto v___jp_416_;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_412_);
lean_dec(v_stx_397_);
v_a_463_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_461_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_461_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_474_; 
lean_dec(v___x_438_);
lean_del_object(v___x_436_);
lean_dec(v_val_434_);
v___x_474_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9);
v_hint_417_ = v___x_474_;
v___y_418_ = v_a_398_;
v___y_419_ = v_a_399_;
goto v___jp_416_;
}
}
}
else
{
lean_object* v___x_476_; 
lean_dec(v___x_433_);
lean_dec(v_gt_410_);
v___x_476_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9);
v_hint_417_ = v___x_476_;
v___y_418_ = v_a_398_;
v___y_419_ = v_a_399_;
goto v___jp_416_;
}
}
v___jp_416_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_420_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1);
v___x_421_ = l_Lean_stringToMessageData(v_a_412_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_hint_417_);
v___x_426_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_stx_397_, v___x_425_, v___y_418_, v___y_419_);
lean_dec(v_stx_397_);
return v___x_426_;
}
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v_gt_410_);
lean_dec(v_lt_408_);
lean_dec(v_stx_397_);
v_a_478_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_411_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_411_);
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
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
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
else
{
lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec(v_a_402_);
lean_dec(v_stx_397_);
v___x_486_ = lean_box(0);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_486_);
v___x_488_ = v___x_404_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_stx_397_);
v_a_491_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_401_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_401_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___boxed(lean_object* v_stx_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg___boxed(lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(uint8_t v_isMany_521_, lean_object* v_stx_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; lean_object* v___y_532_; 
lean_inc(v_stx_522_);
v___x_530_ = l_Lean_Syntax_getKind(v_stx_522_);
if (v_isMany_521_ == 0)
{
lean_object* v___x_543_; 
v___x_543_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___y_532_ = v___x_543_;
goto v___jp_531_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___y_532_ = v___x_544_;
goto v___jp_531_;
}
v___jp_531_:
{
uint8_t v___x_533_; 
v___x_533_ = lean_name_eq(v___x_530_, v___y_532_);
lean_dec(v___x_530_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec(v_stx_522_);
v___x_534_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l_Lean_Syntax_getArg(v_stx_522_, v___x_535_);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = l_Lean_Syntax_getArg(v_stx_522_, v___x_537_);
v___x_539_ = lean_unsigned_to_nat(2u);
v___x_540_ = l_Lean_Syntax_getArg(v_stx_522_, v___x_539_);
lean_dec(v_stx_522_);
v___x_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_541_, 0, v___x_536_);
lean_ctor_set(v___x_541_, 1, v___x_538_);
lean_ctor_set(v___x_541_, 2, v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___boxed(lean_object* v_isMany_545_, lean_object* v_stx_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v_isMany_boxed_554_; lean_object* v_res_555_; 
v_isMany_boxed_554_ = lean_unbox(v_isMany_545_);
v_res_555_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_boxed_554_, v_stx_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(lean_object* v_stx_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_c_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v_c_568_ = l_Lean_Syntax_getArg(v_stx_559_, v___x_567_);
lean_inc(v_c_568_);
v___x_569_ = l_Lean_Syntax_getKind(v_c_568_);
v___x_570_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__1));
v___x_571_ = lean_name_eq(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_573_ = lean_name_eq(v___x_569_, v___x_572_);
lean_dec(v___x_569_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v_c_568_);
v___x_574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v_c_568_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v___x_569_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_c_568_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___boxed(lean_object* v_stx_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v_stx_579_);
return v_res_587_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_box(0);
v___x_592_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_593_ = l_Lean_Expr_const___override(v___x_592_, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(lean_object* v_stx_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_toCold_604_; lean_object* v_currRecDepth_605_; lean_object* v_ref_606_; uint16_t v_optionFlags_607_; uint8_t v_suppressElabErrors_608_; uint8_t v_checkDeprecated_609_; uint8_t v_isRecordingDeps_610_; lean_object* v_ref_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_toCold_604_ = lean_ctor_get(v_a_601_, 0);
v_currRecDepth_605_ = lean_ctor_get(v_a_601_, 1);
v_ref_606_ = lean_ctor_get(v_a_601_, 2);
v_optionFlags_607_ = lean_ctor_get_uint16(v_a_601_, sizeof(void*)*3);
v_suppressElabErrors_608_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 2);
v_checkDeprecated_609_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 3);
v_isRecordingDeps_610_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 4);
v_ref_611_ = l_Lean_replaceRef(v_stx_596_, v_ref_606_);
lean_inc(v_currRecDepth_605_);
lean_inc_ref(v_toCold_604_);
v___x_612_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_612_, 0, v_toCold_604_);
lean_ctor_set(v___x_612_, 1, v_currRecDepth_605_);
lean_ctor_set(v___x_612_, 2, v_ref_611_);
lean_ctor_set_uint16(v___x_612_, sizeof(void*)*3, v_optionFlags_607_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*3 + 2, v_suppressElabErrors_608_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*3 + 3, v_checkDeprecated_609_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*3 + 4, v_isRecordingDeps_610_);
v___x_613_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v___x_612_, v_a_602_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
if (lean_obj_tag(v_a_614_) == 0)
{
lean_object* v_stx_615_; lean_object* v___x_616_; 
v_stx_615_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_stx_615_);
lean_dec_ref_known(v_a_614_, 1);
v___x_616_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_stx_615_, v___x_612_, v_a_602_);
lean_dec_ref_known(v___x_612_, 3);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_625_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_625_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = l_Lean_mkStrLit(v_a_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_621_);
v___x_623_ = v___x_619_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_a_626_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_616_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_616_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v_stx_634_; uint8_t v___x_635_; lean_object* v___x_636_; 
v_stx_634_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_stx_634_);
lean_dec_ref_known(v_a_614_, 1);
v___x_635_ = 0;
v___x_636_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v___x_635_, v_stx_634_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v___x_612_, v_a_602_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v_term_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v_term_638_ = lean_ctor_get(v_a_637_, 1);
lean_inc(v_term_638_);
lean_dec(v_a_637_);
v___x_639_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3);
v___x_640_ = 1;
v___x_641_ = lean_box(0);
v___x_642_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_638_, v___x_639_, v___x_640_, v___x_640_, v___x_641_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v___x_612_, v_a_602_);
lean_dec_ref_known(v___x_612_, 3);
return v___x_642_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref_known(v___x_612_, 3);
v_a_643_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_636_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_636_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref_known(v___x_612_, 3);
v_a_651_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_613_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_613_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___boxed(lean_object* v_stx_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_stx_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_stx_659_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(lean_object* v_00_u03b1_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___boxed(lean_object* v_00_u03b1_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(v_00_u03b1_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(lean_object* v_stx_692_){
_start:
{
lean_object* v___x_694_; lean_object* v_c_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v_c_695_ = l_Lean_Syntax_getArg(v_stx_692_, v___x_694_);
lean_inc(v_c_695_);
v___x_696_ = l_Lean_Syntax_getKind(v_c_695_);
v___x_697_ = ((lean_object*)(l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1));
v___x_698_ = lean_name_eq(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_700_ = lean_name_eq(v___x_696_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_702_ = lean_name_eq(v___x_696_, v___x_701_);
lean_dec(v___x_696_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v_c_695_);
v___x_703_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_704_, 0, v_c_695_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*1, v___x_700_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v___x_696_);
v___x_706_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_706_, 0, v_c_695_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*1, v___x_700_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
else
{
lean_object* v___x_708_; lean_object* v_val_x3f_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
lean_dec(v___x_696_);
v___x_708_ = lean_unsigned_to_nat(1u);
v_val_x3f_709_ = l_Lean_Syntax_getArg(v_stx_692_, v___x_708_);
v___x_710_ = l_Lean_Syntax_getNumArgs(v_val_x3f_709_);
v___x_711_ = lean_nat_dec_eq(v___x_710_, v___x_694_);
lean_dec(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_712_ = l_Lean_Syntax_getArg(v_val_x3f_709_, v___x_694_);
v___x_713_ = l_Lean_Syntax_getArg(v_val_x3f_709_, v___x_708_);
lean_dec(v_val_x3f_709_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v_c_695_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v_val_x3f_709_);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v_c_695_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___boxed(lean_object* v_stx_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_719_);
lean_dec(v_stx_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(lean_object* v_x_722_){
_start:
{
if (lean_obj_tag(v_x_722_) == 1)
{
lean_object* v_args_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_args_724_ = lean_ctor_get(v_x_722_, 2);
v___x_725_ = lean_array_get_size(v_args_724_);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_dec_eq(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_array_fget_borrowed(v_args_724_, v___x_729_);
if (lean_obj_tag(v___x_730_) == 2)
{
lean_object* v_val_731_; lean_object* v___x_732_; 
v_val_731_ = lean_ctor_get(v___x_730_, 1);
lean_inc_ref(v_val_731_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_val_731_);
return v___x_732_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_733_;
}
}
}
else
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg___boxed(lean_object* v_x_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_735_);
lean_dec(v_x_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(lean_object* v_a_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_738_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1___boxed(lean_object* v_a_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(v_a_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v_a_747_);
return v_res_755_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_Lean_Level_ofNat(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = lean_box(0);
v___x_762_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_765_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_768_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1));
v___x_769_ = l_Lean_Expr_const___override(v___x_768_, v___x_767_);
return v___x_769_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6(void){
_start:
{
lean_object* v_strType_770_; lean_object* v___x_771_; lean_object* v_pairType_772_; 
v_strType_770_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_771_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5);
v_pairType_772_ = l_Lean_mkAppB(v___x_771_, v_strType_770_, v_strType_770_);
return v_pairType_772_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_777_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8));
v___x_778_ = l_Lean_Expr_const___override(v___x_777_, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10(void){
_start:
{
lean_object* v_pairType_779_; lean_object* v___x_780_; lean_object* v_arrayType_781_; 
v_pairType_779_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_780_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9);
v_arrayType_781_ = l_Lean_Expr_app___override(v___x_780_, v_pairType_779_);
return v_arrayType_781_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_787_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12));
v___x_788_ = l_Lean_Expr_const___override(v___x_787_, v___x_786_);
return v___x_788_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8));
v___x_790_ = l_Lean_mkStrLit(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15(void){
_start:
{
lean_object* v_pairType_791_; lean_object* v___x_792_; 
v_pairType_791_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v_pairType_791_);
return v___x_792_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20));
v___x_803_ = l_String_toRawSubstring_x27(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30));
v___x_824_ = l_String_toRawSubstring_x27(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0));
v___x_832_ = l_String_toRawSubstring_x27(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47(void){
_start:
{
lean_object* v_arrayType_855_; lean_object* v___x_856_; 
v_arrayType_855_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_arrayType_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(lean_object* v_stx_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_strType_867_; lean_object* v_toCold_868_; lean_object* v_currRecDepth_869_; lean_object* v_ref_870_; uint16_t v_optionFlags_871_; uint8_t v_suppressElabErrors_872_; uint8_t v_checkDeprecated_873_; uint8_t v_isRecordingDeps_874_; lean_object* v_ref_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_865_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_866_ = lean_box(0);
v_strType_867_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v_toCold_868_ = lean_ctor_get(v_a_862_, 0);
v_currRecDepth_869_ = lean_ctor_get(v_a_862_, 1);
v_ref_870_ = lean_ctor_get(v_a_862_, 2);
v_optionFlags_871_ = lean_ctor_get_uint16(v_a_862_, sizeof(void*)*3);
v_suppressElabErrors_872_ = lean_ctor_get_uint8(v_a_862_, sizeof(void*)*3 + 2);
v_checkDeprecated_873_ = lean_ctor_get_uint8(v_a_862_, sizeof(void*)*3 + 3);
v_isRecordingDeps_874_ = lean_ctor_get_uint8(v_a_862_, sizeof(void*)*3 + 4);
v_ref_875_ = l_Lean_replaceRef(v_stx_857_, v_ref_870_);
lean_inc(v_ref_875_);
lean_inc(v_currRecDepth_869_);
lean_inc_ref(v_toCold_868_);
v___x_876_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_876_, 0, v_toCold_868_);
lean_ctor_set(v___x_876_, 1, v_currRecDepth_869_);
lean_ctor_set(v___x_876_, 2, v_ref_875_);
lean_ctor_set_uint16(v___x_876_, sizeof(void*)*3, v_optionFlags_871_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3 + 2, v_suppressElabErrors_872_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3 + 3, v_checkDeprecated_873_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3 + 4, v_isRecordingDeps_874_);
v___x_877_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_857_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
switch(lean_obj_tag(v_a_878_))
{
case 0:
{
lean_object* v_stx_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_ref_875_);
v_stx_879_ = lean_ctor_get(v_a_878_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_a_878_);
if (v_isSharedCheck_918_ == 0)
{
v___x_881_ = v_a_878_;
v_isShared_882_ = v_isSharedCheck_918_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_stx_879_);
lean_dec(v_a_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_918_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_name_883_; lean_object* v_val_884_; lean_object* v___x_885_; 
v_name_883_ = lean_ctor_get(v_stx_879_, 0);
lean_inc(v_name_883_);
v_val_884_ = lean_ctor_get(v_stx_879_, 2);
lean_inc(v_val_884_);
lean_dec_ref(v_stx_879_);
v___x_885_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_883_);
lean_dec(v_name_883_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_val_884_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v___x_876_, v_a_863_);
lean_dec_ref_known(v___x_876_, 3);
lean_dec(v_val_884_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_901_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_901_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_893_ = l_Lean_mkStrLit(v_a_886_);
v___x_894_ = l_Lean_mkApp4(v___x_892_, v_strType_867_, v_strType_867_, v___x_893_, v_a_888_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_894_);
v___x_896_ = v___x_881_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_900_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_896_);
v___x_898_ = v___x_890_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_a_886_);
lean_del_object(v___x_881_);
v_a_902_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_887_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_887_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_val_884_);
lean_del_object(v___x_881_);
lean_dec_ref_known(v___x_876_, 3);
v_a_910_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_885_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_885_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
case 1:
{
lean_object* v_stx_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref_known(v___x_876_, 3);
lean_dec(v_ref_875_);
v_stx_919_ = lean_ctor_get(v_a_878_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_878_);
if (v_isSharedCheck_947_ == 0)
{
v___x_921_ = v_a_878_;
v_isShared_922_ = v_isSharedCheck_947_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_stx_919_);
lean_dec(v_a_878_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_947_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_stx_919_);
lean_dec(v_stx_919_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_938_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_938_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_928_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_929_ = l_Lean_mkStrLit(v_a_924_);
v___x_930_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14);
v___x_931_ = l_Lean_mkApp4(v___x_928_, v_strType_867_, v_strType_867_, v___x_929_, v___x_930_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 0);
lean_ctor_set(v___x_921_, 0, v___x_931_);
v___x_933_ = v___x_921_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_933_);
v___x_935_ = v___x_926_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_del_object(v___x_921_);
v_a_939_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_923_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_923_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
default: 
{
uint8_t v_isMany_948_; 
v_isMany_948_ = lean_ctor_get_uint8(v_a_878_, sizeof(void*)*1);
if (v_isMany_948_ == 0)
{
lean_object* v_stx_949_; lean_object* v___x_950_; 
lean_dec(v_ref_875_);
v_stx_949_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_stx_949_);
lean_dec_ref_known(v_a_878_, 1);
v___x_950_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_948_, v_stx_949_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v___x_876_, v_a_863_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v_term_952_; lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v_term_952_ = lean_ctor_get(v_a_951_, 1);
lean_inc(v_term_952_);
lean_dec(v_a_951_);
v___x_953_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15);
v___x_954_ = 1;
v___x_955_ = lean_box(0);
v___x_956_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_952_, v___x_953_, v___x_954_, v___x_954_, v___x_955_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v___x_876_, v_a_863_);
lean_dec_ref_known(v___x_876_, 3);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_965_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_a_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_956_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_956_);
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
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
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
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref_known(v___x_876_, 3);
v_a_974_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_950_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_950_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_stx_982_; lean_object* v___x_983_; 
v_stx_982_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_stx_982_);
lean_dec_ref_known(v_a_878_, 1);
v___x_983_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_948_, v_stx_982_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v___x_876_, v_a_863_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_quotContext_985_; lean_object* v_currMacroScope_986_; uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_term_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v_quotContext_985_ = lean_ctor_get(v_toCold_868_, 8);
v_currMacroScope_986_ = lean_ctor_get(v_toCold_868_, 9);
v___x_987_ = 0;
v___x_988_ = l_Lean_SourceInfo_fromRef(v_ref_875_, v___x_987_);
lean_dec(v_ref_875_);
v___x_989_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_990_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21);
v___x_991_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24));
lean_inc_n(v_currMacroScope_986_, 3);
lean_inc_n(v_quotContext_985_, 3);
v___x_992_ = l_Lean_addMacroScope(v_quotContext_985_, v___x_991_, v_currMacroScope_986_);
v___x_993_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26));
lean_inc_n(v___x_988_, 10);
v___x_994_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_994_, 0, v___x_988_);
lean_ctor_set(v___x_994_, 1, v___x_990_);
lean_ctor_set(v___x_994_, 2, v___x_992_);
lean_ctor_set(v___x_994_, 3, v___x_993_);
v___x_995_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28));
v___x_996_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29));
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_988_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31);
v___x_999_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32));
v___x_1000_ = l_Lean_addMacroScope(v_quotContext_985_, v___x_999_, v_currMacroScope_986_);
v___x_1001_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1001_, 0, v___x_988_);
lean_ctor_set(v___x_1001_, 1, v___x_998_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
lean_ctor_set(v___x_1001_, 3, v___x_866_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_988_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35));
v___x_1005_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36);
v___x_1006_ = l_Lean_addMacroScope(v_quotContext_985_, v___x_865_, v_currMacroScope_986_);
v___x_1007_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42));
v___x_1008_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1008_, 0, v___x_988_);
lean_ctor_set(v___x_1008_, 1, v___x_1005_);
lean_ctor_set(v___x_1008_, 2, v___x_1006_);
lean_ctor_set(v___x_1008_, 3, v___x_1007_);
v___x_1009_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43));
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_988_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_inc_ref(v___x_1008_);
v___x_1011_ = l_Lean_Syntax_node3(v___x_988_, v___x_1004_, v___x_1008_, v___x_1010_, v___x_1008_);
v_term_1012_ = lean_ctor_get(v_a_984_, 1);
lean_inc(v_term_1012_);
lean_dec(v_a_984_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44));
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_988_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1016_ = l_Lean_Syntax_node5(v___x_988_, v___x_995_, v___x_997_, v___x_1001_, v___x_1003_, v___x_1011_, v___x_1014_);
v___x_1017_ = l_Lean_Syntax_node2(v___x_988_, v___x_1015_, v___x_1016_, v_term_1012_);
v___x_1018_ = l_Lean_Syntax_node2(v___x_988_, v___x_989_, v___x_994_, v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47);
v___x_1020_ = lean_box(0);
v___x_1021_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1018_, v___x_1019_, v_isMany_948_, v_isMany_948_, v___x_1020_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v___x_876_, v_a_863_);
lean_dec_ref_known(v___x_876_, 3);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1021_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1021_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref_known(v___x_876_, 3);
lean_dec(v_ref_875_);
v_a_1039_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_983_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_983_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref_known(v___x_876_, 3);
lean_dec(v_ref_875_);
v_a_1047_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_877_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_877_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___boxed(lean_object* v_stx_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_stx_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_stx_1055_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(lean_object* v_stx_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_1064_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___boxed(lean_object* v_stx_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(v_stx_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v_stx_1073_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(lean_object* v_k_1082_, lean_object* v_x_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_1083_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___boxed(lean_object* v_k_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(v_k_1092_, v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_x_1093_);
lean_dec(v_k_1092_);
return v_res_1101_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1));
v___x_1108_ = l_Lean_Expr_const___override(v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4));
v___x_1115_ = l_Lean_Expr_const___override(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(lean_object* v_as_1116_, size_t v_sz_1117_, size_t v_i_1118_, lean_object* v_b_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_a_1128_; lean_object* v_pairType_1132_; uint8_t v___x_1133_; 
v_pairType_1132_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1133_ = lean_usize_dec_lt(v_i_1118_, v_sz_1117_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_b_1119_);
return v___x_1134_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1136_; 
v_a_1135_ = lean_array_uget_borrowed(v_as_1116_, v_i_1118_);
v___x_1136_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_a_1135_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
if (lean_obj_tag(v_a_1137_) == 0)
{
lean_object* v_val_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_val_1138_ = lean_ctor_get(v_a_1137_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v_a_1137_, 1);
v___x_1139_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2);
v___x_1140_ = l_Lean_mkApp3(v___x_1139_, v_pairType_1132_, v_b_1119_, v_val_1138_);
v_a_1128_ = v___x_1140_;
goto v___jp_1127_;
}
else
{
lean_object* v_val_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_val_1141_ = lean_ctor_get(v_a_1137_, 0);
lean_inc(v_val_1141_);
lean_dec_ref_known(v_a_1137_, 1);
v___x_1142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5);
v___x_1143_ = l_Lean_mkApp3(v___x_1142_, v_pairType_1132_, v_b_1119_, v_val_1141_);
v_a_1128_ = v___x_1143_;
goto v___jp_1127_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_b_1119_);
v_a_1144_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1136_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1136_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
v___jp_1127_:
{
size_t v___x_1129_; size_t v___x_1130_; 
v___x_1129_ = ((size_t)1ULL);
v___x_1130_ = lean_usize_add(v_i_1118_, v___x_1129_);
v_i_1118_ = v___x_1130_;
v_b_1119_ = v_a_1128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___boxed(lean_object* v_as_1152_, lean_object* v_sz_1153_, lean_object* v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; lean_object* v_res_1165_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1153_);
lean_dec(v_sz_1153_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_as_1152_, v_sz_boxed_1163_, v_i_boxed_1164_, v_b_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_as_1152_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(lean_object* v_stxs_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v_pairType_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_box(0);
v_pairType_1175_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1176_ = l_Lean_Meta_mkArrayLit(v_pairType_1175_, v___x_1174_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; size_t v_sz_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v_sz_1178_ = lean_array_size(v_stxs_1166_);
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_stxs_1166_, v_sz_1178_, v___x_1179_, v_a_1177_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
return v___x_1180_;
}
else
{
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs___boxed(lean_object* v_stxs_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_stxs_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec_ref(v_stxs_1181_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(lean_object* v___x_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1190_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed(lean_object* v___x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(v___x_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(lean_object* v_stx_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___y_1218_; lean_object* v_k_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
lean_inc(v_stx_1209_);
v_k_1229_ = l_Lean_Syntax_getKind(v_stx_1209_);
v___x_1230_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_1231_ = lean_name_eq(v_k_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_1233_ = lean_name_eq(v_k_1229_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1235_ = lean_name_eq(v_k_1229_, v___x_1234_);
lean_dec(v_k_1229_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0));
v___y_1218_ = v___x_1236_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1237_; lean_object* v___f_1238_; 
lean_inc(v_stx_1209_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_stx_1209_);
v___f_1238_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1238_, 0, v___x_1237_);
v___y_1218_ = v___f_1238_;
goto v___jp_1217_;
}
}
else
{
lean_object* v___x_1239_; lean_object* v___f_1240_; 
lean_dec(v_k_1229_);
lean_inc(v_stx_1209_);
v___x_1239_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1239_, 0, v_stx_1209_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*1, v___x_1233_);
v___f_1240_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1240_, 0, v___x_1239_);
v___y_1218_ = v___f_1240_;
goto v___jp_1217_;
}
}
else
{
uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___f_1243_; 
lean_dec(v_k_1229_);
v___x_1241_ = 0;
lean_inc(v_stx_1209_);
v___x_1242_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1242_, 0, v_stx_1209_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*1, v___x_1241_);
v___f_1243_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1243_, 0, v___x_1242_);
v___y_1218_ = v___f_1243_;
goto v___jp_1217_;
}
v___jp_1217_:
{
lean_object* v_toCold_1219_; lean_object* v_currRecDepth_1220_; lean_object* v_ref_1221_; uint16_t v_optionFlags_1222_; uint8_t v_suppressElabErrors_1223_; uint8_t v_checkDeprecated_1224_; uint8_t v_isRecordingDeps_1225_; lean_object* v_ref_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_toCold_1219_ = lean_ctor_get(v___y_1214_, 0);
v_currRecDepth_1220_ = lean_ctor_get(v___y_1214_, 1);
v_ref_1221_ = lean_ctor_get(v___y_1214_, 2);
v_optionFlags_1222_ = lean_ctor_get_uint16(v___y_1214_, sizeof(void*)*3);
v_suppressElabErrors_1223_ = lean_ctor_get_uint8(v___y_1214_, sizeof(void*)*3 + 2);
v_checkDeprecated_1224_ = lean_ctor_get_uint8(v___y_1214_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1225_ = lean_ctor_get_uint8(v___y_1214_, sizeof(void*)*3 + 4);
v_ref_1226_ = l_Lean_replaceRef(v_stx_1209_, v_ref_1221_);
lean_dec(v_stx_1209_);
lean_inc(v_currRecDepth_1220_);
lean_inc_ref(v_toCold_1219_);
v___x_1227_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1227_, 0, v_toCold_1219_);
lean_ctor_set(v___x_1227_, 1, v_currRecDepth_1220_);
lean_ctor_set(v___x_1227_, 2, v_ref_1226_);
lean_ctor_set_uint16(v___x_1227_, sizeof(void*)*3, v_optionFlags_1222_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*3 + 2, v_suppressElabErrors_1223_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*3 + 3, v_checkDeprecated_1224_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*3 + 4, v_isRecordingDeps_1225_);
lean_inc(v___y_1215_);
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
v___x_1228_ = lean_apply_7(v___y_1218_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___x_1227_, v___y_1215_, lean_box(0));
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___boxed(lean_object* v_stx_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_stx_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(lean_object* v_as_1267_, size_t v_sz_1268_, size_t v_i_1269_, lean_object* v_b_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_a_1279_; uint8_t v___x_1283_; 
v___x_1283_ = lean_usize_dec_lt(v_i_1269_, v_sz_1268_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_b_1270_);
return v___x_1284_;
}
else
{
lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1323_; 
v_fst_1285_ = lean_ctor_get(v_b_1270_, 0);
v_snd_1286_ = lean_ctor_get(v_b_1270_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_b_1270_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1288_ = v_b_1270_;
v_isShared_1289_ = v_isSharedCheck_1323_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1286_);
lean_inc(v_fst_1285_);
lean_dec(v_b_1270_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1323_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_a_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_a_1290_ = lean_array_uget_borrowed(v_as_1267_, v_i_1269_);
lean_inc(v_a_1290_);
v___x_1291_ = l_Lean_Syntax_getKind(v_a_1290_);
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1));
v___x_1293_ = lean_name_eq(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3));
v___x_1295_ = lean_name_eq(v___x_1291_, v___x_1294_);
lean_dec(v___x_1291_);
if (v___x_1295_ == 0)
{
lean_object* v_tcs_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_tcs_1296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4));
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_snd_1286_);
v___x_1298_ = lean_array_push(v_fst_1285_, v___x_1297_);
lean_inc(v_a_1290_);
v___x_1299_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_a_1290_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = lean_array_push(v___x_1298_, v_a_1300_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v_tcs_1296_);
lean_ctor_set(v___x_1288_, 0, v___x_1301_);
v___x_1303_ = v___x_1288_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_tcs_1296_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v_a_1279_ = v___x_1303_;
goto v___jp_1278_;
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v___x_1298_);
lean_del_object(v___x_1288_);
v_a_1305_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1299_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1299_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_inc(v_a_1290_);
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1290_);
v___x_1314_ = lean_array_push(v_snd_1286_, v___x_1313_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1314_);
v___x_1316_ = v___x_1288_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v_a_1279_ = v___x_1316_;
goto v___jp_1278_;
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
lean_dec(v___x_1291_);
lean_inc(v_a_1290_);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_a_1290_);
v___x_1319_ = lean_array_push(v_snd_1286_, v___x_1318_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1319_);
v___x_1321_ = v___x_1288_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v_a_1279_ = v___x_1321_;
goto v___jp_1278_;
}
}
}
}
v___jp_1278_:
{
size_t v___x_1280_; size_t v___x_1281_; 
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1269_, v___x_1280_);
v_i_1269_ = v___x_1281_;
v_b_1270_ = v_a_1279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___boxed(lean_object* v_as_1324_, lean_object* v_sz_1325_, lean_object* v_i_1326_, lean_object* v_b_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
size_t v_sz_boxed_1335_; size_t v_i_boxed_1336_; lean_object* v_res_1337_; 
v_sz_boxed_1335_ = lean_unbox_usize(v_sz_1325_);
lean_dec(v_sz_1325_);
v_i_boxed_1336_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v_as_1324_, v_sz_boxed_1335_, v_i_boxed_1336_, v_b_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_as_1324_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(lean_object* v_c_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; size_t v_sz_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = l_Lean_Syntax_getArgs(v_c_1342_);
v___x_1352_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1));
v_sz_1353_ = lean_array_size(v___x_1351_);
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v___x_1351_, v_sz_1353_, v___x_1354_, v___x_1352_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___x_1351_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1372_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1372_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1372_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_fst_1360_; lean_object* v_snd_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_fst_1360_ = lean_ctor_get(v_a_1356_, 0);
lean_inc(v_fst_1360_);
v_snd_1361_ = lean_ctor_get(v_a_1356_, 1);
lean_inc(v_snd_1361_);
lean_dec(v_a_1356_);
v___x_1362_ = lean_array_get_size(v_snd_1361_);
v___x_1363_ = lean_nat_dec_eq(v___x_1362_, v___x_1350_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v_items_1365_; lean_object* v___x_1367_; 
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_snd_1361_);
v_items_1365_ = lean_array_push(v_fst_1360_, v___x_1364_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v_items_1365_);
v___x_1367_ = v___x_1358_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_items_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
lean_object* v___x_1370_; 
lean_dec(v_snd_1361_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v_fst_1360_);
v___x_1370_ = v___x_1358_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_fst_1360_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1355_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1355_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___boxed(lean_object* v_c_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_c_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v_c_1381_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(lean_object* v_stx_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
lean_inc(v_stx_1390_);
v___x_1392_ = l_Lean_Syntax_getKind(v_stx_1390_);
v___x_1393_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1394_ = lean_name_eq(v___x_1392_, v___x_1393_);
lean_dec(v___x_1392_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_dec(v_stx_1390_);
v___x_1395_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; size_t v_sz_1399_; size_t v___x_1400_; lean_object* v_attrs_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v_startTag_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1396_ = lean_unsigned_to_nat(2u);
v___x_1397_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1396_);
v___x_1398_ = l_Lean_Syntax_getArgs(v___x_1397_);
lean_dec(v___x_1397_);
v_sz_1399_ = lean_array_size(v___x_1398_);
v___x_1400_ = ((size_t)0ULL);
v_attrs_1401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_1399_, v___x_1400_, v___x_1398_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1402_);
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1404_);
v___x_1406_ = lean_unsigned_to_nat(3u);
v___x_1407_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1406_);
v_startTag_1408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_1408_, 0, v___x_1403_);
lean_ctor_set(v_startTag_1408_, 1, v___x_1405_);
lean_ctor_set(v_startTag_1408_, 2, v_attrs_1401_);
lean_ctor_set(v_startTag_1408_, 3, v___x_1407_);
v___x_1409_ = l_Lean_Syntax_getNumArgs(v_stx_1390_);
v___x_1410_ = lean_unsigned_to_nat(4u);
v___x_1411_ = lean_nat_dec_eq(v___x_1409_, v___x_1410_);
lean_dec(v___x_1409_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v_endTag_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1412_ = lean_unsigned_to_nat(5u);
v___x_1413_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1412_);
v___x_1414_ = lean_unsigned_to_nat(6u);
v___x_1415_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1414_);
v___x_1416_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5));
v___x_1417_ = lean_unsigned_to_nat(7u);
v___x_1418_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1417_);
v_endTag_1419_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_1419_, 0, v___x_1413_);
lean_ctor_set(v_endTag_1419_, 1, v___x_1415_);
lean_ctor_set(v_endTag_1419_, 2, v___x_1416_);
lean_ctor_set(v_endTag_1419_, 3, v___x_1418_);
v___x_1420_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1410_);
lean_dec(v_stx_1390_);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_endTag_1419_);
v___x_1423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1423_, 0, v_startTag_1408_);
lean_ctor_set(v___x_1423_, 1, v___x_1421_);
lean_ctor_set(v___x_1423_, 2, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v_stx_1390_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1426_, 0, v_startTag_1408_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
lean_ctor_set(v___x_1426_, 2, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg___boxed(lean_object* v_stx_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1428_);
return v_res_1430_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0));
v___x_1436_ = l_Lean_Expr_const___override(v___x_1435_, v___x_1434_);
return v___x_1436_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(uint8_t v___x_1439_, lean_object* v_b_1440_, lean_object* v_tm_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2);
v___x_1450_ = lean_box(0);
v___x_1451_ = l_Lean_Elab_Term_elabTermEnsuringType(v_tm_1441_, v___x_1449_, v___x_1439_, v___x_1439_, v___x_1450_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1456_ = lean_array_push(v_b_1440_, v_a_1452_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v___x_1456_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1458_);
v___x_1460_ = v___x_1454_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_b_1440_);
v_a_1463_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1451_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1451_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___boxed(lean_object* v___x_1471_, lean_object* v_b_1472_, lean_object* v_tm_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
uint8_t v___x_17909__boxed_1481_; lean_object* v_res_1482_; 
v___x_17909__boxed_1481_ = lean_unbox(v___x_1471_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_17909__boxed_1481_, v_b_1472_, v_tm_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1482_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2));
v___x_1492_ = l_Lean_Expr_const___override(v___x_1491_, v___x_1490_);
return v___x_1492_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_box(0);
v___x_1499_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5));
v___x_1500_ = l_Lean_Expr_const___override(v___x_1499_, v___x_1498_);
return v___x_1500_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0));
v___x_1507_ = l_Lean_Expr_const___override(v___x_1506_, v___x_1505_);
return v___x_1507_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2));
v___x_1514_ = l_Lean_Expr_const___override(v___x_1513_, v___x_1512_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6));
v___x_1521_ = l_String_toRawSubstring_x27(v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(lean_object* v_as_1532_, size_t v_sz_1533_, size_t v_i_1534_, lean_object* v_b_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_a_1544_; lean_object* v___y_1549_; uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_lt(v_i_1534_, v_sz_1533_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_b_1535_);
return v___x_1561_;
}
else
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_array_uget_borrowed(v_as_1532_, v_i_1534_);
switch(lean_obj_tag(v_a_1562_))
{
case 0:
{
lean_object* v_stx_1563_; lean_object* v_toCold_1564_; lean_object* v_currRecDepth_1565_; lean_object* v_ref_1566_; uint16_t v_optionFlags_1567_; uint8_t v_suppressElabErrors_1568_; uint8_t v_checkDeprecated_1569_; uint8_t v_isRecordingDeps_1570_; lean_object* v_ref_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_stx_1563_ = lean_ctor_get(v_a_1562_, 0);
v_toCold_1564_ = lean_ctor_get(v___y_1540_, 0);
v_currRecDepth_1565_ = lean_ctor_get(v___y_1540_, 1);
v_ref_1566_ = lean_ctor_get(v___y_1540_, 2);
v_optionFlags_1567_ = lean_ctor_get_uint16(v___y_1540_, sizeof(void*)*3);
v_suppressElabErrors_1568_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 2);
v_checkDeprecated_1569_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1570_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 4);
v_ref_1571_ = l_Lean_replaceRef(v_stx_1563_, v_ref_1566_);
lean_inc(v_currRecDepth_1565_);
lean_inc_ref(v_toCold_1564_);
v___x_1572_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1572_, 0, v_toCold_1564_);
lean_ctor_set(v___x_1572_, 1, v_currRecDepth_1565_);
lean_ctor_set(v___x_1572_, 2, v_ref_1571_);
lean_ctor_set_uint16(v___x_1572_, sizeof(void*)*3, v_optionFlags_1567_);
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*3 + 2, v_suppressElabErrors_1568_);
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*3 + 3, v_checkDeprecated_1569_);
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*3 + 4, v_isRecordingDeps_1570_);
lean_inc(v_stx_1563_);
v___x_1573_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_1563_, v___x_1572_, v___y_1541_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; 
lean_dec_ref_known(v___x_1573_, 1);
lean_inc(v_stx_1563_);
v___x_1574_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_1563_, v___x_1572_, v___y_1541_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1574_, 1);
lean_inc(v_stx_1563_);
v___x_1575_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1563_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_startTag_1577_; lean_object* v_children_x3f_1578_; lean_object* v_name_1579_; lean_object* v_attrs_1580_; lean_object* v___x_1581_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v_startTag_1577_ = lean_ctor_get(v_a_1576_, 0);
lean_inc_ref(v_startTag_1577_);
v_children_x3f_1578_ = lean_ctor_get(v_a_1576_, 1);
lean_inc(v_children_x3f_1578_);
lean_dec(v_a_1576_);
v_name_1579_ = lean_ctor_get(v_startTag_1577_, 1);
lean_inc(v_name_1579_);
v_attrs_1580_ = lean_ctor_get(v_startTag_1577_, 2);
lean_inc_ref(v_attrs_1580_);
lean_dec_ref(v_startTag_1577_);
v___x_1581_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_1579_);
lean_dec(v_name_1579_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_attrs_1580_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___x_1572_, v___y_1541_);
lean_dec_ref(v_attrs_1580_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v_a_1592_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
if (lean_obj_tag(v_children_x3f_1578_) == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref_known(v___x_1572_, 3);
v___x_1597_ = lean_box(0);
v_a_1592_ = v___x_1597_;
goto v___jp_1591_;
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1615_; 
v_val_1598_ = lean_ctor_get(v_children_x3f_1578_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_children_x3f_1578_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1600_ = v_children_x3f_1578_;
v_isShared_1601_ = v_isSharedCheck_1615_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v_children_x3f_1578_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1615_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; 
v___x_1602_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_val_1598_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___x_1572_, v___y_1541_);
lean_dec_ref_known(v___x_1572_, 3);
lean_dec(v_val_1598_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_a_1603_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
v_a_1592_ = v___x_1605_;
goto v___jp_1591_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1584_);
lean_dec(v_a_1582_);
lean_dec_ref(v_b_1535_);
v_a_1607_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1602_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1602_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
v___jp_1585_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_inc_ref(v___y_1587_);
v___x_1589_ = l_Lean_mkApp3(v___y_1587_, v___y_1586_, v_a_1584_, v___y_1588_);
v___x_1590_ = lean_array_push(v_b_1535_, v___x_1589_);
v_a_1544_ = v___x_1590_;
goto v___jp_1543_;
}
v___jp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1);
v___x_1594_ = l_Lean_mkStrLit(v_a_1582_);
if (lean_obj_tag(v_a_1592_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
v___y_1586_ = v___x_1594_;
v___y_1587_ = v___x_1593_;
v___y_1588_ = v___x_1595_;
goto v___jp_1585_;
}
else
{
lean_object* v_val_1596_; 
v_val_1596_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_a_1592_, 1);
v___y_1586_ = v___x_1594_;
v___y_1587_ = v___x_1593_;
v___y_1588_ = v_val_1596_;
goto v___jp_1585_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1582_);
lean_dec(v_children_x3f_1578_);
lean_dec_ref_known(v___x_1572_, 3);
lean_dec_ref(v_b_1535_);
v_a_1616_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1583_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1583_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_attrs_1580_);
lean_dec(v_children_x3f_1578_);
lean_dec_ref_known(v___x_1572_, 3);
lean_dec_ref(v_b_1535_);
v_a_1624_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1581_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1581_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref_known(v___x_1572_, 3);
lean_dec_ref(v_b_1535_);
v_a_1632_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1575_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1575_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref_known(v___x_1572_, 3);
lean_dec_ref(v_b_1535_);
v_a_1640_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1574_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1574_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref_known(v___x_1572_, 3);
lean_dec_ref(v_b_1535_);
v_a_1648_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1573_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1573_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
case 1:
{
lean_object* v_stx_1656_; lean_object* v_toCold_1657_; lean_object* v_currRecDepth_1658_; lean_object* v_ref_1659_; uint16_t v_optionFlags_1660_; uint8_t v_suppressElabErrors_1661_; uint8_t v_checkDeprecated_1662_; uint8_t v_isRecordingDeps_1663_; lean_object* v___x_1664_; lean_object* v_ref_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_stx_1656_ = lean_ctor_get(v_a_1562_, 0);
v_toCold_1657_ = lean_ctor_get(v___y_1540_, 0);
v_currRecDepth_1658_ = lean_ctor_get(v___y_1540_, 1);
v_ref_1659_ = lean_ctor_get(v___y_1540_, 2);
v_optionFlags_1660_ = lean_ctor_get_uint16(v___y_1540_, sizeof(void*)*3);
v_suppressElabErrors_1661_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 2);
v_checkDeprecated_1662_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1663_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 4);
lean_inc_ref(v_stx_1656_);
v___x_1664_ = l_Lean_Html_Syntax_TextCommentsView_getSyntax(v_stx_1656_);
v_ref_1665_ = l_Lean_replaceRef(v___x_1664_, v_ref_1659_);
lean_dec(v___x_1664_);
lean_inc(v_currRecDepth_1658_);
lean_inc_ref(v_toCold_1657_);
v___x_1666_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1666_, 0, v_toCold_1657_);
lean_ctor_set(v___x_1666_, 1, v_currRecDepth_1658_);
lean_ctor_set(v___x_1666_, 2, v_ref_1665_);
lean_ctor_set_uint16(v___x_1666_, sizeof(void*)*3, v_optionFlags_1660_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*3 + 2, v_suppressElabErrors_1661_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*3 + 3, v_checkDeprecated_1662_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*3 + 4, v_isRecordingDeps_1663_);
v___x_1667_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_stx_1656_, v___x_1666_, v___y_1541_);
lean_dec_ref_known(v___x_1666_, 3);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_string_utf8_byte_size(v_a_1668_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_nat_dec_eq(v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1672_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3);
v___x_1673_ = l_Lean_mkStrLit(v_a_1668_);
v___x_1674_ = l_Lean_Expr_app___override(v___x_1672_, v___x_1673_);
v___x_1675_ = lean_array_push(v_b_1535_, v___x_1674_);
v_a_1544_ = v___x_1675_;
goto v___jp_1543_;
}
else
{
lean_dec(v_a_1668_);
v_a_1544_ = v_b_1535_;
goto v___jp_1543_;
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_b_1535_);
v_a_1676_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1667_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1667_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
default: 
{
uint8_t v_isMany_1684_; lean_object* v_stx_1685_; lean_object* v_toCold_1686_; lean_object* v_currRecDepth_1687_; lean_object* v_ref_1688_; uint16_t v_optionFlags_1689_; uint8_t v_suppressElabErrors_1690_; uint8_t v_checkDeprecated_1691_; uint8_t v_isRecordingDeps_1692_; lean_object* v_ref_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_isMany_1684_ = lean_ctor_get_uint8(v_a_1562_, sizeof(void*)*1);
v_stx_1685_ = lean_ctor_get(v_a_1562_, 0);
v_toCold_1686_ = lean_ctor_get(v___y_1540_, 0);
v_currRecDepth_1687_ = lean_ctor_get(v___y_1540_, 1);
v_ref_1688_ = lean_ctor_get(v___y_1540_, 2);
v_optionFlags_1689_ = lean_ctor_get_uint16(v___y_1540_, sizeof(void*)*3);
v_suppressElabErrors_1690_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 2);
v_checkDeprecated_1691_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1692_ = lean_ctor_get_uint8(v___y_1540_, sizeof(void*)*3 + 4);
v_ref_1693_ = l_Lean_replaceRef(v_stx_1685_, v_ref_1688_);
lean_inc(v_ref_1693_);
lean_inc(v_currRecDepth_1687_);
lean_inc_ref(v_toCold_1686_);
v___x_1694_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1694_, 0, v_toCold_1686_);
lean_ctor_set(v___x_1694_, 1, v_currRecDepth_1687_);
lean_ctor_set(v___x_1694_, 2, v_ref_1693_);
lean_ctor_set_uint16(v___x_1694_, sizeof(void*)*3, v_optionFlags_1689_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 2, v_suppressElabErrors_1690_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 3, v_checkDeprecated_1691_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 4, v_isRecordingDeps_1692_);
lean_inc(v_stx_1685_);
v___x_1695_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_1684_, v_stx_1685_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___x_1694_, v___y_1541_);
if (lean_obj_tag(v___x_1695_) == 0)
{
if (v_isMany_1684_ == 0)
{
lean_object* v_a_1696_; lean_object* v_term_1697_; lean_object* v___x_1698_; 
lean_dec(v_ref_1693_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v_term_1697_ = lean_ctor_get(v_a_1696_, 1);
lean_inc(v_term_1697_);
lean_dec(v_a_1696_);
v___x_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1560_, v_b_1535_, v_term_1697_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___x_1694_, v___y_1541_);
lean_dec_ref_known(v___x_1694_, 3);
v___y_1549_ = v___x_1698_;
goto v___jp_1548_;
}
else
{
lean_object* v_a_1699_; lean_object* v_quotContext_1700_; lean_object* v_currMacroScope_1701_; lean_object* v_term_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_a_1699_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1695_, 1);
v_quotContext_1700_ = lean_ctor_get(v_toCold_1686_, 8);
v_currMacroScope_1701_ = lean_ctor_get(v_toCold_1686_, 9);
v_term_1702_ = lean_ctor_get(v_a_1699_, 1);
lean_inc(v_term_1702_);
lean_dec(v_a_1699_);
v___x_1703_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_1704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5));
v___x_1705_ = 0;
v___x_1706_ = l_Lean_SourceInfo_fromRef(v_ref_1693_, v___x_1705_);
lean_dec(v_ref_1693_);
v___x_1707_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7);
lean_inc(v_currMacroScope_1701_);
lean_inc(v_quotContext_1700_);
v___x_1708_ = l_Lean_addMacroScope(v_quotContext_1700_, v___x_1704_, v_currMacroScope_1701_);
v___x_1709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10));
lean_inc_n(v___x_1706_, 2);
v___x_1710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1706_);
lean_ctor_set(v___x_1710_, 1, v___x_1707_);
lean_ctor_set(v___x_1710_, 2, v___x_1708_);
lean_ctor_set(v___x_1710_, 3, v___x_1709_);
v___x_1711_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1712_ = l_Lean_Syntax_node1(v___x_1706_, v___x_1711_, v_term_1702_);
v___x_1713_ = l_Lean_Syntax_node2(v___x_1706_, v___x_1703_, v___x_1710_, v___x_1712_);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1560_, v_b_1535_, v___x_1713_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___x_1694_, v___y_1541_);
lean_dec_ref_known(v___x_1694_, 3);
v___y_1549_ = v___x_1714_;
goto v___jp_1548_;
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref_known(v___x_1694_, 3);
lean_dec(v_ref_1693_);
lean_dec_ref(v_b_1535_);
v_a_1715_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1695_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1695_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
}
v___jp_1543_:
{
size_t v___x_1545_; size_t v___x_1546_; 
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_add(v_i_1534_, v___x_1545_);
v_i_1534_ = v___x_1546_;
v_b_1535_ = v_a_1544_;
goto _start;
}
v___jp_1548_:
{
if (lean_obj_tag(v___y_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_snd_1551_; 
v_a_1550_ = lean_ctor_get(v___y_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___y_1549_, 1);
v_snd_1551_ = lean_ctor_get(v_a_1550_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_a_1550_);
v_a_1544_ = v_snd_1551_;
goto v___jp_1543_;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___y_1549_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___y_1549_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___y_1549_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___y_1549_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(lean_object* v_stx_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_toCold_1731_; lean_object* v_currRecDepth_1732_; lean_object* v_ref_1733_; uint16_t v_optionFlags_1734_; uint8_t v_suppressElabErrors_1735_; uint8_t v_checkDeprecated_1736_; uint8_t v_isRecordingDeps_1737_; lean_object* v___x_1738_; lean_object* v_es_1739_; lean_object* v_ref_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_toCold_1731_ = lean_ctor_get(v_a_1728_, 0);
v_currRecDepth_1732_ = lean_ctor_get(v_a_1728_, 1);
v_ref_1733_ = lean_ctor_get(v_a_1728_, 2);
v_optionFlags_1734_ = lean_ctor_get_uint16(v_a_1728_, sizeof(void*)*3);
v_suppressElabErrors_1735_ = lean_ctor_get_uint8(v_a_1728_, sizeof(void*)*3 + 2);
v_checkDeprecated_1736_ = lean_ctor_get_uint8(v_a_1728_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1737_ = lean_ctor_get_uint8(v_a_1728_, sizeof(void*)*3 + 4);
v___x_1738_ = lean_unsigned_to_nat(0u);
v_es_1739_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0));
v_ref_1740_ = l_Lean_replaceRef(v_stx_1723_, v_ref_1733_);
lean_inc(v_currRecDepth_1732_);
lean_inc_ref(v_toCold_1731_);
v___x_1741_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1741_, 0, v_toCold_1731_);
lean_ctor_set(v___x_1741_, 1, v_currRecDepth_1732_);
lean_ctor_set(v___x_1741_, 2, v_ref_1740_);
lean_ctor_set_uint16(v___x_1741_, sizeof(void*)*3, v_optionFlags_1734_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*3 + 2, v_suppressElabErrors_1735_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*3 + 3, v_checkDeprecated_1736_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*3 + 4, v_isRecordingDeps_1737_);
v___x_1742_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_stx_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v___x_1741_, v_a_1729_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; size_t v_sz_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v_sz_1744_ = lean_array_size(v_a_1743_);
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_a_1743_, v_sz_1744_, v___x_1745_, v_es_1739_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v___x_1741_, v_a_1729_);
lean_dec(v_a_1743_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1770_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1770_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1770_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = lean_array_get_size(v_a_1747_);
v___x_1752_ = lean_nat_dec_eq(v___x_1751_, v___x_1738_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_del_object(v___x_1749_);
v___x_1753_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1754_ = lean_array_to_list(v_a_1747_);
v___x_1755_ = l_Lean_Meta_mkArrayLit(v___x_1753_, v___x_1754_, v_a_1726_, v_a_1727_, v___x_1741_, v_a_1729_);
lean_dec_ref_known(v___x_1741_, 3);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1765_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1765_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1765_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1760_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3);
v___x_1761_ = l_Lean_Expr_app___override(v___x_1760_, v_a_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1763_ = v___x_1758_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
return v___x_1755_;
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec(v_a_1747_);
lean_dec_ref_known(v___x_1741_, 3);
v___x_1766_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1766_);
v___x_1768_ = v___x_1749_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref_known(v___x_1741_, 3);
v_a_1771_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1746_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1746_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref_known(v___x_1741_, 3);
v_a_1779_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1742_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1742_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___boxed(lean_object* v_stx_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_stx_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_stx_1787_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___boxed(lean_object* v_as_1796_, lean_object* v_sz_1797_, lean_object* v_i_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
size_t v_sz_boxed_1807_; size_t v_i_boxed_1808_; lean_object* v_res_1809_; 
v_sz_boxed_1807_ = lean_unbox_usize(v_sz_1797_);
lean_dec(v_sz_1797_);
v_i_boxed_1808_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_as_1796_, v_sz_boxed_1807_, v_i_boxed_1808_, v_b_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_as_1796_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(lean_object* v_stx_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1810_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___boxed(lean_object* v_stx_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(v_stx_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg___boxed(lean_object* v_a_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(v_a_1831_);
lean_dec(v_a_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(lean_object* v_a_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1834_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___boxed(lean_object* v_a_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(v_a_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_a_1843_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(lean_object* v_stx_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1));
lean_inc(v_stx_1864_);
v___x_1873_ = l_Lean_Syntax_isOfKind(v_stx_1864_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
lean_dec(v_stx_1864_);
v___x_1874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v_h_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1875_ = lean_unsigned_to_nat(2u);
v_h_1876_ = l_Lean_Syntax_getArg(v_stx_1864_, v___x_1875_);
lean_dec(v_stx_1864_);
v___x_1877_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3));
lean_inc(v_h_1876_);
v___x_1878_ = l_Lean_Syntax_isOfKind(v_h_1876_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_dec(v_h_1876_);
v___x_1879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_h_1876_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
lean_dec(v_h_1876_);
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___boxed(lean_object* v_stx_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(lean_object* v_stx_1890_, lean_object* v_x_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1890_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___boxed(lean_object* v_stx_1900_, lean_object* v_x_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(v_stx_1900_, v_x_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_x_1901_);
return v_res_1909_;
}
}
lean_object* runtime_initialize_Lean_Data_Html_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Html_Elab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Html_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Html_Elab(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_Elab(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Html_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Html_Elab(builtin);
}
#ifdef __cplusplus
}
#endif
