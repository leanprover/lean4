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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint32_t v___y_4_; lean_object* v___x_9_; uint8_t v_decide_10_; 
v___x_9_ = lean_string_utf8_byte_size(v_s_1_);
v_decide_10_ = lean_nat_dec_eq(v_p_2_, v___x_9_);
if (v_decide_10_ == 0)
{
uint32_t v___x_11_; uint32_t v___x_12_; uint8_t v___x_13_; 
v___x_11_ = lean_string_utf8_get_fast(v_s_1_, v_p_2_);
v___x_12_ = 65;
v___x_13_ = lean_uint32_dec_le(v___x_12_, v___x_11_);
if (v___x_13_ == 0)
{
v___y_4_ = v___x_11_;
goto v___jp_3_;
}
else
{
uint32_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 90;
v___x_15_ = lean_uint32_dec_le(v___x_11_, v___x_14_);
if (v___x_15_ == 0)
{
v___y_4_ = v___x_11_;
goto v___jp_3_;
}
else
{
uint32_t v___x_16_; uint32_t v___x_17_; 
v___x_16_ = 32;
v___x_17_ = lean_uint32_add(v___x_11_, v___x_16_);
v___y_4_ = v___x_17_;
goto v___jp_3_;
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
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_p_2_);
v___x_5_ = lean_string_utf8_set(v_s_1_, v_p_2_, v___y_4_);
v___x_6_ = l_Char_utf8Size(v___y_4_);
v___x_7_ = lean_nat_add(v_p_2_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v_p_2_);
v_s_1_ = v___x_5_;
v_p_2_ = v___x_7_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_box(0);
v___x_19_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_20_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
return v___x_20_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0);
v___x_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_24_;
v_res_24_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___boxed(lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v_res_26_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(size_t v_sz_27_, size_t v_i_28_, lean_object* v_bs_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = lean_usize_dec_lt(v_i_28_, v_sz_27_);
if (v___x_30_ == 0)
{
return v_bs_29_;
}
else
{
lean_object* v_v_31_; lean_object* v___x_32_; lean_object* v_bs_x27_33_; size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; 
v_v_31_ = lean_array_uget(v_bs_29_, v_i_28_);
v___x_32_ = lean_unsigned_to_nat(0u);
v_bs_x27_33_ = lean_array_uset(v_bs_29_, v_i_28_, v___x_32_);
v___x_34_ = ((size_t)1ULL);
v___x_35_ = lean_usize_add(v_i_28_, v___x_34_);
v___x_36_ = lean_array_uset(v_bs_x27_33_, v_i_28_, v_v_31_);
v_i_28_ = v___x_35_;
v_bs_29_ = v___x_36_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_27_ = stack[0].m_num;
size_t v_i_28_ = stack[1].m_num;
lean_object* v_bs_29_ = stack[2].m_obj;
lean_object* v_res_38_;
v_res_38_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_27_, v_i_28_, v_bs_29_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1___boxed(lean_object* v_sz_39_, lean_object* v_i_40_, lean_object* v_bs_41_){
_start:
{
size_t v_sz_boxed_42_; size_t v_i_boxed_43_; lean_object* v_res_44_; 
v_sz_boxed_42_ = lean_unbox_usize(v_sz_39_);
lean_dec(v_sz_39_);
v_i_boxed_43_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_boxed_42_, v_i_boxed_43_, v_bs_41_);
return v_res_44_;
}
}
lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(lean_object* v_stx_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
lean_inc(v_stx_56_);
v___x_60_ = l_Lean_Syntax_getKind(v_stx_56_);
v___x_61_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_62_ = lean_name_eq(v___x_60_, v___x_61_);
lean_dec(v___x_60_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec(v_stx_56_);
v___x_63_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_63_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; size_t v_sz_67_; size_t v___x_68_; lean_object* v_attrs_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_startTag_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_64_ = lean_unsigned_to_nat(2u);
v___x_65_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_64_);
v___x_66_ = l_Lean_Syntax_getArgs(v___x_65_);
lean_dec(v___x_65_);
v_sz_67_ = lean_array_size(v___x_66_);
v___x_68_ = ((size_t)0ULL);
v_attrs_69_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_67_, v___x_68_, v___x_66_);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_70_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_72_);
v___x_74_ = lean_unsigned_to_nat(3u);
v___x_75_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_74_);
v_startTag_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_76_, 0, v___x_71_);
lean_ctor_set(v_startTag_76_, 1, v___x_73_);
lean_ctor_set(v_startTag_76_, 2, v_attrs_69_);
lean_ctor_set(v_startTag_76_, 3, v___x_75_);
v___x_77_ = l_Lean_Syntax_getNumArgs(v_stx_56_);
v___x_78_ = lean_unsigned_to_nat(4u);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_77_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_endTag_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_80_ = lean_unsigned_to_nat(5u);
v___x_81_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(6u);
v___x_83_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_82_);
v___x_84_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5));
v___x_85_ = lean_unsigned_to_nat(7u);
v___x_86_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_85_);
v_endTag_87_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_87_, 0, v___x_81_);
lean_ctor_set(v_endTag_87_, 1, v___x_83_);
lean_ctor_set(v_endTag_87_, 2, v___x_84_);
lean_ctor_set(v_endTag_87_, 3, v___x_86_);
v___x_88_ = l_Lean_Syntax_getArg(v_stx_56_, v___x_78_);
lean_dec(v_stx_56_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v_endTag_87_);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v_startTag_76_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_stx_56_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_94_, 0, v_startTag_76_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
lean_ctor_set(v___x_94_, 2, v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_56_ = stack[0].m_obj;
lean_object* v___y_57_ = stack[1].m_obj;
lean_object* v___y_58_ = stack[2].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_56_, v___y_57_, v___y_58_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___boxed(lean_object* v_stx_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_101_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_102_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__0);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_106_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
lean_ctor_set(v___x_108_, 2, v___x_107_);
lean_ctor_set(v___x_108_, 3, v___x_107_);
lean_ctor_set(v___x_108_, 4, v___x_106_);
lean_ctor_set(v___x_108_, 5, v___x_106_);
lean_ctor_set(v___x_108_, 6, v___x_106_);
lean_ctor_set(v___x_108_, 7, v___x_106_);
lean_ctor_set(v___x_108_, 8, v___x_106_);
lean_ctor_set(v___x_108_, 9, v___x_106_);
lean_ctor_set(v___x_108_, 10, v___x_106_);
lean_ctor_set(v___x_108_, 11, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_unsigned_to_nat(32u);
v___x_110_ = lean_mk_empty_array_with_capacity(v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4(void){
_start:
{
size_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = ((size_t)5ULL);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_unsigned_to_nat(32u);
v___x_115_ = lean_mk_empty_array_with_capacity(v___x_114_);
v___x_116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3);
v___x_117_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_113_);
lean_ctor_set(v___x_117_, 3, v___x_113_);
lean_ctor_set_usize(v___x_117_, 4, v___x_112_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_box(1);
v___x_119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4);
v___x_120_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1);
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(lean_object* v_msgData_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; lean_object* v_toCold_127_; lean_object* v_env_128_; lean_object* v_options_129_; uint8_t v___x_130_; lean_object* v_env_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_126_ = lean_st_ref_get(v___y_124_);
v_toCold_127_ = lean_ctor_get(v___y_123_, 0);
v_env_128_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_env_128_);
lean_dec(v___x_126_);
v_options_129_ = lean_ctor_get(v_toCold_127_, 2);
v___x_130_ = 0;
v_env_131_ = l_Lean_Environment_setRecordingDeps(v_env_128_, v___x_130_);
v___x_132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2);
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5);
lean_inc_ref(v_options_129_);
v___x_134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_134_, 0, v_env_131_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_ctor_set(v___x_134_, 3, v_options_129_);
v___x_135_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_msgData_122_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_122_ = stack[0].m_obj;
lean_object* v___y_123_ = stack[1].m_obj;
lean_object* v___y_124_ = stack[2].m_obj;
lean_object* v_res_137_;
v_res_137_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(v_msgData_122_, v___y_123_, v___y_124_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___boxed(lean_object* v_msgData_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(v_msgData_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_142_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(lean_object* v_msg_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_ref_147_; lean_object* v___x_148_; lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_ref_147_ = lean_ctor_get(v___y_144_, 2);
v___x_148_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(v_msg_143_, v___y_144_, v___y_145_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
lean_inc(v_ref_147_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_ref_147_);
lean_ctor_set(v___x_153_, 1, v_a_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 1);
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_143_ = stack[0].m_obj;
lean_object* v___y_144_ = stack[1].m_obj;
lean_object* v___y_145_ = stack[2].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_143_, v___y_144_, v___y_145_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg___boxed(lean_object* v_msg_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_163_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(lean_object* v_ref_164_, lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_toCold_169_; lean_object* v_currRecDepth_170_; lean_object* v_ref_171_; uint16_t v_optionFlags_172_; uint8_t v_suppressElabErrors_173_; uint8_t v_isRecordingDeps_174_; lean_object* v_ref_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_toCold_169_ = lean_ctor_get(v___y_166_, 0);
v_currRecDepth_170_ = lean_ctor_get(v___y_166_, 1);
v_ref_171_ = lean_ctor_get(v___y_166_, 2);
v_optionFlags_172_ = lean_ctor_get_uint16(v___y_166_, sizeof(void*)*3);
v_suppressElabErrors_173_ = lean_ctor_get_uint8(v___y_166_, sizeof(void*)*3 + 2);
v_isRecordingDeps_174_ = lean_ctor_get_uint8(v___y_166_, sizeof(void*)*3 + 3);
v_ref_175_ = l_Lean_replaceRef(v_ref_164_, v_ref_171_);
lean_inc(v_currRecDepth_170_);
lean_inc_ref(v_toCold_169_);
v___x_176_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_176_, 0, v_toCold_169_);
lean_ctor_set(v___x_176_, 1, v_currRecDepth_170_);
lean_ctor_set(v___x_176_, 2, v_ref_175_);
lean_ctor_set_uint16(v___x_176_, sizeof(void*)*3, v_optionFlags_172_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*3 + 2, v_suppressElabErrors_173_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*3 + 3, v_isRecordingDeps_174_);
v___x_177_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_165_, v___x_176_, v___y_167_);
lean_dec_ref_known(v___x_176_, 3);
return v___x_177_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_164_ = stack[0].m_obj;
lean_object* v_msg_165_ = stack[1].m_obj;
lean_object* v___y_166_ = stack[2].m_obj;
lean_object* v___y_167_ = stack[3].m_obj;
lean_object* v_res_178_;
v_res_178_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_ref_164_, v_msg_165_, v___y_166_, v___y_167_);
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg___boxed(lean_object* v_ref_179_, lean_object* v_msg_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_ref_179_, v_msg_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v_ref_179_);
return v_res_184_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(lean_object* v_x_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
if (lean_obj_tag(v_x_185_) == 1)
{
lean_object* v_args_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_args_189_ = lean_ctor_get(v_x_185_, 2);
v___x_190_ = lean_array_get_size(v_args_189_);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_dec_eq(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_array_fget_borrowed(v_args_189_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 2)
{
lean_object* v_val_196_; lean_object* v___x_197_; 
v_val_196_ = lean_ctor_get(v___x_195_, 1);
lean_inc_ref(v_val_196_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_val_196_);
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_198_;
}
}
}
else
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_199_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_185_ = stack[0].m_obj;
lean_object* v___y_186_ = stack[1].m_obj;
lean_object* v___y_187_ = stack[2].m_obj;
lean_object* v_res_200_;
v_res_200_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_x_185_, v___y_186_, v___y_187_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg___boxed(lean_object* v_x_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_x_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v_x_201_);
return v_res_205_;
}
}
lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(lean_object* v_a_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_a_206_, v___y_207_, v___y_208_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_206_ = stack[0].m_obj;
lean_object* v___y_207_ = stack[1].m_obj;
lean_object* v___y_208_ = stack[2].m_obj;
lean_object* v_res_211_;
v_res_211_ = l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(v_a_206_, v___y_207_, v___y_208_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1___boxed(lean_object* v_a_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(v_a_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v_a_212_);
return v_res_216_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__0));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__2));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__4));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__6));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch(lean_object* v_stx_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_316_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_316_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_316_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_316_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_endTag_x3f_238_; 
v_endTag_x3f_238_ = lean_ctor_get(v_a_234_, 2);
lean_inc(v_endTag_x3f_238_);
if (lean_obj_tag(v_endTag_x3f_238_) == 1)
{
lean_object* v_startTag_239_; lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_311_; 
lean_del_object(v___x_236_);
v_startTag_239_ = lean_ctor_get(v_a_234_, 0);
lean_inc_ref(v_startTag_239_);
lean_dec(v_a_234_);
v_val_240_ = lean_ctor_get(v_endTag_x3f_238_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_endTag_x3f_238_);
if (v_isSharedCheck_311_ == 0)
{
v___x_242_ = v_endTag_x3f_238_;
v_isShared_243_ = v_isSharedCheck_311_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v_endTag_x3f_238_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_311_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_name_244_; lean_object* v___x_245_; 
v_name_244_ = lean_ctor_get(v_startTag_239_, 1);
lean_inc(v_name_244_);
lean_dec_ref(v_startTag_239_);
v___x_245_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_244_, v_a_230_, v_a_231_);
lean_dec(v_name_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v_name_247_; lean_object* v___x_248_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
v_name_247_ = lean_ctor_get(v_val_240_, 1);
lean_inc(v_name_247_);
lean_dec(v_val_240_);
v___x_248_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_247_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_294_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_294_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_294_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_294_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_253_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_249_);
v___x_254_ = l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(v_a_249_, v___x_253_);
lean_inc(v_a_246_);
v___x_255_ = l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(v_a_246_, v___x_253_);
v___x_256_ = lean_string_dec_eq(v___x_254_, v___x_255_);
lean_dec_ref(v___x_255_);
lean_dec_ref(v___x_254_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
lean_del_object(v___x_251_);
v___x_257_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1);
lean_inc(v_a_246_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_a_246_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_ctor_set(v___x_260_, 2, v___x_259_);
lean_ctor_set(v___x_260_, 3, v___x_259_);
lean_ctor_set(v___x_260_, 4, v___x_259_);
lean_ctor_set(v___x_260_, 5, v___x_259_);
v___x_261_ = 0;
v___x_262_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_259_);
lean_ctor_set(v___x_262_, 2, v___x_259_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*3, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_265_ = lean_array_push(v___x_264_, v___x_262_);
lean_inc(v_name_247_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v_name_247_);
v___x_267_ = v___x_242_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_name_247_);
v___x_267_ = v_reuseFailAlloc_289_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_MessageData_hint(v___x_257_, v___x_265_, v___x_267_, v___x_259_, v___x_256_, v_a_230_, v_a_231_);
lean_dec_ref(v___x_265_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3);
v___x_271_ = l_Lean_stringToMessageData(v_a_246_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_stringToMessageData(v_a_249_);
v___x_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_a_269_);
v___x_280_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_name_247_, v___x_279_, v_a_230_, v_a_231_);
lean_dec(v_name_247_);
return v___x_280_;
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec(v_a_249_);
lean_dec(v_name_247_);
lean_dec(v_a_246_);
v_a_281_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_268_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_268_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_292_; 
lean_dec(v_a_249_);
lean_dec(v_name_247_);
lean_dec(v_a_246_);
lean_del_object(v___x_242_);
v___x_290_ = lean_box(0);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_290_);
v___x_292_ = v___x_251_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_name_247_);
lean_dec(v_a_246_);
lean_del_object(v___x_242_);
v_a_295_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_248_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_248_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_del_object(v___x_242_);
lean_dec(v_val_240_);
v_a_303_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_245_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_245_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec(v_endTag_x3f_238_);
lean_dec(v_a_234_);
v___x_312_ = lean_box(0);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_312_);
v___x_314_ = v___x_236_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_a_317_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_233_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_233_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Element_checkNamesMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_229_ = stack[0].m_obj;
lean_object* v_a_230_ = stack[1].m_obj;
lean_object* v_a_231_ = stack[2].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_229_, v_a_230_, v_a_231_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___boxed(lean_object* v_stx_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_330_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(lean_object* v_00_u03b1_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_335_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_332_ = stack[1].m_obj;
lean_object* v___y_333_ = stack[2].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(lean_box(0), v___y_332_, v___y_333_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b1_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(v_00_u03b1_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_341_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(lean_object* v_00_u03b1_342_, lean_object* v_ref_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_ref_343_, v_msg_344_, v___y_345_, v___y_346_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_343_ = stack[1].m_obj;
lean_object* v_msg_344_ = stack[2].m_obj;
lean_object* v___y_345_ = stack[3].m_obj;
lean_object* v___y_346_ = stack[4].m_obj;
lean_object* v_res_349_;
v_res_349_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(lean_box(0), v_ref_343_, v_msg_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___boxed(lean_object* v_00_u03b1_350_, lean_object* v_ref_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(v_00_u03b1_350_, v_ref_351_, v_msg_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v_ref_351_);
return v_res_356_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3(lean_object* v_k_357_, lean_object* v_x_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_x_358_, v___y_359_, v___y_360_);
return v___x_362_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_357_ = stack[0].m_obj;
lean_object* v_x_358_ = stack[1].m_obj;
lean_object* v___y_359_ = stack[2].m_obj;
lean_object* v___y_360_ = stack[3].m_obj;
lean_object* v_res_363_;
v_res_363_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3(v_k_357_, v_x_358_, v___y_359_, v___y_360_);
stack->m_obj
 = v_res_363_;
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
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_371_ = stack[1].m_obj;
lean_object* v___y_372_ = stack[2].m_obj;
lean_object* v___y_373_ = stack[3].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6(lean_box(0), v_msg_371_, v___y_372_, v___y_373_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___boxed(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6(v_00_u03b1_377_, v_msg_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__0));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__2));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__6));
v___x_394_ = l_Lean_MessageData_ofFormat(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren(lean_object* v_stx_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
lean_inc(v_stx_398_);
v___x_402_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_491_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_491_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_491_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_491_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_children_x3f_407_; 
v_children_x3f_407_ = lean_ctor_get(v_a_403_, 1);
if (lean_obj_tag(v_children_x3f_407_) == 1)
{
lean_object* v_startTag_408_; lean_object* v_lt_409_; lean_object* v_name_410_; lean_object* v_gt_411_; lean_object* v___x_412_; 
lean_del_object(v___x_405_);
v_startTag_408_ = lean_ctor_get(v_a_403_, 0);
lean_inc_ref(v_startTag_408_);
lean_dec(v_a_403_);
v_lt_409_ = lean_ctor_get(v_startTag_408_, 0);
lean_inc(v_lt_409_);
v_name_410_ = lean_ctor_get(v_startTag_408_, 1);
lean_inc(v_name_410_);
v_gt_411_ = lean_ctor_get(v_startTag_408_, 3);
lean_inc(v_gt_411_);
lean_dec_ref(v_startTag_408_);
v___x_412_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_410_, v_a_399_, v_a_400_);
lean_dec(v_name_410_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_478_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_478_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_478_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_478_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_hint_418_; lean_object* v___y_419_; lean_object* v___y_420_; uint8_t v___x_428_; 
lean_inc(v_a_413_);
v___x_428_ = l_Lean_Html_isVoidElement(v_a_413_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec(v_a_413_);
lean_dec(v_gt_411_);
lean_dec(v_lt_409_);
lean_dec(v_stx_398_);
v___x_429_ = lean_box(0);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_429_);
v___x_431_ = v___x_415_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
else
{
uint8_t v___x_433_; lean_object* v___x_434_; 
lean_del_object(v___x_415_);
v___x_433_ = 0;
v___x_434_ = l_Lean_Syntax_getPos_x3f(v_lt_409_, v___x_433_);
lean_dec(v_lt_409_);
if (lean_obj_tag(v___x_434_) == 1)
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_476_; 
v_val_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_476_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_476_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_476_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Syntax_getPos_x3f(v_gt_411_, v___x_433_);
lean_dec(v_gt_411_);
if (lean_obj_tag(v___x_439_) == 1)
{
lean_object* v_toCold_440_; lean_object* v_fileMap_441_; lean_object* v_val_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_474_; 
v_toCold_440_ = lean_ctor_get(v_a_399_, 0);
v_fileMap_441_ = lean_ctor_get(v_toCold_440_, 1);
v_val_442_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_474_ == 0)
{
v___x_444_ = v___x_439_;
v_isShared_445_ = v_isSharedCheck_474_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_val_442_);
lean_dec(v___x_439_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_474_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_source_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v_source_446_ = lean_ctor_get(v_fileMap_441_, 0);
v___x_447_ = lean_string_utf8_extract(v_source_446_, v_val_435_, v_val_442_);
lean_dec(v_val_442_);
lean_dec(v_val_435_);
v___x_448_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__4));
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
v___x_450_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__7);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_449_);
v___x_452_ = v___x_437_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_449_);
v___x_452_ = v_reuseFailAlloc_473_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
lean_ctor_set(v___x_454_, 2, v___x_453_);
lean_ctor_set(v___x_454_, 3, v___x_453_);
lean_ctor_set(v___x_454_, 4, v___x_453_);
lean_ctor_set(v___x_454_, 5, v___x_453_);
v___x_455_ = 0;
v___x_456_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_453_);
lean_ctor_set(v___x_456_, 2, v___x_453_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*3, v___x_455_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_mk_empty_array_with_capacity(v___x_457_);
v___x_459_ = lean_array_push(v___x_458_, v___x_456_);
lean_inc(v_stx_398_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_stx_398_);
v___x_461_ = v___x_444_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_stx_398_);
v___x_461_ = v_reuseFailAlloc_472_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_MessageData_hint(v___x_450_, v___x_459_, v___x_461_, v___x_453_, v___x_433_, v_a_399_, v_a_400_);
lean_dec_ref(v___x_459_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v_hint_418_ = v_a_463_;
v___y_419_ = v_a_399_;
v___y_420_ = v_a_400_;
goto v___jp_417_;
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_a_413_);
lean_dec(v_stx_398_);
v_a_464_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_462_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_475_; 
lean_dec(v___x_439_);
lean_del_object(v___x_437_);
lean_dec(v_val_435_);
v___x_475_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9);
v_hint_418_ = v___x_475_;
v___y_419_ = v_a_399_;
v___y_420_ = v_a_400_;
goto v___jp_417_;
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec(v___x_434_);
lean_dec(v_gt_411_);
v___x_477_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__9);
v_hint_418_ = v___x_477_;
v___y_419_ = v_a_399_;
v___y_420_ = v_a_400_;
goto v___jp_417_;
}
}
v___jp_417_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_421_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__1);
v___x_422_ = l_Lean_stringToMessageData(v_a_413_);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3, &l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3_once, _init_l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__3);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_hint_418_);
v___x_427_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_stx_398_, v___x_426_, v___y_419_, v___y_420_);
lean_dec(v_stx_398_);
return v___x_427_;
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec(v_gt_411_);
lean_dec(v_lt_409_);
lean_dec(v_stx_398_);
v_a_479_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_412_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_412_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec(v_a_403_);
lean_dec(v_stx_398_);
v___x_487_ = lean_box(0);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_487_);
v___x_489_ = v___x_405_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_stx_398_);
v_a_492_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_402_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_402_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Element_checkNoVoidChildren_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_398_ = stack[0].m_obj;
lean_object* v_a_399_ = stack[1].m_obj;
lean_object* v_a_400_ = stack[2].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_398_, v_a_399_, v_a_400_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___boxed(lean_object* v_stx_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
return v_res_505_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_509_;
v_res_509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg___boxed(lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v_res_511_;
}
}
lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(uint8_t v_isMany_524_, lean_object* v_stx_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___y_535_; 
lean_inc(v_stx_525_);
v___x_533_ = l_Lean_Syntax_getKind(v_stx_525_);
if (v_isMany_524_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___y_535_ = v___x_546_;
goto v___jp_534_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___y_535_ = v___x_547_;
goto v___jp_534_;
}
v___jp_534_:
{
uint8_t v___x_536_; 
v___x_536_ = lean_name_eq(v___x_533_, v___y_535_);
lean_dec(v___x_533_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v_stx_525_);
v___x_537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = l_Lean_Syntax_getArg(v_stx_525_, v___x_538_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = l_Lean_Syntax_getArg(v_stx_525_, v___x_540_);
v___x_542_ = lean_unsigned_to_nat(2u);
v___x_543_ = l_Lean_Syntax_getArg(v_stx_525_, v___x_542_);
lean_dec(v_stx_525_);
v___x_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_544_, 0, v___x_539_);
lean_ctor_set(v___x_544_, 1, v___x_541_);
lean_ctor_set(v___x_544_, 2, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_isMany_524_ = stack[0].m_num;
lean_object* v_stx_525_ = stack[1].m_obj;
lean_object* v___y_526_ = stack[2].m_obj;
lean_object* v___y_527_ = stack[3].m_obj;
lean_object* v___y_528_ = stack[4].m_obj;
lean_object* v___y_529_ = stack[5].m_obj;
lean_object* v___y_530_ = stack[6].m_obj;
lean_object* v___y_531_ = stack[7].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_524_, v_stx_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___boxed(lean_object* v_isMany_549_, lean_object* v_stx_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v_isMany_boxed_558_; lean_object* v_res_559_; 
v_isMany_boxed_558_ = lean_unbox(v_isMany_549_);
v_res_559_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_boxed_558_, v_stx_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_559_;
}
}
lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(lean_object* v_stx_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_c_572_; lean_object* v___x_573_; lean_object* v___y_575_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v_c_572_ = l_Lean_Syntax_getArg(v_stx_563_, v___x_571_);
lean_inc(v_c_572_);
v___x_573_ = l_Lean_Syntax_getKind(v_c_572_);
v___x_580_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__1));
v___x_581_ = lean_name_eq(v___x_573_, v___x_580_);
if (v___x_581_ == 0)
{
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___y_575_ = v___x_582_;
goto v___jp_574_;
}
else
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___x_573_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_c_572_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
v___jp_574_:
{
uint8_t v___x_576_; 
v___x_576_ = lean_name_eq(v___x_573_, v___y_575_);
lean_dec(v___x_573_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v_c_572_);
v___x_577_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_c_572_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_563_ = stack[0].m_obj;
lean_object* v___y_564_ = stack[1].m_obj;
lean_object* v___y_565_ = stack[2].m_obj;
lean_object* v___y_566_ = stack[3].m_obj;
lean_object* v___y_567_ = stack[4].m_obj;
lean_object* v___y_568_ = stack[5].m_obj;
lean_object* v___y_569_ = stack[6].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___boxed(lean_object* v_stx_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v_stx_587_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v___x_600_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_601_ = l_Lean_Expr_const___override(v___x_600_, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(lean_object* v_stx_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_toCold_612_; lean_object* v_currRecDepth_613_; lean_object* v_ref_614_; uint16_t v_optionFlags_615_; uint8_t v_suppressElabErrors_616_; uint8_t v_isRecordingDeps_617_; lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_toCold_612_ = lean_ctor_get(v_a_609_, 0);
v_currRecDepth_613_ = lean_ctor_get(v_a_609_, 1);
v_ref_614_ = lean_ctor_get(v_a_609_, 2);
v_optionFlags_615_ = lean_ctor_get_uint16(v_a_609_, sizeof(void*)*3);
v_suppressElabErrors_616_ = lean_ctor_get_uint8(v_a_609_, sizeof(void*)*3 + 2);
v_isRecordingDeps_617_ = lean_ctor_get_uint8(v_a_609_, sizeof(void*)*3 + 3);
v_ref_618_ = l_Lean_replaceRef(v_stx_604_, v_ref_614_);
lean_inc(v_currRecDepth_613_);
lean_inc_ref(v_toCold_612_);
v___x_619_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_619_, 0, v_toCold_612_);
lean_ctor_set(v___x_619_, 1, v_currRecDepth_613_);
lean_ctor_set(v___x_619_, 2, v_ref_618_);
lean_ctor_set_uint16(v___x_619_, sizeof(void*)*3, v_optionFlags_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 2, v_suppressElabErrors_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 3, v_isRecordingDeps_617_);
v___x_620_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v___x_619_, v_a_610_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
if (lean_obj_tag(v_a_621_) == 0)
{
lean_object* v_stx_622_; lean_object* v___x_623_; 
v_stx_622_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_stx_622_);
lean_dec_ref_known(v_a_621_, 1);
v___x_623_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_stx_622_, v___x_619_, v_a_610_);
lean_dec_ref_known(v___x_619_, 3);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = l_Lean_mkStrLit(v_a_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_623_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_623_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_stx_641_; uint8_t v___x_642_; lean_object* v___x_643_; 
v_stx_641_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_stx_641_);
lean_dec_ref_known(v_a_621_, 1);
v___x_642_ = 0;
v___x_643_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v___x_642_, v_stx_641_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v___x_619_, v_a_610_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v_term_645_; lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v_term_645_ = lean_ctor_get(v_a_644_, 1);
lean_inc(v_term_645_);
lean_dec(v_a_644_);
v___x_646_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3);
v___x_647_ = 1;
v___x_648_ = lean_box(0);
v___x_649_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_645_, v___x_646_, v___x_647_, v___x_647_, v___x_648_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v___x_619_, v_a_610_);
lean_dec_ref_known(v___x_619_, 3);
return v___x_649_;
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref_known(v___x_619_, 3);
v_a_650_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_643_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_643_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref_known(v___x_619_, 3);
v_a_658_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_620_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_620_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_604_ = stack[0].m_obj;
lean_object* v_a_605_ = stack[1].m_obj;
lean_object* v_a_606_ = stack[2].m_obj;
lean_object* v_a_607_ = stack[3].m_obj;
lean_object* v_a_608_ = stack[4].m_obj;
lean_object* v_a_609_ = stack[5].m_obj;
lean_object* v_a_610_ = stack[6].m_obj;
lean_object* v_res_666_;
v_res_666_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_stx_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___boxed(lean_object* v_stx_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_stx_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_stx_667_);
return v_res_675_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(lean_object* v_00_u03b1_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_684_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_677_ = stack[1].m_obj;
lean_object* v___y_678_ = stack[2].m_obj;
lean_object* v___y_679_ = stack[3].m_obj;
lean_object* v___y_680_ = stack[4].m_obj;
lean_object* v___y_681_ = stack[5].m_obj;
lean_object* v___y_682_ = stack[6].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(lean_box(0), v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___boxed(lean_object* v_00_u03b1_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(v_00_u03b1_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_694_;
}
}
lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(lean_object* v_stx_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_c_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v_c_704_ = l_Lean_Syntax_getArg(v_stx_701_, v___x_703_);
lean_inc(v_c_704_);
v___x_705_ = l_Lean_Syntax_getKind(v_c_704_);
v___x_706_ = ((lean_object*)(l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1));
v___x_707_ = lean_name_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___y_711_; 
v___x_708_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_709_ = lean_name_eq(v___x_705_, v___x_708_);
if (v___x_709_ == 0)
{
if (v___x_709_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___y_711_ = v___x_716_;
goto v___jp_710_;
}
else
{
v___y_711_ = v___x_708_;
goto v___jp_710_;
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v___x_705_);
v___x_717_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_717_, 0, v_c_704_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*1, v___x_709_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
v___jp_710_:
{
uint8_t v___x_712_; 
v___x_712_ = lean_name_eq(v___x_705_, v___y_711_);
lean_dec(v___x_705_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec(v_c_704_);
v___x_713_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_713_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_714_, 0, v_c_704_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*1, v___x_709_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
}
else
{
lean_object* v___x_719_; lean_object* v_val_x3f_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
lean_dec(v___x_705_);
v___x_719_ = lean_unsigned_to_nat(1u);
v_val_x3f_720_ = l_Lean_Syntax_getArg(v_stx_701_, v___x_719_);
v___x_721_ = l_Lean_Syntax_getNumArgs(v_val_x3f_720_);
v___x_722_ = lean_nat_dec_eq(v___x_721_, v___x_703_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_723_ = l_Lean_Syntax_getArg(v_val_x3f_720_, v___x_703_);
v___x_724_ = l_Lean_Syntax_getArg(v_val_x3f_720_, v___x_719_);
lean_dec(v_val_x3f_720_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v_c_704_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v_val_x3f_720_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_c_704_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_701_ = stack[0].m_obj;
lean_object* v_res_730_;
v_res_730_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_701_);
stack->m_obj
 = v_res_730_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___boxed(lean_object* v_stx_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_731_);
lean_dec(v_stx_731_);
return v_res_733_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 1)
{
lean_object* v_args_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_args_736_ = lean_ctor_get(v_x_734_, 2);
v___x_737_ = lean_array_get_size(v_args_736_);
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_dec_eq(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_array_fget_borrowed(v_args_736_, v___x_741_);
if (lean_obj_tag(v___x_742_) == 2)
{
lean_object* v_val_743_; lean_object* v___x_744_; 
v_val_743_ = lean_ctor_get(v___x_742_, 1);
lean_inc_ref(v_val_743_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_val_743_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_745_;
}
}
}
else
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_746_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_734_ = stack[0].m_obj;
lean_object* v_res_747_;
v_res_747_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_734_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg___boxed(lean_object* v_x_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_748_);
lean_dec(v_x_748_);
return v_res_750_;
}
}
lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(lean_object* v_a_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_751_);
return v___x_759_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_751_ = stack[0].m_obj;
lean_object* v___y_752_ = stack[1].m_obj;
lean_object* v___y_753_ = stack[2].m_obj;
lean_object* v___y_754_ = stack[3].m_obj;
lean_object* v___y_755_ = stack[4].m_obj;
lean_object* v___y_756_ = stack[5].m_obj;
lean_object* v___y_757_ = stack[6].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(v_a_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1___boxed(lean_object* v_a_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(v_a_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v_a_761_);
return v_res_769_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l_Lean_Level_ofNat(v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_box(0);
v___x_776_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
return v___x_777_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_779_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_778_);
return v___x_780_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_782_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1));
v___x_783_ = l_Lean_Expr_const___override(v___x_782_, v___x_781_);
return v___x_783_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6(void){
_start:
{
lean_object* v_strType_784_; lean_object* v___x_785_; lean_object* v_pairType_786_; 
v_strType_784_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_785_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5);
v_pairType_786_ = l_Lean_mkAppB(v___x_785_, v_strType_784_, v_strType_784_);
return v_pairType_786_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_791_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8));
v___x_792_ = l_Lean_Expr_const___override(v___x_791_, v___x_790_);
return v___x_792_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10(void){
_start:
{
lean_object* v_pairType_793_; lean_object* v___x_794_; lean_object* v_arrayType_795_; 
v_pairType_793_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_794_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9);
v_arrayType_795_ = l_Lean_Expr_app___override(v___x_794_, v_pairType_793_);
return v_arrayType_795_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_801_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12));
v___x_802_ = l_Lean_Expr_const___override(v___x_801_, v___x_800_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8));
v___x_804_ = l_Lean_mkStrLit(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15(void){
_start:
{
lean_object* v_pairType_805_; lean_object* v___x_806_; 
v_pairType_805_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_pairType_805_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20));
v___x_817_ = l_String_toRawSubstring_x27(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30));
v___x_838_ = l_String_toRawSubstring_x27(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0));
v___x_846_ = l_String_toRawSubstring_x27(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47(void){
_start:
{
lean_object* v_arrayType_869_; lean_object* v___x_870_; 
v_arrayType_869_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v_arrayType_869_);
return v___x_870_;
}
}
lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(lean_object* v_stx_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_strType_881_; lean_object* v_toCold_882_; lean_object* v_currRecDepth_883_; lean_object* v_ref_884_; uint16_t v_optionFlags_885_; uint8_t v_suppressElabErrors_886_; uint8_t v_isRecordingDeps_887_; lean_object* v_ref_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_880_ = lean_box(0);
v_strType_881_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v_toCold_882_ = lean_ctor_get(v_a_876_, 0);
v_currRecDepth_883_ = lean_ctor_get(v_a_876_, 1);
v_ref_884_ = lean_ctor_get(v_a_876_, 2);
v_optionFlags_885_ = lean_ctor_get_uint16(v_a_876_, sizeof(void*)*3);
v_suppressElabErrors_886_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*3 + 2);
v_isRecordingDeps_887_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*3 + 3);
v_ref_888_ = l_Lean_replaceRef(v_stx_871_, v_ref_884_);
lean_inc(v_ref_888_);
lean_inc(v_currRecDepth_883_);
lean_inc_ref(v_toCold_882_);
v___x_889_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_889_, 0, v_toCold_882_);
lean_ctor_set(v___x_889_, 1, v_currRecDepth_883_);
lean_ctor_set(v___x_889_, 2, v_ref_888_);
lean_ctor_set_uint16(v___x_889_, sizeof(void*)*3, v_optionFlags_885_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*3 + 2, v_suppressElabErrors_886_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*3 + 3, v_isRecordingDeps_887_);
v___x_890_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_871_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
switch(lean_obj_tag(v_a_891_))
{
case 0:
{
lean_object* v_stx_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_ref_888_);
v_stx_892_ = lean_ctor_get(v_a_891_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_931_ == 0)
{
v___x_894_ = v_a_891_;
v_isShared_895_ = v_isSharedCheck_931_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_stx_892_);
lean_dec(v_a_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_931_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_name_896_; lean_object* v_val_897_; lean_object* v___x_898_; 
v_name_896_ = lean_ctor_get(v_stx_892_, 0);
lean_inc(v_name_896_);
v_val_897_ = lean_ctor_get(v_stx_892_, 2);
lean_inc(v_val_897_);
lean_dec_ref(v_stx_892_);
v___x_898_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_896_);
lean_dec(v_name_896_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_val_897_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v___x_889_, v_a_877_);
lean_dec_ref_known(v___x_889_, 3);
lean_dec(v_val_897_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_914_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_914_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_905_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_906_ = l_Lean_mkStrLit(v_a_899_);
v___x_907_ = l_Lean_mkApp4(v___x_905_, v_strType_881_, v_strType_881_, v___x_906_, v_a_901_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_907_);
v___x_909_ = v___x_894_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_909_);
v___x_911_ = v___x_903_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_a_899_);
lean_del_object(v___x_894_);
v_a_915_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_900_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_900_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_val_897_);
lean_del_object(v___x_894_);
lean_dec_ref_known(v___x_889_, 3);
v_a_923_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_898_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_898_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
case 1:
{
lean_object* v_stx_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref_known(v___x_889_, 3);
lean_dec(v_ref_888_);
v_stx_932_ = lean_ctor_get(v_a_891_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_960_ == 0)
{
v___x_934_ = v_a_891_;
v_isShared_935_ = v_isSharedCheck_960_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_stx_932_);
lean_dec(v_a_891_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_960_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_stx_932_);
lean_dec(v_stx_932_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_951_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_951_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_941_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_942_ = l_Lean_mkStrLit(v_a_937_);
v___x_943_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14);
v___x_944_ = l_Lean_mkApp4(v___x_941_, v_strType_881_, v_strType_881_, v___x_942_, v___x_943_);
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 0);
lean_ctor_set(v___x_934_, 0, v___x_944_);
v___x_946_ = v___x_934_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_946_);
v___x_948_ = v___x_939_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_934_);
v_a_952_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_936_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_936_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
default: 
{
uint8_t v_isMany_961_; 
v_isMany_961_ = lean_ctor_get_uint8(v_a_891_, sizeof(void*)*1);
if (v_isMany_961_ == 0)
{
lean_object* v_stx_962_; lean_object* v___x_963_; 
lean_dec(v_ref_888_);
v_stx_962_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_stx_962_);
lean_dec_ref_known(v_a_891_, 1);
v___x_963_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_961_, v_stx_962_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v___x_889_, v_a_877_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v_term_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v_term_965_ = lean_ctor_get(v_a_964_, 1);
lean_inc(v_term_965_);
lean_dec(v_a_964_);
v___x_966_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15);
v___x_967_ = 1;
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_965_, v___x_966_, v___x_967_, v___x_967_, v___x_968_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v___x_889_, v_a_877_);
lean_dec_ref_known(v___x_889_, 3);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_a_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_a_979_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_969_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_969_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref_known(v___x_889_, 3);
v_a_987_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_963_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_963_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_stx_995_; lean_object* v___x_996_; 
v_stx_995_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_stx_995_);
lean_dec_ref_known(v_a_891_, 1);
v___x_996_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_961_, v_stx_995_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v___x_889_, v_a_877_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_quotContext_998_; lean_object* v_currMacroScope_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_term_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v_quotContext_998_ = lean_ctor_get(v_toCold_882_, 8);
v_currMacroScope_999_ = lean_ctor_get(v_toCold_882_, 9);
v___x_1000_ = 0;
v___x_1001_ = l_Lean_SourceInfo_fromRef(v_ref_888_, v___x_1000_);
lean_dec(v_ref_888_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_1003_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21);
v___x_1004_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24));
lean_inc_n(v_currMacroScope_999_, 3);
lean_inc_n(v_quotContext_998_, 3);
v___x_1005_ = l_Lean_addMacroScope(v_quotContext_998_, v___x_1004_, v_currMacroScope_999_);
v___x_1006_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26));
lean_inc_n(v___x_1001_, 10);
v___x_1007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1001_);
lean_ctor_set(v___x_1007_, 1, v___x_1003_);
lean_ctor_set(v___x_1007_, 2, v___x_1005_);
lean_ctor_set(v___x_1007_, 3, v___x_1006_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28));
v___x_1009_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29));
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1001_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31);
v___x_1012_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32));
v___x_1013_ = l_Lean_addMacroScope(v_quotContext_998_, v___x_1012_, v_currMacroScope_999_);
v___x_1014_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1001_);
lean_ctor_set(v___x_1014_, 1, v___x_1011_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
lean_ctor_set(v___x_1014_, 3, v___x_880_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33));
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1001_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35));
v___x_1018_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36);
v___x_1019_ = l_Lean_addMacroScope(v_quotContext_998_, v___x_879_, v_currMacroScope_999_);
v___x_1020_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42));
v___x_1021_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1001_);
lean_ctor_set(v___x_1021_, 1, v___x_1018_);
lean_ctor_set(v___x_1021_, 2, v___x_1019_);
lean_ctor_set(v___x_1021_, 3, v___x_1020_);
v___x_1022_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43));
v___x_1023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1001_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
lean_inc_ref(v___x_1021_);
v___x_1024_ = l_Lean_Syntax_node3(v___x_1001_, v___x_1017_, v___x_1021_, v___x_1023_, v___x_1021_);
v_term_1025_ = lean_ctor_get(v_a_997_, 1);
lean_inc(v_term_1025_);
lean_dec(v_a_997_);
v___x_1026_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44));
v___x_1027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1001_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1029_ = l_Lean_Syntax_node5(v___x_1001_, v___x_1008_, v___x_1010_, v___x_1014_, v___x_1016_, v___x_1024_, v___x_1027_);
v___x_1030_ = l_Lean_Syntax_node2(v___x_1001_, v___x_1028_, v___x_1029_, v_term_1025_);
v___x_1031_ = l_Lean_Syntax_node2(v___x_1001_, v___x_1002_, v___x_1007_, v___x_1030_);
v___x_1032_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47);
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1031_, v___x_1032_, v_isMany_961_, v_isMany_961_, v___x_1033_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v___x_889_, v_a_877_);
lean_dec_ref_known(v___x_889_, 3);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1034_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1034_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref_known(v___x_889_, 3);
lean_dec(v_ref_888_);
v_a_1052_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_996_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_996_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref_known(v___x_889_, 3);
lean_dec(v_ref_888_);
v_a_1060_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_890_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_890_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_871_ = stack[0].m_obj;
lean_object* v_a_872_ = stack[1].m_obj;
lean_object* v_a_873_ = stack[2].m_obj;
lean_object* v_a_874_ = stack[3].m_obj;
lean_object* v_a_875_ = stack[4].m_obj;
lean_object* v_a_876_ = stack[5].m_obj;
lean_object* v_a_877_ = stack[6].m_obj;
lean_object* v_res_1068_;
v_res_1068_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_stx_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
stack->m_obj
 = v_res_1068_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___boxed(lean_object* v_stx_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_stx_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_stx_1069_);
return v_res_1077_;
}
}
lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(lean_object* v_stx_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_1078_);
return v___x_1086_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1078_ = stack[0].m_obj;
lean_object* v___y_1079_ = stack[1].m_obj;
lean_object* v___y_1080_ = stack[2].m_obj;
lean_object* v___y_1081_ = stack[3].m_obj;
lean_object* v___y_1082_ = stack[4].m_obj;
lean_object* v___y_1083_ = stack[5].m_obj;
lean_object* v___y_1084_ = stack[6].m_obj;
lean_object* v_res_1087_;
v_res_1087_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(v_stx_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___boxed(lean_object* v_stx_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(v_stx_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v_stx_1088_);
return v_res_1096_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(lean_object* v_k_1097_, lean_object* v_x_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_1098_);
return v___x_1106_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1097_ = stack[0].m_obj;
lean_object* v_x_1098_ = stack[1].m_obj;
lean_object* v___y_1099_ = stack[2].m_obj;
lean_object* v___y_1100_ = stack[3].m_obj;
lean_object* v___y_1101_ = stack[4].m_obj;
lean_object* v___y_1102_ = stack[5].m_obj;
lean_object* v___y_1103_ = stack[6].m_obj;
lean_object* v___y_1104_ = stack[7].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(v_k_1097_, v_x_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___boxed(lean_object* v_k_1108_, lean_object* v_x_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(v_k_1108_, v_x_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v_x_1109_);
lean_dec(v_k_1108_);
return v_res_1117_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1));
v___x_1124_ = l_Lean_Expr_const___override(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4));
v___x_1131_ = l_Lean_Expr_const___override(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(lean_object* v_as_1132_, size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_b_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_a_1144_; lean_object* v_pairType_1148_; uint8_t v___x_1149_; 
v_pairType_1148_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1149_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_b_1135_);
return v___x_1150_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1152_; 
v_a_1151_ = lean_array_uget_borrowed(v_as_1132_, v_i_1134_);
v___x_1152_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_a_1151_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
if (lean_obj_tag(v_a_1153_) == 0)
{
lean_object* v_val_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_val_1154_ = lean_ctor_get(v_a_1153_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v_a_1153_, 1);
v___x_1155_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2);
v___x_1156_ = l_Lean_mkApp3(v___x_1155_, v_pairType_1148_, v_b_1135_, v_val_1154_);
v_a_1144_ = v___x_1156_;
goto v___jp_1143_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_val_1157_ = lean_ctor_get(v_a_1153_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v_a_1153_, 1);
v___x_1158_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5);
v___x_1159_ = l_Lean_mkApp3(v___x_1158_, v_pairType_1148_, v_b_1135_, v_val_1157_);
v_a_1144_ = v___x_1159_;
goto v___jp_1143_;
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_b_1135_);
v_a_1160_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1152_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1152_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
v___jp_1143_:
{
size_t v___x_1145_; size_t v___x_1146_; 
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1134_, v___x_1145_);
v_i_1134_ = v___x_1146_;
v_b_1135_ = v_a_1144_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1132_ = stack[0].m_obj;
size_t v_sz_1133_ = stack[1].m_num;
size_t v_i_1134_ = stack[2].m_num;
lean_object* v_b_1135_ = stack[3].m_obj;
lean_object* v___y_1136_ = stack[4].m_obj;
lean_object* v___y_1137_ = stack[5].m_obj;
lean_object* v___y_1138_ = stack[6].m_obj;
lean_object* v___y_1139_ = stack[7].m_obj;
lean_object* v___y_1140_ = stack[8].m_obj;
lean_object* v___y_1141_ = stack[9].m_obj;
lean_object* v_res_1168_;
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_as_1132_, v_sz_1133_, v_i_1134_, v_b_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
stack->m_obj
 = v_res_1168_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___boxed(lean_object* v_as_1169_, lean_object* v_sz_1170_, lean_object* v_i_1171_, lean_object* v_b_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
size_t v_sz_boxed_1180_; size_t v_i_boxed_1181_; lean_object* v_res_1182_; 
v_sz_boxed_1180_ = lean_unbox_usize(v_sz_1170_);
lean_dec(v_sz_1170_);
v_i_boxed_1181_ = lean_unbox_usize(v_i_1171_);
lean_dec(v_i_1171_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_as_1169_, v_sz_boxed_1180_, v_i_boxed_1181_, v_b_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec_ref(v_as_1169_);
return v_res_1182_;
}
}
lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(lean_object* v_stxs_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_pairType_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_box(0);
v_pairType_1192_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1193_ = l_Lean_Meta_mkArrayLit(v_pairType_1192_, v___x_1191_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; size_t v_sz_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v_sz_1195_ = lean_array_size(v_stxs_1183_);
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_stxs_1183_, v_sz_1195_, v___x_1196_, v_a_1194_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1197_;
}
else
{
return v___x_1193_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_0interp(lean_interpreter_value* stack)
{
lean_object* v_stxs_1183_ = stack[0].m_obj;
lean_object* v_a_1184_ = stack[1].m_obj;
lean_object* v_a_1185_ = stack[2].m_obj;
lean_object* v_a_1186_ = stack[3].m_obj;
lean_object* v_a_1187_ = stack[4].m_obj;
lean_object* v_a_1188_ = stack[5].m_obj;
lean_object* v_a_1189_ = stack[6].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_stxs_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs___boxed(lean_object* v_stxs_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_stxs_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec_ref(v_stxs_1199_);
return v_res_1207_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(lean_object* v___x_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1208_);
return v___x_1216_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1208_ = stack[0].m_obj;
lean_object* v___y_1209_ = stack[1].m_obj;
lean_object* v___y_1210_ = stack[2].m_obj;
lean_object* v___y_1211_ = stack[3].m_obj;
lean_object* v___y_1212_ = stack[4].m_obj;
lean_object* v___y_1213_ = stack[5].m_obj;
lean_object* v___y_1214_ = stack[6].m_obj;
lean_object* v_res_1217_;
v_res_1217_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(v___x_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed(lean_object* v___x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(v___x_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1226_;
}
}
lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(lean_object* v_stx_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___y_1237_; lean_object* v_k_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
lean_inc(v_stx_1228_);
v_k_1247_ = l_Lean_Syntax_getKind(v_stx_1228_);
v___x_1248_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_1249_ = lean_name_eq(v_k_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_1251_ = lean_name_eq(v_k_1247_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1253_ = lean_name_eq(v_k_1247_, v___x_1252_);
lean_dec(v_k_1247_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0));
v___y_1237_ = v___x_1254_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1255_; lean_object* v___f_1256_; 
lean_inc(v_stx_1228_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_stx_1228_);
v___f_1256_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1256_, 0, v___x_1255_);
v___y_1237_ = v___f_1256_;
goto v___jp_1236_;
}
}
else
{
lean_object* v___x_1257_; lean_object* v___f_1258_; 
lean_dec(v_k_1247_);
lean_inc(v_stx_1228_);
v___x_1257_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1257_, 0, v_stx_1228_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*1, v___x_1251_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1258_, 0, v___x_1257_);
v___y_1237_ = v___f_1258_;
goto v___jp_1236_;
}
}
else
{
uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; 
lean_dec(v_k_1247_);
v___x_1259_ = 0;
lean_inc(v_stx_1228_);
v___x_1260_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1260_, 0, v_stx_1228_);
lean_ctor_set_uint8(v___x_1260_, sizeof(void*)*1, v___x_1259_);
v___f_1261_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1261_, 0, v___x_1260_);
v___y_1237_ = v___f_1261_;
goto v___jp_1236_;
}
v___jp_1236_:
{
lean_object* v_toCold_1238_; lean_object* v_currRecDepth_1239_; lean_object* v_ref_1240_; uint16_t v_optionFlags_1241_; uint8_t v_suppressElabErrors_1242_; uint8_t v_isRecordingDeps_1243_; lean_object* v_ref_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_toCold_1238_ = lean_ctor_get(v___y_1233_, 0);
v_currRecDepth_1239_ = lean_ctor_get(v___y_1233_, 1);
v_ref_1240_ = lean_ctor_get(v___y_1233_, 2);
v_optionFlags_1241_ = lean_ctor_get_uint16(v___y_1233_, sizeof(void*)*3);
v_suppressElabErrors_1242_ = lean_ctor_get_uint8(v___y_1233_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1243_ = lean_ctor_get_uint8(v___y_1233_, sizeof(void*)*3 + 3);
v_ref_1244_ = l_Lean_replaceRef(v_stx_1228_, v_ref_1240_);
lean_dec(v_stx_1228_);
lean_inc(v_currRecDepth_1239_);
lean_inc_ref(v_toCold_1238_);
v___x_1245_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1245_, 0, v_toCold_1238_);
lean_ctor_set(v___x_1245_, 1, v_currRecDepth_1239_);
lean_ctor_set(v___x_1245_, 2, v_ref_1244_);
lean_ctor_set_uint16(v___x_1245_, sizeof(void*)*3, v_optionFlags_1241_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3 + 2, v_suppressElabErrors_1242_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3 + 3, v_isRecordingDeps_1243_);
lean_inc(v___y_1234_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
v___x_1246_ = lean_apply_7(v___y_1237_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___x_1245_, v___y_1234_, lean_box(0));
return v___x_1246_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1228_ = stack[0].m_obj;
lean_object* v___y_1229_ = stack[1].m_obj;
lean_object* v___y_1230_ = stack[2].m_obj;
lean_object* v___y_1231_ = stack[3].m_obj;
lean_object* v___y_1232_ = stack[4].m_obj;
lean_object* v___y_1233_ = stack[5].m_obj;
lean_object* v___y_1234_ = stack[6].m_obj;
lean_object* v_res_1262_;
v_res_1262_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_stx_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
stack->m_obj
 = v_res_1262_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___boxed(lean_object* v_stx_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_stx_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1271_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(lean_object* v_as_1286_, size_t v_sz_1287_, size_t v_i_1288_, lean_object* v_b_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_a_1298_; uint8_t v___x_1302_; 
v___x_1302_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_b_1289_);
return v___x_1303_;
}
else
{
lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1342_; 
v_fst_1304_ = lean_ctor_get(v_b_1289_, 0);
v_snd_1305_ = lean_ctor_get(v_b_1289_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_b_1289_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1307_ = v_b_1289_;
v_isShared_1308_ = v_isSharedCheck_1342_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snd_1305_);
lean_inc(v_fst_1304_);
lean_dec(v_b_1289_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1342_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_a_1309_ = lean_array_uget_borrowed(v_as_1286_, v_i_1288_);
lean_inc(v_a_1309_);
v___x_1310_ = l_Lean_Syntax_getKind(v_a_1309_);
v___x_1311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1));
v___x_1312_ = lean_name_eq(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3));
v___x_1314_ = lean_name_eq(v___x_1310_, v___x_1313_);
lean_dec(v___x_1310_);
if (v___x_1314_ == 0)
{
lean_object* v_tcs_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_tcs_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4));
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_snd_1305_);
v___x_1317_ = lean_array_push(v_fst_1304_, v___x_1316_);
lean_inc(v_a_1309_);
v___x_1318_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_a_1309_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = lean_array_push(v___x_1317_, v_a_1319_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_tcs_1315_);
lean_ctor_set(v___x_1307_, 0, v___x_1320_);
v___x_1322_ = v___x_1307_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_tcs_1315_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
v_a_1298_ = v___x_1322_;
goto v___jp_1297_;
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v___x_1317_);
lean_del_object(v___x_1307_);
v_a_1324_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1318_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1318_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
lean_inc(v_a_1309_);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_a_1309_);
v___x_1333_ = lean_array_push(v_snd_1305_, v___x_1332_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1333_);
v___x_1335_ = v___x_1307_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_fst_1304_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
v_a_1298_ = v___x_1335_;
goto v___jp_1297_;
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v___x_1310_);
lean_inc(v_a_1309_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1309_);
v___x_1338_ = lean_array_push(v_snd_1305_, v___x_1337_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1338_);
v___x_1340_ = v___x_1307_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_fst_1304_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v_a_1298_ = v___x_1340_;
goto v___jp_1297_;
}
}
}
}
v___jp_1297_:
{
size_t v___x_1299_; size_t v___x_1300_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1288_, v___x_1299_);
v_i_1288_ = v___x_1300_;
v_b_1289_ = v_a_1298_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1286_ = stack[0].m_obj;
size_t v_sz_1287_ = stack[1].m_num;
size_t v_i_1288_ = stack[2].m_num;
lean_object* v_b_1289_ = stack[3].m_obj;
lean_object* v___y_1290_ = stack[4].m_obj;
lean_object* v___y_1291_ = stack[5].m_obj;
lean_object* v___y_1292_ = stack[6].m_obj;
lean_object* v___y_1293_ = stack[7].m_obj;
lean_object* v___y_1294_ = stack[8].m_obj;
lean_object* v___y_1295_ = stack[9].m_obj;
lean_object* v_res_1343_;
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v_as_1286_, v_sz_1287_, v_i_1288_, v_b_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
stack->m_obj
 = v_res_1343_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___boxed(lean_object* v_as_1344_, lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_b_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
size_t v_sz_boxed_1355_; size_t v_i_boxed_1356_; lean_object* v_res_1357_; 
v_sz_boxed_1355_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1356_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v_as_1344_, v_sz_boxed_1355_, v_i_boxed_1356_, v_b_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v_as_1344_);
return v_res_1357_;
}
}
lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(lean_object* v_c_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; size_t v_sz_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = l_Lean_Syntax_getArgs(v_c_1362_);
v___x_1372_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1));
v_sz_1373_ = lean_array_size(v___x_1371_);
v___x_1374_ = ((size_t)0ULL);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v___x_1371_, v_sz_1373_, v___x_1374_, v___x_1372_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec_ref(v___x_1371_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1392_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1392_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1392_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_fst_1380_ = lean_ctor_get(v_a_1376_, 0);
lean_inc(v_fst_1380_);
v_snd_1381_ = lean_ctor_get(v_a_1376_, 1);
lean_inc(v_snd_1381_);
lean_dec(v_a_1376_);
v___x_1382_ = lean_array_get_size(v_snd_1381_);
v___x_1383_ = lean_nat_dec_eq(v___x_1382_, v___x_1370_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v_items_1385_; lean_object* v___x_1387_; 
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_snd_1381_);
v_items_1385_ = lean_array_push(v_fst_1380_, v___x_1384_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_items_1385_);
v___x_1387_ = v___x_1378_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_items_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_object* v___x_1390_; 
lean_dec(v_snd_1381_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_fst_1380_);
v___x_1390_ = v___x_1378_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_fst_1380_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1375_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1375_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1362_ = stack[0].m_obj;
lean_object* v___y_1363_ = stack[1].m_obj;
lean_object* v___y_1364_ = stack[2].m_obj;
lean_object* v___y_1365_ = stack[3].m_obj;
lean_object* v___y_1366_ = stack[4].m_obj;
lean_object* v___y_1367_ = stack[5].m_obj;
lean_object* v___y_1368_ = stack[6].m_obj;
lean_object* v_res_1401_;
v_res_1401_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_c_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
stack->m_obj
 = v_res_1401_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___boxed(lean_object* v_c_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_c_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v_c_1402_);
return v_res_1410_;
}
}
lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(lean_object* v_stx_1411_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
lean_inc(v_stx_1411_);
v___x_1413_ = l_Lean_Syntax_getKind(v_stx_1411_);
v___x_1414_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1415_ = lean_name_eq(v___x_1413_, v___x_1414_);
lean_dec(v___x_1413_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_dec(v_stx_1411_);
v___x_1416_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v_sz_1420_; size_t v___x_1421_; lean_object* v_attrs_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_startTag_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1417_ = lean_unsigned_to_nat(2u);
v___x_1418_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1417_);
v___x_1419_ = l_Lean_Syntax_getArgs(v___x_1418_);
lean_dec(v___x_1418_);
v_sz_1420_ = lean_array_size(v___x_1419_);
v___x_1421_ = ((size_t)0ULL);
v_attrs_1422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_1420_, v___x_1421_, v___x_1419_);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1423_);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1425_);
v___x_1427_ = lean_unsigned_to_nat(3u);
v___x_1428_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1427_);
v_startTag_1429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_1429_, 0, v___x_1424_);
lean_ctor_set(v_startTag_1429_, 1, v___x_1426_);
lean_ctor_set(v_startTag_1429_, 2, v_attrs_1422_);
lean_ctor_set(v_startTag_1429_, 3, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_getNumArgs(v_stx_1411_);
v___x_1431_ = lean_unsigned_to_nat(4u);
v___x_1432_ = lean_nat_dec_eq(v___x_1430_, v___x_1431_);
lean_dec(v___x_1430_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_endTag_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1433_ = lean_unsigned_to_nat(5u);
v___x_1434_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1433_);
v___x_1435_ = lean_unsigned_to_nat(6u);
v___x_1436_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5));
v___x_1438_ = lean_unsigned_to_nat(7u);
v___x_1439_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1438_);
v_endTag_1440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_1440_, 0, v___x_1434_);
lean_ctor_set(v_endTag_1440_, 1, v___x_1436_);
lean_ctor_set(v_endTag_1440_, 2, v___x_1437_);
lean_ctor_set(v_endTag_1440_, 3, v___x_1439_);
v___x_1441_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1431_);
lean_dec(v_stx_1411_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_endTag_1440_);
v___x_1444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1444_, 0, v_startTag_1429_);
lean_ctor_set(v___x_1444_, 1, v___x_1442_);
lean_ctor_set(v___x_1444_, 2, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_stx_1411_);
v___x_1446_ = lean_box(0);
v___x_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1447_, 0, v_startTag_1429_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1411_ = stack[0].m_obj;
lean_object* v_res_1449_;
v_res_1449_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1411_);
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg___boxed(lean_object* v_stx_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1450_);
return v_res_1452_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0));
v___x_1458_ = l_Lean_Expr_const___override(v___x_1457_, v___x_1456_);
return v___x_1458_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(uint8_t v___x_1461_, lean_object* v_b_1462_, lean_object* v_tm_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2);
v___x_1472_ = lean_box(0);
v___x_1473_ = l_Lean_Elab_Term_elabTermEnsuringType(v_tm_1463_, v___x_1471_, v___x_1461_, v___x_1461_, v___x_1472_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1484_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1478_ = lean_array_push(v_b_1462_, v_a_1474_);
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___x_1478_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1480_);
v___x_1482_ = v___x_1476_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_b_1462_);
v_a_1485_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1473_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1473_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1461_ = stack[0].m_num;
lean_object* v_b_1462_ = stack[1].m_obj;
lean_object* v_tm_1463_ = stack[2].m_obj;
lean_object* v___y_1464_ = stack[3].m_obj;
lean_object* v___y_1465_ = stack[4].m_obj;
lean_object* v___y_1466_ = stack[5].m_obj;
lean_object* v___y_1467_ = stack[6].m_obj;
lean_object* v___y_1468_ = stack[7].m_obj;
lean_object* v___y_1469_ = stack[8].m_obj;
lean_object* v_res_1493_;
v_res_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1461_, v_b_1462_, v_tm_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
stack->m_obj
 = v_res_1493_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___boxed(lean_object* v___x_1494_, lean_object* v_b_1495_, lean_object* v_tm_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v___x_18295__boxed_1504_; lean_object* v_res_1505_; 
v___x_18295__boxed_1504_ = lean_unbox(v___x_1494_);
v_res_1505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_18295__boxed_1504_, v_b_1495_, v_tm_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1505_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2));
v___x_1515_ = l_Lean_Expr_const___override(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5));
v___x_1523_ = l_Lean_Expr_const___override(v___x_1522_, v___x_1521_);
return v___x_1523_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_box(0);
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0));
v___x_1530_ = l_Lean_Expr_const___override(v___x_1529_, v___x_1528_);
return v___x_1530_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_box(0);
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2));
v___x_1537_ = l_Lean_Expr_const___override(v___x_1536_, v___x_1535_);
return v___x_1537_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6));
v___x_1544_ = l_String_toRawSubstring_x27(v___x_1543_);
return v___x_1544_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(lean_object* v_as_1555_, size_t v_sz_1556_, size_t v_i_1557_, lean_object* v_b_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_a_1567_; lean_object* v___y_1572_; uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_lt(v_i_1557_, v_sz_1556_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_b_1558_);
return v___x_1584_;
}
else
{
lean_object* v_a_1585_; 
v_a_1585_ = lean_array_uget_borrowed(v_as_1555_, v_i_1557_);
switch(lean_obj_tag(v_a_1585_))
{
case 0:
{
lean_object* v_stx_1586_; lean_object* v_toCold_1587_; lean_object* v_currRecDepth_1588_; lean_object* v_ref_1589_; uint16_t v_optionFlags_1590_; uint8_t v_suppressElabErrors_1591_; uint8_t v_isRecordingDeps_1592_; lean_object* v_ref_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_stx_1586_ = lean_ctor_get(v_a_1585_, 0);
v_toCold_1587_ = lean_ctor_get(v___y_1563_, 0);
v_currRecDepth_1588_ = lean_ctor_get(v___y_1563_, 1);
v_ref_1589_ = lean_ctor_get(v___y_1563_, 2);
v_optionFlags_1590_ = lean_ctor_get_uint16(v___y_1563_, sizeof(void*)*3);
v_suppressElabErrors_1591_ = lean_ctor_get_uint8(v___y_1563_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1592_ = lean_ctor_get_uint8(v___y_1563_, sizeof(void*)*3 + 3);
v_ref_1593_ = l_Lean_replaceRef(v_stx_1586_, v_ref_1589_);
lean_inc(v_currRecDepth_1588_);
lean_inc_ref(v_toCold_1587_);
v___x_1594_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1594_, 0, v_toCold_1587_);
lean_ctor_set(v___x_1594_, 1, v_currRecDepth_1588_);
lean_ctor_set(v___x_1594_, 2, v_ref_1593_);
lean_ctor_set_uint16(v___x_1594_, sizeof(void*)*3, v_optionFlags_1590_);
lean_ctor_set_uint8(v___x_1594_, sizeof(void*)*3 + 2, v_suppressElabErrors_1591_);
lean_ctor_set_uint8(v___x_1594_, sizeof(void*)*3 + 3, v_isRecordingDeps_1592_);
lean_inc(v_stx_1586_);
v___x_1595_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_1586_, v___x_1594_, v___y_1564_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref_known(v___x_1595_, 1);
lean_inc(v_stx_1586_);
v___x_1596_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_1586_, v___x_1594_, v___y_1564_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref_known(v___x_1596_, 1);
lean_inc(v_stx_1586_);
v___x_1597_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1586_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v_startTag_1599_; lean_object* v_children_x3f_1600_; lean_object* v_name_1601_; lean_object* v_attrs_1602_; lean_object* v___x_1603_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v_startTag_1599_ = lean_ctor_get(v_a_1598_, 0);
lean_inc_ref(v_startTag_1599_);
v_children_x3f_1600_ = lean_ctor_get(v_a_1598_, 1);
lean_inc(v_children_x3f_1600_);
lean_dec(v_a_1598_);
v_name_1601_ = lean_ctor_get(v_startTag_1599_, 1);
lean_inc(v_name_1601_);
v_attrs_1602_ = lean_ctor_get(v_startTag_1599_, 2);
lean_inc_ref(v_attrs_1602_);
lean_dec_ref(v_startTag_1599_);
v___x_1603_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_1601_);
lean_dec(v_name_1601_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1605_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_attrs_1602_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___x_1594_, v___y_1564_);
lean_dec_ref(v_attrs_1602_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v_a_1614_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
if (lean_obj_tag(v_children_x3f_1600_) == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref_known(v___x_1594_, 3);
v___x_1619_ = lean_box(0);
v_a_1614_ = v___x_1619_;
goto v___jp_1613_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1637_; 
v_val_1620_ = lean_ctor_get(v_children_x3f_1600_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_children_x3f_1600_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1622_ = v_children_x3f_1600_;
v_isShared_1623_ = v_isSharedCheck_1637_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_val_1620_);
lean_dec(v_children_x3f_1600_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1637_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_val_1620_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___x_1594_, v___y_1564_);
lean_dec_ref_known(v___x_1594_, 3);
lean_dec(v_val_1620_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v_a_1625_);
v___x_1627_ = v___x_1622_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
v_a_1614_ = v___x_1627_;
goto v___jp_1613_;
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_del_object(v___x_1622_);
lean_dec(v_a_1606_);
lean_dec(v_a_1604_);
lean_dec_ref(v_b_1558_);
v_a_1629_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1624_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1624_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
v___jp_1607_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_inc_ref(v___y_1609_);
v___x_1611_ = l_Lean_mkApp3(v___y_1609_, v___y_1608_, v_a_1606_, v___y_1610_);
v___x_1612_ = lean_array_push(v_b_1558_, v___x_1611_);
v_a_1567_ = v___x_1612_;
goto v___jp_1566_;
}
v___jp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1);
v___x_1616_ = l_Lean_mkStrLit(v_a_1604_);
if (lean_obj_tag(v_a_1614_) == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
v___y_1608_ = v___x_1616_;
v___y_1609_ = v___x_1615_;
v___y_1610_ = v___x_1617_;
goto v___jp_1607_;
}
else
{
lean_object* v_val_1618_; 
v_val_1618_ = lean_ctor_get(v_a_1614_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v_a_1614_, 1);
v___y_1608_ = v___x_1616_;
v___y_1609_ = v___x_1615_;
v___y_1610_ = v_val_1618_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_a_1604_);
lean_dec(v_children_x3f_1600_);
lean_dec_ref_known(v___x_1594_, 3);
lean_dec_ref(v_b_1558_);
v_a_1638_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1605_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1605_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_attrs_1602_);
lean_dec(v_children_x3f_1600_);
lean_dec_ref_known(v___x_1594_, 3);
lean_dec_ref(v_b_1558_);
v_a_1646_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1603_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1603_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref_known(v___x_1594_, 3);
lean_dec_ref(v_b_1558_);
v_a_1654_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1597_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1597_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref_known(v___x_1594_, 3);
lean_dec_ref(v_b_1558_);
v_a_1662_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1596_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1596_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref_known(v___x_1594_, 3);
lean_dec_ref(v_b_1558_);
v_a_1670_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1595_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1595_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
case 1:
{
lean_object* v_stx_1678_; lean_object* v_toCold_1679_; lean_object* v_currRecDepth_1680_; lean_object* v_ref_1681_; uint16_t v_optionFlags_1682_; uint8_t v_suppressElabErrors_1683_; uint8_t v_isRecordingDeps_1684_; lean_object* v___x_1685_; lean_object* v_ref_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_stx_1678_ = lean_ctor_get(v_a_1585_, 0);
v_toCold_1679_ = lean_ctor_get(v___y_1563_, 0);
v_currRecDepth_1680_ = lean_ctor_get(v___y_1563_, 1);
v_ref_1681_ = lean_ctor_get(v___y_1563_, 2);
v_optionFlags_1682_ = lean_ctor_get_uint16(v___y_1563_, sizeof(void*)*3);
v_suppressElabErrors_1683_ = lean_ctor_get_uint8(v___y_1563_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1684_ = lean_ctor_get_uint8(v___y_1563_, sizeof(void*)*3 + 3);
lean_inc_ref(v_stx_1678_);
v___x_1685_ = l_Lean_Html_Syntax_TextCommentsView_getSyntax(v_stx_1678_);
v_ref_1686_ = l_Lean_replaceRef(v___x_1685_, v_ref_1681_);
lean_dec(v___x_1685_);
lean_inc(v_currRecDepth_1680_);
lean_inc_ref(v_toCold_1679_);
v___x_1687_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1687_, 0, v_toCold_1679_);
lean_ctor_set(v___x_1687_, 1, v_currRecDepth_1680_);
lean_ctor_set(v___x_1687_, 2, v_ref_1686_);
lean_ctor_set_uint16(v___x_1687_, sizeof(void*)*3, v_optionFlags_1682_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*3 + 2, v_suppressElabErrors_1683_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*3 + 3, v_isRecordingDeps_1684_);
v___x_1688_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_stx_1678_, v___x_1687_, v___y_1564_);
lean_dec_ref_known(v___x_1687_, 3);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_string_utf8_byte_size(v_a_1689_);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_nat_dec_eq(v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3);
v___x_1694_ = l_Lean_mkStrLit(v_a_1689_);
v___x_1695_ = l_Lean_Expr_app___override(v___x_1693_, v___x_1694_);
v___x_1696_ = lean_array_push(v_b_1558_, v___x_1695_);
v_a_1567_ = v___x_1696_;
goto v___jp_1566_;
}
else
{
lean_dec(v_a_1689_);
v_a_1567_ = v_b_1558_;
goto v___jp_1566_;
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_b_1558_);
v_a_1697_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1688_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1688_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
default: 
{
uint8_t v_isMany_1705_; lean_object* v_stx_1706_; lean_object* v_toCold_1707_; lean_object* v_currRecDepth_1708_; lean_object* v_ref_1709_; uint16_t v_optionFlags_1710_; uint8_t v_suppressElabErrors_1711_; uint8_t v_isRecordingDeps_1712_; lean_object* v_ref_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_isMany_1705_ = lean_ctor_get_uint8(v_a_1585_, sizeof(void*)*1);
v_stx_1706_ = lean_ctor_get(v_a_1585_, 0);
v_toCold_1707_ = lean_ctor_get(v___y_1563_, 0);
v_currRecDepth_1708_ = lean_ctor_get(v___y_1563_, 1);
v_ref_1709_ = lean_ctor_get(v___y_1563_, 2);
v_optionFlags_1710_ = lean_ctor_get_uint16(v___y_1563_, sizeof(void*)*3);
v_suppressElabErrors_1711_ = lean_ctor_get_uint8(v___y_1563_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1712_ = lean_ctor_get_uint8(v___y_1563_, sizeof(void*)*3 + 3);
v_ref_1713_ = l_Lean_replaceRef(v_stx_1706_, v_ref_1709_);
lean_inc(v_ref_1713_);
lean_inc(v_currRecDepth_1708_);
lean_inc_ref(v_toCold_1707_);
v___x_1714_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1714_, 0, v_toCold_1707_);
lean_ctor_set(v___x_1714_, 1, v_currRecDepth_1708_);
lean_ctor_set(v___x_1714_, 2, v_ref_1713_);
lean_ctor_set_uint16(v___x_1714_, sizeof(void*)*3, v_optionFlags_1710_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*3 + 2, v_suppressElabErrors_1711_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*3 + 3, v_isRecordingDeps_1712_);
lean_inc(v_stx_1706_);
v___x_1715_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_1705_, v_stx_1706_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___x_1714_, v___y_1564_);
if (lean_obj_tag(v___x_1715_) == 0)
{
if (v_isMany_1705_ == 0)
{
lean_object* v_a_1716_; lean_object* v_term_1717_; lean_object* v___x_1718_; 
lean_dec(v_ref_1713_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v_term_1717_ = lean_ctor_get(v_a_1716_, 1);
lean_inc(v_term_1717_);
lean_dec(v_a_1716_);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1583_, v_b_1558_, v_term_1717_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___x_1714_, v___y_1564_);
lean_dec_ref_known(v___x_1714_, 3);
v___y_1572_ = v___x_1718_;
goto v___jp_1571_;
}
else
{
lean_object* v_a_1719_; lean_object* v_quotContext_1720_; lean_object* v_currMacroScope_1721_; lean_object* v_term_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_a_1719_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1715_, 1);
v_quotContext_1720_ = lean_ctor_get(v_toCold_1707_, 8);
v_currMacroScope_1721_ = lean_ctor_get(v_toCold_1707_, 9);
v_term_1722_ = lean_ctor_get(v_a_1719_, 1);
lean_inc(v_term_1722_);
lean_dec(v_a_1719_);
v___x_1723_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_1724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5));
v___x_1725_ = 0;
v___x_1726_ = l_Lean_SourceInfo_fromRef(v_ref_1713_, v___x_1725_);
lean_dec(v_ref_1713_);
v___x_1727_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7);
lean_inc(v_currMacroScope_1721_);
lean_inc(v_quotContext_1720_);
v___x_1728_ = l_Lean_addMacroScope(v_quotContext_1720_, v___x_1724_, v_currMacroScope_1721_);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10));
lean_inc_n(v___x_1726_, 2);
v___x_1730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1726_);
lean_ctor_set(v___x_1730_, 1, v___x_1727_);
lean_ctor_set(v___x_1730_, 2, v___x_1728_);
lean_ctor_set(v___x_1730_, 3, v___x_1729_);
v___x_1731_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1732_ = l_Lean_Syntax_node1(v___x_1726_, v___x_1731_, v_term_1722_);
v___x_1733_ = l_Lean_Syntax_node2(v___x_1726_, v___x_1723_, v___x_1730_, v___x_1732_);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1583_, v_b_1558_, v___x_1733_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___x_1714_, v___y_1564_);
lean_dec_ref_known(v___x_1714_, 3);
v___y_1572_ = v___x_1734_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref_known(v___x_1714_, 3);
lean_dec(v_ref_1713_);
lean_dec_ref(v_b_1558_);
v_a_1735_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1715_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1715_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
v___jp_1566_:
{
size_t v___x_1568_; size_t v___x_1569_; 
v___x_1568_ = ((size_t)1ULL);
v___x_1569_ = lean_usize_add(v_i_1557_, v___x_1568_);
v_i_1557_ = v___x_1569_;
v_b_1558_ = v_a_1567_;
goto _start;
}
v___jp_1571_:
{
if (lean_obj_tag(v___y_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v_snd_1574_; 
v_a_1573_ = lean_ctor_get(v___y_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___y_1572_, 1);
v_snd_1574_ = lean_ctor_get(v_a_1573_, 1);
lean_inc(v_snd_1574_);
lean_dec(v_a_1573_);
v_a_1567_ = v_snd_1574_;
goto v___jp_1566_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_a_1575_ = lean_ctor_get(v___y_1572_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___y_1572_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___y_1572_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___y_1572_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1555_ = stack[0].m_obj;
size_t v_sz_1556_ = stack[1].m_num;
size_t v_i_1557_ = stack[2].m_num;
lean_object* v_b_1558_ = stack[3].m_obj;
lean_object* v___y_1559_ = stack[4].m_obj;
lean_object* v___y_1560_ = stack[5].m_obj;
lean_object* v___y_1561_ = stack[6].m_obj;
lean_object* v___y_1562_ = stack[7].m_obj;
lean_object* v___y_1563_ = stack[8].m_obj;
lean_object* v___y_1564_ = stack[9].m_obj;
lean_object* v_res_1743_;
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_as_1555_, v_sz_1556_, v_i_1557_, v_b_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
stack->m_obj
 = v_res_1743_;
}
lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(lean_object* v_stx_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_toCold_1752_; lean_object* v_currRecDepth_1753_; lean_object* v_ref_1754_; uint16_t v_optionFlags_1755_; uint8_t v_suppressElabErrors_1756_; uint8_t v_isRecordingDeps_1757_; lean_object* v___x_1758_; lean_object* v_es_1759_; lean_object* v_ref_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_toCold_1752_ = lean_ctor_get(v_a_1749_, 0);
v_currRecDepth_1753_ = lean_ctor_get(v_a_1749_, 1);
v_ref_1754_ = lean_ctor_get(v_a_1749_, 2);
v_optionFlags_1755_ = lean_ctor_get_uint16(v_a_1749_, sizeof(void*)*3);
v_suppressElabErrors_1756_ = lean_ctor_get_uint8(v_a_1749_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1757_ = lean_ctor_get_uint8(v_a_1749_, sizeof(void*)*3 + 3);
v___x_1758_ = lean_unsigned_to_nat(0u);
v_es_1759_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0));
v_ref_1760_ = l_Lean_replaceRef(v_stx_1744_, v_ref_1754_);
lean_inc(v_currRecDepth_1753_);
lean_inc_ref(v_toCold_1752_);
v___x_1761_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1761_, 0, v_toCold_1752_);
lean_ctor_set(v___x_1761_, 1, v_currRecDepth_1753_);
lean_ctor_set(v___x_1761_, 2, v_ref_1760_);
lean_ctor_set_uint16(v___x_1761_, sizeof(void*)*3, v_optionFlags_1755_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*3 + 2, v_suppressElabErrors_1756_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*3 + 3, v_isRecordingDeps_1757_);
v___x_1762_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_stx_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v___x_1761_, v_a_1750_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; size_t v_sz_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v_sz_1764_ = lean_array_size(v_a_1763_);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_a_1763_, v_sz_1764_, v___x_1765_, v_es_1759_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v___x_1761_, v_a_1750_);
lean_dec(v_a_1763_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1790_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1790_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1790_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_get_size(v_a_1767_);
v___x_1772_ = lean_nat_dec_eq(v___x_1771_, v___x_1758_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_del_object(v___x_1769_);
v___x_1773_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1774_ = lean_array_to_list(v_a_1767_);
v___x_1775_ = l_Lean_Meta_mkArrayLit(v___x_1773_, v___x_1774_, v_a_1747_, v_a_1748_, v___x_1761_, v_a_1750_);
lean_dec_ref_known(v___x_1761_, 3);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1785_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1780_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3);
v___x_1781_ = l_Lean_Expr_app___override(v___x_1780_, v_a_1776_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1781_);
v___x_1783_ = v___x_1778_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
return v___x_1775_;
}
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_dec(v_a_1767_);
lean_dec_ref_known(v___x_1761_, 3);
v___x_1786_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1786_);
v___x_1788_ = v___x_1769_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref_known(v___x_1761_, 3);
v_a_1791_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1766_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1766_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref_known(v___x_1761_, 3);
v_a_1799_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1762_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1762_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1744_ = stack[0].m_obj;
lean_object* v_a_1745_ = stack[1].m_obj;
lean_object* v_a_1746_ = stack[2].m_obj;
lean_object* v_a_1747_ = stack[3].m_obj;
lean_object* v_a_1748_ = stack[4].m_obj;
lean_object* v_a_1749_ = stack[5].m_obj;
lean_object* v_a_1750_ = stack[6].m_obj;
lean_object* v_res_1807_;
v_res_1807_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_stx_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
stack->m_obj
 = v_res_1807_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___boxed(lean_object* v_stx_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_stx_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_stx_1808_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___boxed(lean_object* v_as_1817_, lean_object* v_sz_1818_, lean_object* v_i_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
size_t v_sz_boxed_1828_; size_t v_i_boxed_1829_; lean_object* v_res_1830_; 
v_sz_boxed_1828_ = lean_unbox_usize(v_sz_1818_);
lean_dec(v_sz_1818_);
v_i_boxed_1829_ = lean_unbox_usize(v_i_1819_);
lean_dec(v_i_1819_);
v_res_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_as_1817_, v_sz_boxed_1828_, v_i_boxed_1829_, v_b_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_as_1817_);
return v_res_1830_;
}
}
lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(lean_object* v_stx_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1831_);
return v___x_1839_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1831_ = stack[0].m_obj;
lean_object* v___y_1832_ = stack[1].m_obj;
lean_object* v___y_1833_ = stack[2].m_obj;
lean_object* v___y_1834_ = stack[3].m_obj;
lean_object* v___y_1835_ = stack[4].m_obj;
lean_object* v___y_1836_ = stack[5].m_obj;
lean_object* v___y_1837_ = stack[6].m_obj;
lean_object* v_res_1840_;
v_res_1840_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(v_stx_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
stack->m_obj
 = v_res_1840_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___boxed(lean_object* v_stx_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(v_stx_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v_res_1849_;
}
}
lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1850_ = stack[0].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(v_a_1850_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg___boxed(lean_object* v_a_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(v_a_1854_);
lean_dec(v_a_1854_);
return v_res_1856_;
}
}
lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(lean_object* v_a_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1857_);
return v___x_1865_;
}
}
LEAN_EXPORT void l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1857_ = stack[0].m_obj;
lean_object* v___y_1858_ = stack[1].m_obj;
lean_object* v___y_1859_ = stack[2].m_obj;
lean_object* v___y_1860_ = stack[3].m_obj;
lean_object* v___y_1861_ = stack[4].m_obj;
lean_object* v___y_1862_ = stack[5].m_obj;
lean_object* v___y_1863_ = stack[6].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(v_a_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___boxed(lean_object* v_a_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(v_a_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v_a_1867_);
return v_res_1875_;
}
}
lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(lean_object* v_stx_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1));
lean_inc(v_stx_1888_);
v___x_1897_ = l_Lean_Syntax_isOfKind(v_stx_1888_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec(v_stx_1888_);
v___x_1898_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; lean_object* v_h_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1899_ = lean_unsigned_to_nat(2u);
v_h_1900_ = l_Lean_Syntax_getArg(v_stx_1888_, v___x_1899_);
lean_dec(v_stx_1888_);
v___x_1901_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3));
lean_inc(v_h_1900_);
v___x_1902_ = l_Lean_Syntax_isOfKind(v_h_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec(v_h_1900_);
v___x_1903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; 
v___x_1904_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_h_1900_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_h_1900_);
return v___x_1904_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1888_ = stack[0].m_obj;
lean_object* v_a_1889_ = stack[1].m_obj;
lean_object* v_a_1890_ = stack[2].m_obj;
lean_object* v_a_1891_ = stack[3].m_obj;
lean_object* v_a_1892_ = stack[4].m_obj;
lean_object* v_a_1893_ = stack[5].m_obj;
lean_object* v_a_1894_ = stack[6].m_obj;
lean_object* v_res_1905_;
v_res_1905_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
stack->m_obj
 = v_res_1905_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___boxed(lean_object* v_stx_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
return v_res_1914_;
}
}
lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(lean_object* v_stx_1915_, lean_object* v_x_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1915_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT void l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1915_ = stack[0].m_obj;
lean_object* v_x_1916_ = stack[1].m_obj;
lean_object* v_a_1917_ = stack[2].m_obj;
lean_object* v_a_1918_ = stack[3].m_obj;
lean_object* v_a_1919_ = stack[4].m_obj;
lean_object* v_a_1920_ = stack[5].m_obj;
lean_object* v_a_1921_ = stack[6].m_obj;
lean_object* v_a_1922_ = stack[7].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(v_stx_1915_, v_x_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___boxed(lean_object* v_stx_1926_, lean_object* v_x_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(v_stx_1926_, v_x_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_x_1927_);
return v_res_1935_;
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
