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
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_115_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
lean_ctor_set(v___x_117_, 3, v___x_116_);
lean_ctor_set(v___x_117_, 4, v___x_115_);
lean_ctor_set(v___x_117_, 5, v___x_115_);
lean_ctor_set(v___x_117_, 6, v___x_115_);
lean_ctor_set(v___x_117_, 7, v___x_115_);
lean_ctor_set(v___x_117_, 8, v___x_115_);
lean_ctor_set(v___x_117_, 9, v___x_115_);
lean_ctor_set(v___x_117_, 10, v___x_115_);
lean_ctor_set(v___x_117_, 11, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_unsigned_to_nat(32u);
v___x_119_ = lean_mk_empty_array_with_capacity(v___x_118_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4(void){
_start:
{
size_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_121_ = ((size_t)5ULL);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_unsigned_to_nat(32u);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_123_);
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__3);
v___x_126_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
lean_ctor_set(v___x_126_, 2, v___x_122_);
lean_ctor_set(v___x_126_, 3, v___x_122_);
lean_ctor_set_usize(v___x_126_, 4, v___x_121_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = lean_box(1);
v___x_128_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__4);
v___x_129_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__1);
v___x_130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(lean_object* v_msgData_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; lean_object* v_toCold_136_; lean_object* v_env_137_; lean_object* v_options_138_; uint8_t v___x_139_; lean_object* v_env_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_135_ = lean_st_ref_get(v___y_133_);
v_toCold_136_ = lean_ctor_get(v___y_132_, 0);
v_env_137_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_env_137_);
lean_dec(v___x_135_);
v_options_138_ = lean_ctor_get(v_toCold_136_, 2);
v___x_139_ = 0;
v_env_140_ = l_Lean_Environment_setRecordingDeps(v_env_137_, v___x_139_);
v___x_141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__2);
v___x_142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___closed__5);
lean_inc_ref(v_options_138_);
v___x_143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_143_, 0, v_env_140_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_142_);
lean_ctor_set(v___x_143_, 3, v_options_138_);
v___x_144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_msgData_131_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7___boxed(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(v_msgData_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_ref_155_; lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_165_; 
v_ref_155_ = lean_ctor_get(v___y_152_, 2);
v___x_156_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6_spec__7(v_msg_151_, v___y_152_, v___y_153_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_165_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
lean_inc(v_ref_155_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_ref_155_);
lean_ctor_set(v___x_161_, 1, v_a_157_);
if (v_isShared_160_ == 0)
{
lean_ctor_set_tag(v___x_159_, 1);
lean_ctor_set(v___x_159_, 0, v___x_161_);
v___x_163_ = v___x_159_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg___boxed(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(lean_object* v_ref_171_, lean_object* v_msg_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_toCold_176_; lean_object* v_currRecDepth_177_; lean_object* v_ref_178_; uint16_t v_optionFlags_179_; uint8_t v_suppressElabErrors_180_; uint8_t v_isRecordingDeps_181_; lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_toCold_176_ = lean_ctor_get(v___y_173_, 0);
v_currRecDepth_177_ = lean_ctor_get(v___y_173_, 1);
v_ref_178_ = lean_ctor_get(v___y_173_, 2);
v_optionFlags_179_ = lean_ctor_get_uint16(v___y_173_, sizeof(void*)*3);
v_suppressElabErrors_180_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*3 + 2);
v_isRecordingDeps_181_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*3 + 3);
v_ref_182_ = l_Lean_replaceRef(v_ref_171_, v_ref_178_);
lean_inc(v_currRecDepth_177_);
lean_inc_ref(v_toCold_176_);
v___x_183_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_183_, 0, v_toCold_176_);
lean_ctor_set(v___x_183_, 1, v_currRecDepth_177_);
lean_ctor_set(v___x_183_, 2, v_ref_182_);
lean_ctor_set_uint16(v___x_183_, sizeof(void*)*3, v_optionFlags_179_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3 + 2, v_suppressElabErrors_180_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3 + 3, v_isRecordingDeps_181_);
v___x_184_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_172_, v___x_183_, v___y_174_);
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
lean_object* v___x_567_; lean_object* v_c_568_; lean_object* v___x_569_; lean_object* v___y_571_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v_c_568_ = l_Lean_Syntax_getArg(v_stx_559_, v___x_567_);
lean_inc(v_c_568_);
v___x_569_ = l_Lean_Syntax_getKind(v_c_568_);
v___x_576_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__1));
v___x_577_ = lean_name_eq(v___x_569_, v___x_576_);
if (v___x_577_ == 0)
{
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___y_571_ = v___x_578_;
goto v___jp_570_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___y_571_ = v___x_579_;
goto v___jp_570_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___x_569_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v_c_568_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
v___jp_570_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_name_eq(v___x_569_, v___y_571_);
lean_dec(v___x_569_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v_c_568_);
v___x_573_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v_c_568_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___boxed(lean_object* v_stx_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v_stx_582_);
return v_res_590_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_box(0);
v___x_595_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_596_ = l_Lean_Expr_const___override(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(lean_object* v_stx_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_toCold_607_; lean_object* v_currRecDepth_608_; lean_object* v_ref_609_; uint16_t v_optionFlags_610_; uint8_t v_suppressElabErrors_611_; uint8_t v_isRecordingDeps_612_; lean_object* v_ref_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_toCold_607_ = lean_ctor_get(v_a_604_, 0);
v_currRecDepth_608_ = lean_ctor_get(v_a_604_, 1);
v_ref_609_ = lean_ctor_get(v_a_604_, 2);
v_optionFlags_610_ = lean_ctor_get_uint16(v_a_604_, sizeof(void*)*3);
v_suppressElabErrors_611_ = lean_ctor_get_uint8(v_a_604_, sizeof(void*)*3 + 2);
v_isRecordingDeps_612_ = lean_ctor_get_uint8(v_a_604_, sizeof(void*)*3 + 3);
v_ref_613_ = l_Lean_replaceRef(v_stx_599_, v_ref_609_);
lean_inc(v_currRecDepth_608_);
lean_inc_ref(v_toCold_607_);
v___x_614_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_614_, 0, v_toCold_607_);
lean_ctor_set(v___x_614_, 1, v_currRecDepth_608_);
lean_ctor_set(v___x_614_, 2, v_ref_613_);
lean_ctor_set_uint16(v___x_614_, sizeof(void*)*3, v_optionFlags_610_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*3 + 2, v_suppressElabErrors_611_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*3 + 3, v_isRecordingDeps_612_);
v___x_615_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v___x_614_, v_a_605_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
if (lean_obj_tag(v_a_616_) == 0)
{
lean_object* v_stx_617_; lean_object* v___x_618_; 
v_stx_617_ = lean_ctor_get(v_a_616_, 0);
lean_inc(v_stx_617_);
lean_dec_ref_known(v_a_616_, 1);
v___x_618_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_stx_617_, v___x_614_, v_a_605_);
lean_dec_ref_known(v___x_614_, 3);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_627_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_mkStrLit(v_a_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
v_a_628_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_618_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_618_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_stx_636_; uint8_t v___x_637_; lean_object* v___x_638_; 
v_stx_636_ = lean_ctor_get(v_a_616_, 0);
lean_inc(v_stx_636_);
lean_dec_ref_known(v_a_616_, 1);
v___x_637_ = 0;
v___x_638_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v___x_637_, v_stx_636_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v___x_614_, v_a_605_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_term_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v_term_640_ = lean_ctor_get(v_a_639_, 1);
lean_inc(v_term_640_);
lean_dec(v_a_639_);
v___x_641_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3);
v___x_642_ = 1;
v___x_643_ = lean_box(0);
v___x_644_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_640_, v___x_641_, v___x_642_, v___x_642_, v___x_643_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v___x_614_, v_a_605_);
lean_dec_ref_known(v___x_614_, 3);
return v___x_644_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref_known(v___x_614_, 3);
v_a_645_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_638_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_638_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref_known(v___x_614_, 3);
v_a_653_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_615_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_615_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___boxed(lean_object* v_stx_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_stx_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_stx_661_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(lean_object* v_00_u03b1_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___boxed(lean_object* v_00_u03b1_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(v_00_u03b1_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(lean_object* v_stx_694_){
_start:
{
lean_object* v___x_696_; lean_object* v_c_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v_c_697_ = l_Lean_Syntax_getArg(v_stx_694_, v___x_696_);
lean_inc(v_c_697_);
v___x_698_ = l_Lean_Syntax_getKind(v_c_697_);
v___x_699_ = ((lean_object*)(l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1));
v___x_700_ = lean_name_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; uint8_t v___x_702_; lean_object* v___y_704_; 
v___x_701_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_702_ = lean_name_eq(v___x_698_, v___x_701_);
if (v___x_702_ == 0)
{
if (v___x_702_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___y_704_ = v___x_709_;
goto v___jp_703_;
}
else
{
v___y_704_ = v___x_701_;
goto v___jp_703_;
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v___x_698_);
v___x_710_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_710_, 0, v_c_697_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*1, v___x_702_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
v___jp_703_:
{
uint8_t v___x_705_; 
v___x_705_ = lean_name_eq(v___x_698_, v___y_704_);
lean_dec(v___x_698_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_dec(v_c_697_);
v___x_706_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_707_, 0, v_c_697_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v___x_702_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
else
{
lean_object* v___x_712_; lean_object* v_val_x3f_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
lean_dec(v___x_698_);
v___x_712_ = lean_unsigned_to_nat(1u);
v_val_x3f_713_ = l_Lean_Syntax_getArg(v_stx_694_, v___x_712_);
v___x_714_ = l_Lean_Syntax_getNumArgs(v_val_x3f_713_);
v___x_715_ = lean_nat_dec_eq(v___x_714_, v___x_696_);
lean_dec(v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_716_ = l_Lean_Syntax_getArg(v_val_x3f_713_, v___x_696_);
v___x_717_ = l_Lean_Syntax_getArg(v_val_x3f_713_, v___x_712_);
lean_dec(v_val_x3f_713_);
v___x_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_718_, 0, v_c_697_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v_val_x3f_713_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v_c_697_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___boxed(lean_object* v_stx_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_723_);
lean_dec(v_stx_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 1)
{
lean_object* v_args_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_args_728_ = lean_ctor_get(v_x_726_, 2);
v___x_729_ = lean_array_get_size(v_args_728_);
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_dec_eq(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_732_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_array_fget_borrowed(v_args_728_, v___x_733_);
if (lean_obj_tag(v___x_734_) == 2)
{
lean_object* v_val_735_; lean_object* v___x_736_; 
v_val_735_ = lean_ctor_get(v___x_734_, 1);
lean_inc_ref(v_val_735_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_val_735_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_737_;
}
}
}
else
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg___boxed(lean_object* v_x_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_739_);
lean_dec(v_x_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(lean_object* v_a_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_742_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1___boxed(lean_object* v_a_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(v_a_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v_a_751_);
return v_res_759_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = l_Lean_Level_ofNat(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
v___x_766_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_769_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_772_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1));
v___x_773_ = l_Lean_Expr_const___override(v___x_772_, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6(void){
_start:
{
lean_object* v_strType_774_; lean_object* v___x_775_; lean_object* v_pairType_776_; 
v_strType_774_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_775_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5);
v_pairType_776_ = l_Lean_mkAppB(v___x_775_, v_strType_774_, v_strType_774_);
return v_pairType_776_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_781_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8));
v___x_782_ = l_Lean_Expr_const___override(v___x_781_, v___x_780_);
return v___x_782_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10(void){
_start:
{
lean_object* v_pairType_783_; lean_object* v___x_784_; lean_object* v_arrayType_785_; 
v_pairType_783_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_784_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9);
v_arrayType_785_ = l_Lean_Expr_app___override(v___x_784_, v_pairType_783_);
return v_arrayType_785_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_791_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12));
v___x_792_ = l_Lean_Expr_const___override(v___x_791_, v___x_790_);
return v___x_792_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8));
v___x_794_ = l_Lean_mkStrLit(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15(void){
_start:
{
lean_object* v_pairType_795_; lean_object* v___x_796_; 
v_pairType_795_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_pairType_795_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20));
v___x_807_ = l_String_toRawSubstring_x27(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30));
v___x_828_ = l_String_toRawSubstring_x27(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0));
v___x_836_ = l_String_toRawSubstring_x27(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47(void){
_start:
{
lean_object* v_arrayType_859_; lean_object* v___x_860_; 
v_arrayType_859_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_arrayType_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(lean_object* v_stx_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_strType_871_; lean_object* v_toCold_872_; lean_object* v_currRecDepth_873_; lean_object* v_ref_874_; uint16_t v_optionFlags_875_; uint8_t v_suppressElabErrors_876_; uint8_t v_isRecordingDeps_877_; lean_object* v_ref_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_870_ = lean_box(0);
v_strType_871_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v_toCold_872_ = lean_ctor_get(v_a_866_, 0);
v_currRecDepth_873_ = lean_ctor_get(v_a_866_, 1);
v_ref_874_ = lean_ctor_get(v_a_866_, 2);
v_optionFlags_875_ = lean_ctor_get_uint16(v_a_866_, sizeof(void*)*3);
v_suppressElabErrors_876_ = lean_ctor_get_uint8(v_a_866_, sizeof(void*)*3 + 2);
v_isRecordingDeps_877_ = lean_ctor_get_uint8(v_a_866_, sizeof(void*)*3 + 3);
v_ref_878_ = l_Lean_replaceRef(v_stx_861_, v_ref_874_);
lean_inc(v_ref_878_);
lean_inc(v_currRecDepth_873_);
lean_inc_ref(v_toCold_872_);
v___x_879_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_879_, 0, v_toCold_872_);
lean_ctor_set(v___x_879_, 1, v_currRecDepth_873_);
lean_ctor_set(v___x_879_, 2, v_ref_878_);
lean_ctor_set_uint16(v___x_879_, sizeof(void*)*3, v_optionFlags_875_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*3 + 2, v_suppressElabErrors_876_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*3 + 3, v_isRecordingDeps_877_);
v___x_880_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_861_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
switch(lean_obj_tag(v_a_881_))
{
case 0:
{
lean_object* v_stx_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_ref_878_);
v_stx_882_ = lean_ctor_get(v_a_881_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_921_ == 0)
{
v___x_884_ = v_a_881_;
v_isShared_885_ = v_isSharedCheck_921_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_stx_882_);
lean_dec(v_a_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_921_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_name_886_; lean_object* v_val_887_; lean_object* v___x_888_; 
v_name_886_ = lean_ctor_get(v_stx_882_, 0);
lean_inc(v_name_886_);
v_val_887_ = lean_ctor_get(v_stx_882_, 2);
lean_inc(v_val_887_);
lean_dec_ref(v_stx_882_);
v___x_888_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_886_);
lean_dec(v_name_886_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_val_887_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v___x_879_, v_a_867_);
lean_dec_ref_known(v___x_879_, 3);
lean_dec(v_val_887_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_904_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_904_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_904_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_904_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_895_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_896_ = l_Lean_mkStrLit(v_a_889_);
v___x_897_ = l_Lean_mkApp4(v___x_895_, v_strType_871_, v_strType_871_, v___x_896_, v_a_891_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_897_);
v___x_899_ = v___x_884_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_899_);
v___x_901_ = v___x_893_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_a_889_);
lean_del_object(v___x_884_);
v_a_905_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_890_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_890_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_val_887_);
lean_del_object(v___x_884_);
lean_dec_ref_known(v___x_879_, 3);
v_a_913_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_888_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_888_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
case 1:
{
lean_object* v_stx_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref_known(v___x_879_, 3);
lean_dec(v_ref_878_);
v_stx_922_ = lean_ctor_get(v_a_881_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_950_ == 0)
{
v___x_924_ = v_a_881_;
v_isShared_925_ = v_isSharedCheck_950_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_stx_922_);
lean_dec(v_a_881_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_950_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; 
v___x_926_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_stx_922_);
lean_dec(v_stx_922_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_941_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_941_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_931_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_932_ = l_Lean_mkStrLit(v_a_927_);
v___x_933_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14);
v___x_934_ = l_Lean_mkApp4(v___x_931_, v_strType_871_, v_strType_871_, v___x_932_, v___x_933_);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 0);
lean_ctor_set(v___x_924_, 0, v___x_934_);
v___x_936_ = v___x_924_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_940_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_938_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_936_);
v___x_938_ = v___x_929_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_del_object(v___x_924_);
v_a_942_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_926_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_926_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
default: 
{
uint8_t v_isMany_951_; 
v_isMany_951_ = lean_ctor_get_uint8(v_a_881_, sizeof(void*)*1);
if (v_isMany_951_ == 0)
{
lean_object* v_stx_952_; lean_object* v___x_953_; 
lean_dec(v_ref_878_);
v_stx_952_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_stx_952_);
lean_dec_ref_known(v_a_881_, 1);
v___x_953_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_951_, v_stx_952_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v___x_879_, v_a_867_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_term_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v_term_955_ = lean_ctor_get(v_a_954_, 1);
lean_inc(v_term_955_);
lean_dec(v_a_954_);
v___x_956_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15);
v___x_957_ = 1;
v___x_958_ = lean_box(0);
v___x_959_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_955_, v___x_956_, v___x_957_, v___x_957_, v___x_958_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v___x_879_, v_a_867_);
lean_dec_ref_known(v___x_879_, 3);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
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
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_a_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
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
v_a_969_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_959_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_959_);
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
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref_known(v___x_879_, 3);
v_a_977_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_953_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_953_);
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
else
{
lean_object* v_stx_985_; lean_object* v___x_986_; 
v_stx_985_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_stx_985_);
lean_dec_ref_known(v_a_881_, 1);
v___x_986_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_951_, v_stx_985_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v___x_879_, v_a_867_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v_quotContext_988_; lean_object* v_currMacroScope_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_term_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v_quotContext_988_ = lean_ctor_get(v_toCold_872_, 8);
v_currMacroScope_989_ = lean_ctor_get(v_toCold_872_, 9);
v___x_990_ = 0;
v___x_991_ = l_Lean_SourceInfo_fromRef(v_ref_878_, v___x_990_);
lean_dec(v_ref_878_);
v___x_992_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_993_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21);
v___x_994_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24));
lean_inc_n(v_currMacroScope_989_, 3);
lean_inc_n(v_quotContext_988_, 3);
v___x_995_ = l_Lean_addMacroScope(v_quotContext_988_, v___x_994_, v_currMacroScope_989_);
v___x_996_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26));
lean_inc_n(v___x_991_, 10);
v___x_997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_997_, 0, v___x_991_);
lean_ctor_set(v___x_997_, 1, v___x_993_);
lean_ctor_set(v___x_997_, 2, v___x_995_);
lean_ctor_set(v___x_997_, 3, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28));
v___x_999_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29));
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_991_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31);
v___x_1002_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32));
v___x_1003_ = l_Lean_addMacroScope(v_quotContext_988_, v___x_1002_, v_currMacroScope_989_);
v___x_1004_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1004_, 0, v___x_991_);
lean_ctor_set(v___x_1004_, 1, v___x_1001_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
lean_ctor_set(v___x_1004_, 3, v___x_870_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_991_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35));
v___x_1008_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36);
v___x_1009_ = l_Lean_addMacroScope(v_quotContext_988_, v___x_869_, v_currMacroScope_989_);
v___x_1010_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42));
v___x_1011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1011_, 0, v___x_991_);
lean_ctor_set(v___x_1011_, 1, v___x_1008_);
lean_ctor_set(v___x_1011_, 2, v___x_1009_);
lean_ctor_set(v___x_1011_, 3, v___x_1010_);
v___x_1012_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43));
v___x_1013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_991_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_inc_ref(v___x_1011_);
v___x_1014_ = l_Lean_Syntax_node3(v___x_991_, v___x_1007_, v___x_1011_, v___x_1013_, v___x_1011_);
v_term_1015_ = lean_ctor_get(v_a_987_, 1);
lean_inc(v_term_1015_);
lean_dec(v_a_987_);
v___x_1016_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44));
v___x_1017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_991_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1019_ = l_Lean_Syntax_node5(v___x_991_, v___x_998_, v___x_1000_, v___x_1004_, v___x_1006_, v___x_1014_, v___x_1017_);
v___x_1020_ = l_Lean_Syntax_node2(v___x_991_, v___x_1018_, v___x_1019_, v_term_1015_);
v___x_1021_ = l_Lean_Syntax_node2(v___x_991_, v___x_992_, v___x_997_, v___x_1020_);
v___x_1022_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47);
v___x_1023_ = lean_box(0);
v___x_1024_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1021_, v___x_1022_, v_isMany_951_, v_isMany_951_, v___x_1023_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v___x_879_, v_a_867_);
lean_dec_ref_known(v___x_879_, 3);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1024_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1024_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref_known(v___x_879_, 3);
lean_dec(v_ref_878_);
v_a_1042_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_986_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_986_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref_known(v___x_879_, 3);
lean_dec(v_ref_878_);
v_a_1050_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_880_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_880_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___boxed(lean_object* v_stx_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_stx_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_stx_1058_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(lean_object* v_stx_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_1067_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___boxed(lean_object* v_stx_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(v_stx_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_stx_1076_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(lean_object* v_k_1085_, lean_object* v_x_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_1086_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___boxed(lean_object* v_k_1095_, lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(v_k_1095_, v_x_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v_x_1096_);
lean_dec(v_k_1095_);
return v_res_1104_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1));
v___x_1111_ = l_Lean_Expr_const___override(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4));
v___x_1118_ = l_Lean_Expr_const___override(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(lean_object* v_as_1119_, size_t v_sz_1120_, size_t v_i_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_a_1131_; lean_object* v_pairType_1135_; uint8_t v___x_1136_; 
v_pairType_1135_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1136_ = lean_usize_dec_lt(v_i_1121_, v_sz_1120_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_b_1122_);
return v___x_1137_;
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1138_ = lean_array_uget_borrowed(v_as_1119_, v_i_1121_);
v___x_1139_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_a_1138_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
if (lean_obj_tag(v_a_1140_) == 0)
{
lean_object* v_val_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_val_1141_ = lean_ctor_get(v_a_1140_, 0);
lean_inc(v_val_1141_);
lean_dec_ref_known(v_a_1140_, 1);
v___x_1142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2);
v___x_1143_ = l_Lean_mkApp3(v___x_1142_, v_pairType_1135_, v_b_1122_, v_val_1141_);
v_a_1131_ = v___x_1143_;
goto v___jp_1130_;
}
else
{
lean_object* v_val_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_val_1144_ = lean_ctor_get(v_a_1140_, 0);
lean_inc(v_val_1144_);
lean_dec_ref_known(v_a_1140_, 1);
v___x_1145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5);
v___x_1146_ = l_Lean_mkApp3(v___x_1145_, v_pairType_1135_, v_b_1122_, v_val_1144_);
v_a_1131_ = v___x_1146_;
goto v___jp_1130_;
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v_b_1122_);
v_a_1147_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1139_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1139_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
v___jp_1130_:
{
size_t v___x_1132_; size_t v___x_1133_; 
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_add(v_i_1121_, v___x_1132_);
v_i_1121_ = v___x_1133_;
v_b_1122_ = v_a_1131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___boxed(lean_object* v_as_1155_, lean_object* v_sz_1156_, lean_object* v_i_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1156_);
lean_dec(v_sz_1156_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_as_1155_, v_sz_boxed_1166_, v_i_boxed_1167_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_as_1155_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(lean_object* v_stxs_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v_pairType_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_box(0);
v_pairType_1178_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1179_ = l_Lean_Meta_mkArrayLit(v_pairType_1178_, v___x_1177_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; size_t v_sz_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v_sz_1181_ = lean_array_size(v_stxs_1169_);
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_stxs_1169_, v_sz_1181_, v___x_1182_, v_a_1180_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1183_;
}
else
{
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs___boxed(lean_object* v_stxs_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_stxs_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec_ref(v_stxs_1184_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(lean_object* v___x_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1193_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed(lean_object* v___x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(v___x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(lean_object* v_stx_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___y_1221_; lean_object* v_k_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
lean_inc(v_stx_1212_);
v_k_1231_ = l_Lean_Syntax_getKind(v_stx_1212_);
v___x_1232_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_1233_ = lean_name_eq(v_k_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_1235_ = lean_name_eq(v_k_1231_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1237_ = lean_name_eq(v_k_1231_, v___x_1236_);
lean_dec(v_k_1231_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0));
v___y_1221_ = v___x_1238_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1239_; lean_object* v___f_1240_; 
lean_inc(v_stx_1212_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_stx_1212_);
v___f_1240_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1240_, 0, v___x_1239_);
v___y_1221_ = v___f_1240_;
goto v___jp_1220_;
}
}
else
{
lean_object* v___x_1241_; lean_object* v___f_1242_; 
lean_dec(v_k_1231_);
lean_inc(v_stx_1212_);
v___x_1241_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1241_, 0, v_stx_1212_);
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*1, v___x_1235_);
v___f_1242_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1242_, 0, v___x_1241_);
v___y_1221_ = v___f_1242_;
goto v___jp_1220_;
}
}
else
{
uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___f_1245_; 
lean_dec(v_k_1231_);
v___x_1243_ = 0;
lean_inc(v_stx_1212_);
v___x_1244_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1244_, 0, v_stx_1212_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*1, v___x_1243_);
v___f_1245_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1245_, 0, v___x_1244_);
v___y_1221_ = v___f_1245_;
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v_toCold_1222_; lean_object* v_currRecDepth_1223_; lean_object* v_ref_1224_; uint16_t v_optionFlags_1225_; uint8_t v_suppressElabErrors_1226_; uint8_t v_isRecordingDeps_1227_; lean_object* v_ref_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_toCold_1222_ = lean_ctor_get(v___y_1217_, 0);
v_currRecDepth_1223_ = lean_ctor_get(v___y_1217_, 1);
v_ref_1224_ = lean_ctor_get(v___y_1217_, 2);
v_optionFlags_1225_ = lean_ctor_get_uint16(v___y_1217_, sizeof(void*)*3);
v_suppressElabErrors_1226_ = lean_ctor_get_uint8(v___y_1217_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1227_ = lean_ctor_get_uint8(v___y_1217_, sizeof(void*)*3 + 3);
v_ref_1228_ = l_Lean_replaceRef(v_stx_1212_, v_ref_1224_);
lean_dec(v_stx_1212_);
lean_inc(v_currRecDepth_1223_);
lean_inc_ref(v_toCold_1222_);
v___x_1229_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1229_, 0, v_toCold_1222_);
lean_ctor_set(v___x_1229_, 1, v_currRecDepth_1223_);
lean_ctor_set(v___x_1229_, 2, v_ref_1228_);
lean_ctor_set_uint16(v___x_1229_, sizeof(void*)*3, v_optionFlags_1225_);
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*3 + 2, v_suppressElabErrors_1226_);
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*3 + 3, v_isRecordingDeps_1227_);
lean_inc(v___y_1218_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1230_ = lean_apply_7(v___y_1221_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___x_1229_, v___y_1218_, lean_box(0));
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___boxed(lean_object* v_stx_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_stx_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(lean_object* v_as_1269_, size_t v_sz_1270_, size_t v_i_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_a_1281_; uint8_t v___x_1285_; 
v___x_1285_ = lean_usize_dec_lt(v_i_1271_, v_sz_1270_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_b_1272_);
return v___x_1286_;
}
else
{
lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1325_; 
v_fst_1287_ = lean_ctor_get(v_b_1272_, 0);
v_snd_1288_ = lean_ctor_get(v_b_1272_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_b_1272_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1290_ = v_b_1272_;
v_isShared_1291_ = v_isSharedCheck_1325_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_snd_1288_);
lean_inc(v_fst_1287_);
lean_dec(v_b_1272_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1325_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_a_1292_ = lean_array_uget_borrowed(v_as_1269_, v_i_1271_);
lean_inc(v_a_1292_);
v___x_1293_ = l_Lean_Syntax_getKind(v_a_1292_);
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1));
v___x_1295_ = lean_name_eq(v___x_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3));
v___x_1297_ = lean_name_eq(v___x_1293_, v___x_1296_);
lean_dec(v___x_1293_);
if (v___x_1297_ == 0)
{
lean_object* v_tcs_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_tcs_1298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4));
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_snd_1288_);
v___x_1300_ = lean_array_push(v_fst_1287_, v___x_1299_);
lean_inc(v_a_1292_);
v___x_1301_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_a_1292_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1303_ = lean_array_push(v___x_1300_, v_a_1302_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v_tcs_1298_);
lean_ctor_set(v___x_1290_, 0, v___x_1303_);
v___x_1305_ = v___x_1290_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_tcs_1298_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
v_a_1281_ = v___x_1305_;
goto v___jp_1280_;
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v___x_1300_);
lean_del_object(v___x_1290_);
v_a_1307_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1301_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1301_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_inc(v_a_1292_);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_a_1292_);
v___x_1316_ = lean_array_push(v_snd_1288_, v___x_1315_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1316_);
v___x_1318_ = v___x_1290_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v_a_1281_ = v___x_1318_;
goto v___jp_1280_;
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec(v___x_1293_);
lean_inc(v_a_1292_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1292_);
v___x_1321_ = lean_array_push(v_snd_1288_, v___x_1320_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1321_);
v___x_1323_ = v___x_1290_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_fst_1287_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
v_a_1281_ = v___x_1323_;
goto v___jp_1280_;
}
}
}
}
v___jp_1280_:
{
size_t v___x_1282_; size_t v___x_1283_; 
v___x_1282_ = ((size_t)1ULL);
v___x_1283_ = lean_usize_add(v_i_1271_, v___x_1282_);
v_i_1271_ = v___x_1283_;
v_b_1272_ = v_a_1281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___boxed(lean_object* v_as_1326_, lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
size_t v_sz_boxed_1337_; size_t v_i_boxed_1338_; lean_object* v_res_1339_; 
v_sz_boxed_1337_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1338_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v_as_1326_, v_sz_boxed_1337_, v_i_boxed_1338_, v_b_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v_as_1326_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(lean_object* v_c_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; size_t v_sz_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = l_Lean_Syntax_getArgs(v_c_1344_);
v___x_1354_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1));
v_sz_1355_ = lean_array_size(v___x_1353_);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v___x_1353_, v_sz_1355_, v___x_1356_, v___x_1354_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec_ref(v___x_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1374_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1374_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1374_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_fst_1362_; lean_object* v_snd_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_fst_1362_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_fst_1362_);
v_snd_1363_ = lean_ctor_get(v_a_1358_, 1);
lean_inc(v_snd_1363_);
lean_dec(v_a_1358_);
v___x_1364_ = lean_array_get_size(v_snd_1363_);
v___x_1365_ = lean_nat_dec_eq(v___x_1364_, v___x_1352_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v_items_1367_; lean_object* v___x_1369_; 
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_snd_1363_);
v_items_1367_ = lean_array_push(v_fst_1362_, v___x_1366_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_items_1367_);
v___x_1369_ = v___x_1360_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_items_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1372_; 
lean_dec(v_snd_1363_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_fst_1362_);
v___x_1372_ = v___x_1360_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_fst_1362_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1357_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1357_);
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
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___boxed(lean_object* v_c_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_c_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v_c_1383_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(lean_object* v_stx_1392_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
lean_inc(v_stx_1392_);
v___x_1394_ = l_Lean_Syntax_getKind(v_stx_1392_);
v___x_1395_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1396_ = lean_name_eq(v___x_1394_, v___x_1395_);
lean_dec(v___x_1394_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_stx_1392_);
v___x_1397_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; size_t v_sz_1401_; size_t v___x_1402_; lean_object* v_attrs_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_startTag_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1398_ = lean_unsigned_to_nat(2u);
v___x_1399_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1398_);
v___x_1400_ = l_Lean_Syntax_getArgs(v___x_1399_);
lean_dec(v___x_1399_);
v_sz_1401_ = lean_array_size(v___x_1400_);
v___x_1402_ = ((size_t)0ULL);
v_attrs_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_1401_, v___x_1402_, v___x_1400_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1404_);
v___x_1406_ = lean_unsigned_to_nat(1u);
v___x_1407_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1406_);
v___x_1408_ = lean_unsigned_to_nat(3u);
v___x_1409_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1408_);
v_startTag_1410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_1410_, 0, v___x_1405_);
lean_ctor_set(v_startTag_1410_, 1, v___x_1407_);
lean_ctor_set(v_startTag_1410_, 2, v_attrs_1403_);
lean_ctor_set(v_startTag_1410_, 3, v___x_1409_);
v___x_1411_ = l_Lean_Syntax_getNumArgs(v_stx_1392_);
v___x_1412_ = lean_unsigned_to_nat(4u);
v___x_1413_ = lean_nat_dec_eq(v___x_1411_, v___x_1412_);
lean_dec(v___x_1411_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_endTag_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1414_ = lean_unsigned_to_nat(5u);
v___x_1415_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1414_);
v___x_1416_ = lean_unsigned_to_nat(6u);
v___x_1417_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1416_);
v___x_1418_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5));
v___x_1419_ = lean_unsigned_to_nat(7u);
v___x_1420_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1419_);
v_endTag_1421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_1421_, 0, v___x_1415_);
lean_ctor_set(v_endTag_1421_, 1, v___x_1417_);
lean_ctor_set(v_endTag_1421_, 2, v___x_1418_);
lean_ctor_set(v_endTag_1421_, 3, v___x_1420_);
v___x_1422_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1412_);
lean_dec(v_stx_1392_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_endTag_1421_);
v___x_1425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1425_, 0, v_startTag_1410_);
lean_ctor_set(v___x_1425_, 1, v___x_1423_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec(v_stx_1392_);
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1428_, 0, v_startTag_1410_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg___boxed(lean_object* v_stx_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1430_);
return v_res_1432_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0));
v___x_1438_ = l_Lean_Expr_const___override(v___x_1437_, v___x_1436_);
return v___x_1438_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(uint8_t v___x_1441_, lean_object* v_b_1442_, lean_object* v_tm_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2);
v___x_1452_ = lean_box(0);
v___x_1453_ = l_Lean_Elab_Term_elabTermEnsuringType(v_tm_1443_, v___x_1451_, v___x_1441_, v___x_1441_, v___x_1452_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1464_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1458_ = lean_array_push(v_b_1442_, v_a_1454_);
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1458_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1460_);
v___x_1462_ = v___x_1456_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v_b_1442_);
v_a_1465_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1453_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1453_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___boxed(lean_object* v___x_1473_, lean_object* v_b_1474_, lean_object* v_tm_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v___x_18099__boxed_1483_; lean_object* v_res_1484_; 
v___x_18099__boxed_1483_ = lean_unbox(v___x_1473_);
v_res_1484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_18099__boxed_1483_, v_b_1474_, v_tm_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1484_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2));
v___x_1494_ = l_Lean_Expr_const___override(v___x_1493_, v___x_1492_);
return v___x_1494_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5));
v___x_1502_ = l_Lean_Expr_const___override(v___x_1501_, v___x_1500_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_box(0);
v___x_1508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0));
v___x_1509_ = l_Lean_Expr_const___override(v___x_1508_, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_box(0);
v___x_1515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2));
v___x_1516_ = l_Lean_Expr_const___override(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6));
v___x_1523_ = l_String_toRawSubstring_x27(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(lean_object* v_as_1534_, size_t v_sz_1535_, size_t v_i_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_a_1546_; lean_object* v___y_1551_; uint8_t v___x_1562_; 
v___x_1562_ = lean_usize_dec_lt(v_i_1536_, v_sz_1535_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_b_1537_);
return v___x_1563_;
}
else
{
lean_object* v_a_1564_; 
v_a_1564_ = lean_array_uget_borrowed(v_as_1534_, v_i_1536_);
switch(lean_obj_tag(v_a_1564_))
{
case 0:
{
lean_object* v_stx_1565_; lean_object* v_toCold_1566_; lean_object* v_currRecDepth_1567_; lean_object* v_ref_1568_; uint16_t v_optionFlags_1569_; uint8_t v_suppressElabErrors_1570_; uint8_t v_isRecordingDeps_1571_; lean_object* v_ref_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_stx_1565_ = lean_ctor_get(v_a_1564_, 0);
v_toCold_1566_ = lean_ctor_get(v___y_1542_, 0);
v_currRecDepth_1567_ = lean_ctor_get(v___y_1542_, 1);
v_ref_1568_ = lean_ctor_get(v___y_1542_, 2);
v_optionFlags_1569_ = lean_ctor_get_uint16(v___y_1542_, sizeof(void*)*3);
v_suppressElabErrors_1570_ = lean_ctor_get_uint8(v___y_1542_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1571_ = lean_ctor_get_uint8(v___y_1542_, sizeof(void*)*3 + 3);
v_ref_1572_ = l_Lean_replaceRef(v_stx_1565_, v_ref_1568_);
lean_inc(v_currRecDepth_1567_);
lean_inc_ref(v_toCold_1566_);
v___x_1573_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1573_, 0, v_toCold_1566_);
lean_ctor_set(v___x_1573_, 1, v_currRecDepth_1567_);
lean_ctor_set(v___x_1573_, 2, v_ref_1572_);
lean_ctor_set_uint16(v___x_1573_, sizeof(void*)*3, v_optionFlags_1569_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*3 + 2, v_suppressElabErrors_1570_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*3 + 3, v_isRecordingDeps_1571_);
lean_inc(v_stx_1565_);
v___x_1574_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_1565_, v___x_1573_, v___y_1543_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1574_, 1);
lean_inc(v_stx_1565_);
v___x_1575_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_1565_, v___x_1573_, v___y_1543_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref_known(v___x_1575_, 1);
lean_inc(v_stx_1565_);
v___x_1576_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1565_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v_startTag_1578_; lean_object* v_children_x3f_1579_; lean_object* v_name_1580_; lean_object* v_attrs_1581_; lean_object* v___x_1582_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v_startTag_1578_ = lean_ctor_get(v_a_1577_, 0);
lean_inc_ref(v_startTag_1578_);
v_children_x3f_1579_ = lean_ctor_get(v_a_1577_, 1);
lean_inc(v_children_x3f_1579_);
lean_dec(v_a_1577_);
v_name_1580_ = lean_ctor_get(v_startTag_1578_, 1);
lean_inc(v_name_1580_);
v_attrs_1581_ = lean_ctor_get(v_startTag_1578_, 2);
lean_inc_ref(v_attrs_1581_);
lean_dec_ref(v_startTag_1578_);
v___x_1582_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_1580_);
lean_dec(v_name_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_attrs_1581_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___x_1573_, v___y_1543_);
lean_dec_ref(v_attrs_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v_a_1593_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
if (lean_obj_tag(v_children_x3f_1579_) == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref_known(v___x_1573_, 3);
v___x_1598_ = lean_box(0);
v_a_1593_ = v___x_1598_;
goto v___jp_1592_;
}
else
{
lean_object* v_val_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1616_; 
v_val_1599_ = lean_ctor_get(v_children_x3f_1579_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_children_x3f_1579_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1601_ = v_children_x3f_1579_;
v_isShared_1602_ = v_isSharedCheck_1616_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_val_1599_);
lean_dec(v_children_x3f_1579_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1616_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_val_1599_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___x_1573_, v___y_1543_);
lean_dec_ref_known(v___x_1573_, 3);
lean_dec(v_val_1599_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_a_1604_);
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v_a_1593_ = v___x_1606_;
goto v___jp_1592_;
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_del_object(v___x_1601_);
lean_dec(v_a_1585_);
lean_dec(v_a_1583_);
lean_dec_ref(v_b_1537_);
v_a_1608_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1603_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1603_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
v___jp_1586_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_inc_ref(v___y_1588_);
v___x_1590_ = l_Lean_mkApp3(v___y_1588_, v___y_1587_, v_a_1585_, v___y_1589_);
v___x_1591_ = lean_array_push(v_b_1537_, v___x_1590_);
v_a_1546_ = v___x_1591_;
goto v___jp_1545_;
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1);
v___x_1595_ = l_Lean_mkStrLit(v_a_1583_);
if (lean_obj_tag(v_a_1593_) == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
v___y_1587_ = v___x_1595_;
v___y_1588_ = v___x_1594_;
v___y_1589_ = v___x_1596_;
goto v___jp_1586_;
}
else
{
lean_object* v_val_1597_; 
v_val_1597_ = lean_ctor_get(v_a_1593_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v_a_1593_, 1);
v___y_1587_ = v___x_1595_;
v___y_1588_ = v___x_1594_;
v___y_1589_ = v_val_1597_;
goto v___jp_1586_;
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_a_1583_);
lean_dec(v_children_x3f_1579_);
lean_dec_ref_known(v___x_1573_, 3);
lean_dec_ref(v_b_1537_);
v_a_1617_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1584_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1584_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_attrs_1581_);
lean_dec(v_children_x3f_1579_);
lean_dec_ref_known(v___x_1573_, 3);
lean_dec_ref(v_b_1537_);
v_a_1625_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1582_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1582_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref_known(v___x_1573_, 3);
lean_dec_ref(v_b_1537_);
v_a_1633_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1576_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1576_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref_known(v___x_1573_, 3);
lean_dec_ref(v_b_1537_);
v_a_1641_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1575_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1575_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref_known(v___x_1573_, 3);
lean_dec_ref(v_b_1537_);
v_a_1649_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1574_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1574_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
case 1:
{
lean_object* v_stx_1657_; lean_object* v_toCold_1658_; lean_object* v_currRecDepth_1659_; lean_object* v_ref_1660_; uint16_t v_optionFlags_1661_; uint8_t v_suppressElabErrors_1662_; uint8_t v_isRecordingDeps_1663_; lean_object* v___x_1664_; lean_object* v_ref_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_stx_1657_ = lean_ctor_get(v_a_1564_, 0);
v_toCold_1658_ = lean_ctor_get(v___y_1542_, 0);
v_currRecDepth_1659_ = lean_ctor_get(v___y_1542_, 1);
v_ref_1660_ = lean_ctor_get(v___y_1542_, 2);
v_optionFlags_1661_ = lean_ctor_get_uint16(v___y_1542_, sizeof(void*)*3);
v_suppressElabErrors_1662_ = lean_ctor_get_uint8(v___y_1542_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1663_ = lean_ctor_get_uint8(v___y_1542_, sizeof(void*)*3 + 3);
lean_inc_ref(v_stx_1657_);
v___x_1664_ = l_Lean_Html_Syntax_TextCommentsView_getSyntax(v_stx_1657_);
v_ref_1665_ = l_Lean_replaceRef(v___x_1664_, v_ref_1660_);
lean_dec(v___x_1664_);
lean_inc(v_currRecDepth_1659_);
lean_inc_ref(v_toCold_1658_);
v___x_1666_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1666_, 0, v_toCold_1658_);
lean_ctor_set(v___x_1666_, 1, v_currRecDepth_1659_);
lean_ctor_set(v___x_1666_, 2, v_ref_1665_);
lean_ctor_set_uint16(v___x_1666_, sizeof(void*)*3, v_optionFlags_1661_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*3 + 2, v_suppressElabErrors_1662_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*3 + 3, v_isRecordingDeps_1663_);
v___x_1667_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_stx_1657_, v___x_1666_, v___y_1543_);
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
v___x_1675_ = lean_array_push(v_b_1537_, v___x_1674_);
v_a_1546_ = v___x_1675_;
goto v___jp_1545_;
}
else
{
lean_dec(v_a_1668_);
v_a_1546_ = v_b_1537_;
goto v___jp_1545_;
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_b_1537_);
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
uint8_t v_isMany_1684_; lean_object* v_stx_1685_; lean_object* v_toCold_1686_; lean_object* v_currRecDepth_1687_; lean_object* v_ref_1688_; uint16_t v_optionFlags_1689_; uint8_t v_suppressElabErrors_1690_; uint8_t v_isRecordingDeps_1691_; lean_object* v_ref_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_isMany_1684_ = lean_ctor_get_uint8(v_a_1564_, sizeof(void*)*1);
v_stx_1685_ = lean_ctor_get(v_a_1564_, 0);
v_toCold_1686_ = lean_ctor_get(v___y_1542_, 0);
v_currRecDepth_1687_ = lean_ctor_get(v___y_1542_, 1);
v_ref_1688_ = lean_ctor_get(v___y_1542_, 2);
v_optionFlags_1689_ = lean_ctor_get_uint16(v___y_1542_, sizeof(void*)*3);
v_suppressElabErrors_1690_ = lean_ctor_get_uint8(v___y_1542_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1691_ = lean_ctor_get_uint8(v___y_1542_, sizeof(void*)*3 + 3);
v_ref_1692_ = l_Lean_replaceRef(v_stx_1685_, v_ref_1688_);
lean_inc(v_ref_1692_);
lean_inc(v_currRecDepth_1687_);
lean_inc_ref(v_toCold_1686_);
v___x_1693_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1693_, 0, v_toCold_1686_);
lean_ctor_set(v___x_1693_, 1, v_currRecDepth_1687_);
lean_ctor_set(v___x_1693_, 2, v_ref_1692_);
lean_ctor_set_uint16(v___x_1693_, sizeof(void*)*3, v_optionFlags_1689_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*3 + 2, v_suppressElabErrors_1690_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*3 + 3, v_isRecordingDeps_1691_);
lean_inc(v_stx_1685_);
v___x_1694_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_1684_, v_stx_1685_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___x_1693_, v___y_1543_);
if (lean_obj_tag(v___x_1694_) == 0)
{
if (v_isMany_1684_ == 0)
{
lean_object* v_a_1695_; lean_object* v_term_1696_; lean_object* v___x_1697_; 
lean_dec(v_ref_1692_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v_term_1696_ = lean_ctor_get(v_a_1695_, 1);
lean_inc(v_term_1696_);
lean_dec(v_a_1695_);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1562_, v_b_1537_, v_term_1696_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___x_1693_, v___y_1543_);
lean_dec_ref_known(v___x_1693_, 3);
v___y_1551_ = v___x_1697_;
goto v___jp_1550_;
}
else
{
lean_object* v_a_1698_; lean_object* v_quotContext_1699_; lean_object* v_currMacroScope_1700_; lean_object* v_term_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1698_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1694_, 1);
v_quotContext_1699_ = lean_ctor_get(v_toCold_1686_, 8);
v_currMacroScope_1700_ = lean_ctor_get(v_toCold_1686_, 9);
v_term_1701_ = lean_ctor_get(v_a_1698_, 1);
lean_inc(v_term_1701_);
lean_dec(v_a_1698_);
v___x_1702_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5));
v___x_1704_ = 0;
v___x_1705_ = l_Lean_SourceInfo_fromRef(v_ref_1692_, v___x_1704_);
lean_dec(v_ref_1692_);
v___x_1706_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7);
lean_inc(v_currMacroScope_1700_);
lean_inc(v_quotContext_1699_);
v___x_1707_ = l_Lean_addMacroScope(v_quotContext_1699_, v___x_1703_, v_currMacroScope_1700_);
v___x_1708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10));
lean_inc_n(v___x_1705_, 2);
v___x_1709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1705_);
lean_ctor_set(v___x_1709_, 1, v___x_1706_);
lean_ctor_set(v___x_1709_, 2, v___x_1707_);
lean_ctor_set(v___x_1709_, 3, v___x_1708_);
v___x_1710_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1711_ = l_Lean_Syntax_node1(v___x_1705_, v___x_1710_, v_term_1701_);
v___x_1712_ = l_Lean_Syntax_node2(v___x_1705_, v___x_1702_, v___x_1709_, v___x_1711_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1562_, v_b_1537_, v___x_1712_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___x_1693_, v___y_1543_);
lean_dec_ref_known(v___x_1693_, 3);
v___y_1551_ = v___x_1713_;
goto v___jp_1550_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref_known(v___x_1693_, 3);
lean_dec(v_ref_1692_);
lean_dec_ref(v_b_1537_);
v_a_1714_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1694_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1694_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
v___jp_1545_:
{
size_t v___x_1547_; size_t v___x_1548_; 
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1536_, v___x_1547_);
v_i_1536_ = v___x_1548_;
v_b_1537_ = v_a_1546_;
goto _start;
}
v___jp_1550_:
{
if (lean_obj_tag(v___y_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v_snd_1553_; 
v_a_1552_ = lean_ctor_get(v___y_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___y_1551_, 1);
v_snd_1553_ = lean_ctor_get(v_a_1552_, 1);
lean_inc(v_snd_1553_);
lean_dec(v_a_1552_);
v_a_1546_ = v_snd_1553_;
goto v___jp_1545_;
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_a_1554_ = lean_ctor_get(v___y_1551_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___y_1551_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___y_1551_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___y_1551_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(lean_object* v_stx_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_toCold_1730_; lean_object* v_currRecDepth_1731_; lean_object* v_ref_1732_; uint16_t v_optionFlags_1733_; uint8_t v_suppressElabErrors_1734_; uint8_t v_isRecordingDeps_1735_; lean_object* v___x_1736_; lean_object* v_es_1737_; lean_object* v_ref_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_toCold_1730_ = lean_ctor_get(v_a_1727_, 0);
v_currRecDepth_1731_ = lean_ctor_get(v_a_1727_, 1);
v_ref_1732_ = lean_ctor_get(v_a_1727_, 2);
v_optionFlags_1733_ = lean_ctor_get_uint16(v_a_1727_, sizeof(void*)*3);
v_suppressElabErrors_1734_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1735_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*3 + 3);
v___x_1736_ = lean_unsigned_to_nat(0u);
v_es_1737_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0));
v_ref_1738_ = l_Lean_replaceRef(v_stx_1722_, v_ref_1732_);
lean_inc(v_currRecDepth_1731_);
lean_inc_ref(v_toCold_1730_);
v___x_1739_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1739_, 0, v_toCold_1730_);
lean_ctor_set(v___x_1739_, 1, v_currRecDepth_1731_);
lean_ctor_set(v___x_1739_, 2, v_ref_1738_);
lean_ctor_set_uint16(v___x_1739_, sizeof(void*)*3, v_optionFlags_1733_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 2, v_suppressElabErrors_1734_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 3, v_isRecordingDeps_1735_);
v___x_1740_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_stx_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v___x_1739_, v_a_1728_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; size_t v_sz_1742_; size_t v___x_1743_; lean_object* v___x_1744_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v_sz_1742_ = lean_array_size(v_a_1741_);
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_a_1741_, v_sz_1742_, v___x_1743_, v_es_1737_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v___x_1739_, v_a_1728_);
lean_dec(v_a_1741_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1768_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1768_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1768_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = lean_array_get_size(v_a_1745_);
v___x_1750_ = lean_nat_dec_eq(v___x_1749_, v___x_1736_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_del_object(v___x_1747_);
v___x_1751_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1752_ = lean_array_to_list(v_a_1745_);
v___x_1753_ = l_Lean_Meta_mkArrayLit(v___x_1751_, v___x_1752_, v_a_1725_, v_a_1726_, v___x_1739_, v_a_1728_);
lean_dec_ref_known(v___x_1739_, 3);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1763_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1763_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1763_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1758_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3);
v___x_1759_ = l_Lean_Expr_app___override(v___x_1758_, v_a_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1759_);
v___x_1761_ = v___x_1756_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
return v___x_1753_;
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_dec(v_a_1745_);
lean_dec_ref_known(v___x_1739_, 3);
v___x_1764_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1764_);
v___x_1766_ = v___x_1747_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref_known(v___x_1739_, 3);
v_a_1769_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1744_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1744_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref_known(v___x_1739_, 3);
v_a_1777_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1740_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1740_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___boxed(lean_object* v_stx_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_stx_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_stx_1785_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___boxed(lean_object* v_as_1794_, lean_object* v_sz_1795_, lean_object* v_i_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
size_t v_sz_boxed_1805_; size_t v_i_boxed_1806_; lean_object* v_res_1807_; 
v_sz_boxed_1805_ = lean_unbox_usize(v_sz_1795_);
lean_dec(v_sz_1795_);
v_i_boxed_1806_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v_res_1807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_as_1794_, v_sz_boxed_1805_, v_i_boxed_1806_, v_b_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec_ref(v_as_1794_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(lean_object* v_stx_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1808_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___boxed(lean_object* v_stx_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(v_stx_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(lean_object* v_a_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg___boxed(lean_object* v_a_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(v_a_1829_);
lean_dec(v_a_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(lean_object* v_a_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1832_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___boxed(lean_object* v_a_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(v_a_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v_a_1841_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(lean_object* v_stx_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1));
lean_inc(v_stx_1862_);
v___x_1871_ = l_Lean_Syntax_isOfKind(v_stx_1862_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec(v_stx_1862_);
v___x_1872_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v_h_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1873_ = lean_unsigned_to_nat(2u);
v_h_1874_ = l_Lean_Syntax_getArg(v_stx_1862_, v___x_1873_);
lean_dec(v_stx_1862_);
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3));
lean_inc(v_h_1874_);
v___x_1876_ = l_Lean_Syntax_isOfKind(v_h_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; 
lean_dec(v_h_1874_);
v___x_1877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; 
v___x_1878_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_h_1874_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec(v_h_1874_);
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___boxed(lean_object* v_stx_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(lean_object* v_stx_1888_, lean_object* v_x_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1888_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___boxed(lean_object* v_stx_1898_, lean_object* v_x_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(v_stx_1898_, v_x_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_x_1899_);
return v_res_1907_;
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
