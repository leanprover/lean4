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
lean_object* v_toCold_604_; lean_object* v_currRecDepth_605_; lean_object* v_ref_606_; uint16_t v_optionFlags_607_; uint8_t v_suppressElabErrors_608_; uint8_t v_isRecordingDeps_609_; lean_object* v_ref_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_toCold_604_ = lean_ctor_get(v_a_601_, 0);
v_currRecDepth_605_ = lean_ctor_get(v_a_601_, 1);
v_ref_606_ = lean_ctor_get(v_a_601_, 2);
v_optionFlags_607_ = lean_ctor_get_uint16(v_a_601_, sizeof(void*)*3);
v_suppressElabErrors_608_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 2);
v_isRecordingDeps_609_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 3);
v_ref_610_ = l_Lean_replaceRef(v_stx_596_, v_ref_606_);
lean_inc(v_currRecDepth_605_);
lean_inc_ref(v_toCold_604_);
v___x_611_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_611_, 0, v_toCold_604_);
lean_ctor_set(v___x_611_, 1, v_currRecDepth_605_);
lean_ctor_set(v___x_611_, 2, v_ref_610_);
lean_ctor_set_uint16(v___x_611_, sizeof(void*)*3, v_optionFlags_607_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*3 + 2, v_suppressElabErrors_608_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*3 + 3, v_isRecordingDeps_609_);
v___x_612_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v___x_611_, v_a_602_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
if (lean_obj_tag(v_a_613_) == 0)
{
lean_object* v_stx_614_; lean_object* v___x_615_; 
v_stx_614_ = lean_ctor_get(v_a_613_, 0);
lean_inc(v_stx_614_);
lean_dec_ref_known(v_a_613_, 1);
v___x_615_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_stx_614_, v___x_611_, v_a_602_);
lean_dec_ref_known(v___x_611_, 3);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_624_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_624_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_mkStrLit(v_a_616_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_625_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_615_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_615_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_stx_633_; uint8_t v___x_634_; lean_object* v___x_635_; 
v_stx_633_ = lean_ctor_get(v_a_613_, 0);
lean_inc(v_stx_633_);
lean_dec_ref_known(v_a_613_, 1);
v___x_634_ = 0;
v___x_635_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v___x_634_, v_stx_633_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v___x_611_, v_a_602_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_term_637_; lean_object* v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v_term_637_ = lean_ctor_get(v_a_636_, 1);
lean_inc(v_term_637_);
lean_dec(v_a_636_);
v___x_638_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3);
v___x_639_ = 1;
v___x_640_ = lean_box(0);
v___x_641_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_637_, v___x_638_, v___x_639_, v___x_639_, v___x_640_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v___x_611_, v_a_602_);
lean_dec_ref_known(v___x_611_, 3);
return v___x_641_;
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec_ref_known(v___x_611_, 3);
v_a_642_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_635_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_635_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref_known(v___x_611_, 3);
v_a_650_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_612_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_612_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___boxed(lean_object* v_stx_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_stx_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_stx_658_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(lean_object* v_00_u03b1_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___boxed(lean_object* v_00_u03b1_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(v_00_u03b1_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(lean_object* v_stx_691_){
_start:
{
lean_object* v___x_693_; lean_object* v_c_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v_c_694_ = l_Lean_Syntax_getArg(v_stx_691_, v___x_693_);
lean_inc(v_c_694_);
v___x_695_ = l_Lean_Syntax_getKind(v_c_694_);
v___x_696_ = ((lean_object*)(l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1));
v___x_697_ = lean_name_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_699_ = lean_name_eq(v___x_695_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_701_ = lean_name_eq(v___x_695_, v___x_700_);
lean_dec(v___x_695_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec(v_c_694_);
v___x_702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_703_, 0, v_c_694_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*1, v___x_699_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v___x_695_);
v___x_705_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_705_, 0, v_c_694_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_699_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
else
{
lean_object* v___x_707_; lean_object* v_val_x3f_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
lean_dec(v___x_695_);
v___x_707_ = lean_unsigned_to_nat(1u);
v_val_x3f_708_ = l_Lean_Syntax_getArg(v_stx_691_, v___x_707_);
v___x_709_ = l_Lean_Syntax_getNumArgs(v_val_x3f_708_);
v___x_710_ = lean_nat_dec_eq(v___x_709_, v___x_693_);
lean_dec(v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_711_ = l_Lean_Syntax_getArg(v_val_x3f_708_, v___x_693_);
v___x_712_ = l_Lean_Syntax_getArg(v_val_x3f_708_, v___x_707_);
lean_dec(v_val_x3f_708_);
v___x_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_713_, 0, v_c_694_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_val_x3f_708_);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v_c_694_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___boxed(lean_object* v_stx_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_718_);
lean_dec(v_stx_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 1)
{
lean_object* v_args_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_args_723_ = lean_ctor_get(v_x_721_, 2);
v___x_724_ = lean_array_get_size(v_args_723_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_dec_eq(v___x_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_727_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_array_fget_borrowed(v_args_723_, v___x_728_);
if (lean_obj_tag(v___x_729_) == 2)
{
lean_object* v_val_730_; lean_object* v___x_731_; 
v_val_730_ = lean_ctor_get(v___x_729_, 1);
lean_inc_ref(v_val_730_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v_val_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_732_;
}
}
}
else
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg___boxed(lean_object* v_x_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_734_);
lean_dec(v_x_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(lean_object* v_a_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_737_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1___boxed(lean_object* v_a_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_a_746_);
return v_res_754_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = l_Lean_Level_ofNat(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_box(0);
v___x_761_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_764_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_767_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1));
v___x_768_ = l_Lean_Expr_const___override(v___x_767_, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6(void){
_start:
{
lean_object* v_strType_769_; lean_object* v___x_770_; lean_object* v_pairType_771_; 
v_strType_769_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_770_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5);
v_pairType_771_ = l_Lean_mkAppB(v___x_770_, v_strType_769_, v_strType_769_);
return v_pairType_771_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_776_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8));
v___x_777_ = l_Lean_Expr_const___override(v___x_776_, v___x_775_);
return v___x_777_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10(void){
_start:
{
lean_object* v_pairType_778_; lean_object* v___x_779_; lean_object* v_arrayType_780_; 
v_pairType_778_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_779_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9);
v_arrayType_780_ = l_Lean_Expr_app___override(v___x_779_, v_pairType_778_);
return v_arrayType_780_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_786_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12));
v___x_787_ = l_Lean_Expr_const___override(v___x_786_, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8));
v___x_789_ = l_Lean_mkStrLit(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15(void){
_start:
{
lean_object* v_pairType_790_; lean_object* v___x_791_; 
v_pairType_790_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v_pairType_790_);
return v___x_791_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20));
v___x_802_ = l_String_toRawSubstring_x27(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30));
v___x_823_ = l_String_toRawSubstring_x27(v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0));
v___x_831_ = l_String_toRawSubstring_x27(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47(void){
_start:
{
lean_object* v_arrayType_854_; lean_object* v___x_855_; 
v_arrayType_854_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10);
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v_arrayType_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(lean_object* v_stx_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_strType_866_; lean_object* v_toCold_867_; lean_object* v_currRecDepth_868_; lean_object* v_ref_869_; uint16_t v_optionFlags_870_; uint8_t v_suppressElabErrors_871_; uint8_t v_isRecordingDeps_872_; lean_object* v_ref_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_865_ = lean_box(0);
v_strType_866_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v_toCold_867_ = lean_ctor_get(v_a_861_, 0);
v_currRecDepth_868_ = lean_ctor_get(v_a_861_, 1);
v_ref_869_ = lean_ctor_get(v_a_861_, 2);
v_optionFlags_870_ = lean_ctor_get_uint16(v_a_861_, sizeof(void*)*3);
v_suppressElabErrors_871_ = lean_ctor_get_uint8(v_a_861_, sizeof(void*)*3 + 2);
v_isRecordingDeps_872_ = lean_ctor_get_uint8(v_a_861_, sizeof(void*)*3 + 3);
v_ref_873_ = l_Lean_replaceRef(v_stx_856_, v_ref_869_);
lean_inc(v_ref_873_);
lean_inc(v_currRecDepth_868_);
lean_inc_ref(v_toCold_867_);
v___x_874_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_874_, 0, v_toCold_867_);
lean_ctor_set(v___x_874_, 1, v_currRecDepth_868_);
lean_ctor_set(v___x_874_, 2, v_ref_873_);
lean_ctor_set_uint16(v___x_874_, sizeof(void*)*3, v_optionFlags_870_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*3 + 2, v_suppressElabErrors_871_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*3 + 3, v_isRecordingDeps_872_);
v___x_875_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_856_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
switch(lean_obj_tag(v_a_876_))
{
case 0:
{
lean_object* v_stx_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_916_; 
lean_dec(v_ref_873_);
v_stx_877_ = lean_ctor_get(v_a_876_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_876_);
if (v_isSharedCheck_916_ == 0)
{
v___x_879_ = v_a_876_;
v_isShared_880_ = v_isSharedCheck_916_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_stx_877_);
lean_dec(v_a_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_916_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_name_881_; lean_object* v_val_882_; lean_object* v___x_883_; 
v_name_881_ = lean_ctor_get(v_stx_877_, 0);
lean_inc(v_name_881_);
v_val_882_ = lean_ctor_get(v_stx_877_, 2);
lean_inc(v_val_882_);
lean_dec_ref(v_stx_877_);
v___x_883_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_881_);
lean_dec(v_name_881_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_val_882_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v___x_874_, v_a_862_);
lean_dec_ref_known(v___x_874_, 3);
lean_dec(v_val_882_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_899_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_899_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_899_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_899_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_890_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_891_ = l_Lean_mkStrLit(v_a_884_);
v___x_892_ = l_Lean_mkApp4(v___x_890_, v_strType_866_, v_strType_866_, v___x_891_, v_a_886_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_892_);
v___x_894_ = v___x_879_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_894_);
v___x_896_ = v___x_888_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_884_);
lean_del_object(v___x_879_);
v_a_900_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_885_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_885_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_val_882_);
lean_del_object(v___x_879_);
lean_dec_ref_known(v___x_874_, 3);
v_a_908_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_883_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_883_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
case 1:
{
lean_object* v_stx_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref_known(v___x_874_, 3);
lean_dec(v_ref_873_);
v_stx_917_ = lean_ctor_get(v_a_876_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_a_876_);
if (v_isSharedCheck_945_ == 0)
{
v___x_919_ = v_a_876_;
v_isShared_920_ = v_isSharedCheck_945_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_stx_917_);
lean_dec(v_a_876_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_945_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_stx_917_);
lean_dec(v_stx_917_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_936_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_936_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_936_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_936_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_926_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_927_ = l_Lean_mkStrLit(v_a_922_);
v___x_928_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14);
v___x_929_ = l_Lean_mkApp4(v___x_926_, v_strType_866_, v_strType_866_, v___x_927_, v___x_928_);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 0);
lean_ctor_set(v___x_919_, 0, v___x_929_);
v___x_931_ = v___x_919_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_935_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_931_);
v___x_933_ = v___x_924_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_del_object(v___x_919_);
v_a_937_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_921_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_921_);
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
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
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
}
default: 
{
uint8_t v_isMany_946_; 
v_isMany_946_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*1);
if (v_isMany_946_ == 0)
{
lean_object* v_stx_947_; lean_object* v___x_948_; 
lean_dec(v_ref_873_);
v_stx_947_ = lean_ctor_get(v_a_876_, 0);
lean_inc(v_stx_947_);
lean_dec_ref_known(v_a_876_, 1);
v___x_948_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_946_, v_stx_947_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v___x_874_, v_a_862_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v_term_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v_term_950_ = lean_ctor_get(v_a_949_, 1);
lean_inc(v_term_950_);
lean_dec(v_a_949_);
v___x_951_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15);
v___x_952_ = 1;
v___x_953_ = lean_box(0);
v___x_954_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_950_, v___x_951_, v___x_952_, v___x_952_, v___x_953_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v___x_874_, v_a_862_);
lean_dec_ref_known(v___x_874_, 3);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_963_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v_a_955_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_954_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_954_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref_known(v___x_874_, 3);
v_a_972_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_948_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_948_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_stx_980_; lean_object* v___x_981_; 
v_stx_980_ = lean_ctor_get(v_a_876_, 0);
lean_inc(v_stx_980_);
lean_dec_ref_known(v_a_876_, 1);
v___x_981_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_946_, v_stx_980_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v___x_874_, v_a_862_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_quotContext_983_; lean_object* v_currMacroScope_984_; uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_term_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v_quotContext_983_ = lean_ctor_get(v_toCold_867_, 8);
v_currMacroScope_984_ = lean_ctor_get(v_toCold_867_, 9);
v___x_985_ = 0;
v___x_986_ = l_Lean_SourceInfo_fromRef(v_ref_873_, v___x_985_);
lean_dec(v_ref_873_);
v___x_987_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_988_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21);
v___x_989_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24));
lean_inc_n(v_currMacroScope_984_, 3);
lean_inc_n(v_quotContext_983_, 3);
v___x_990_ = l_Lean_addMacroScope(v_quotContext_983_, v___x_989_, v_currMacroScope_984_);
v___x_991_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26));
lean_inc_n(v___x_986_, 10);
v___x_992_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_992_, 0, v___x_986_);
lean_ctor_set(v___x_992_, 1, v___x_988_);
lean_ctor_set(v___x_992_, 2, v___x_990_);
lean_ctor_set(v___x_992_, 3, v___x_991_);
v___x_993_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28));
v___x_994_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29));
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_986_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31);
v___x_997_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32));
v___x_998_ = l_Lean_addMacroScope(v_quotContext_983_, v___x_997_, v_currMacroScope_984_);
v___x_999_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_999_, 0, v___x_986_);
lean_ctor_set(v___x_999_, 1, v___x_996_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
lean_ctor_set(v___x_999_, 3, v___x_865_);
v___x_1000_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_986_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35));
v___x_1003_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36);
v___x_1004_ = l_Lean_addMacroScope(v_quotContext_983_, v___x_864_, v_currMacroScope_984_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42));
v___x_1006_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1006_, 0, v___x_986_);
lean_ctor_set(v___x_1006_, 1, v___x_1003_);
lean_ctor_set(v___x_1006_, 2, v___x_1004_);
lean_ctor_set(v___x_1006_, 3, v___x_1005_);
v___x_1007_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43));
v___x_1008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_986_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
lean_inc_ref(v___x_1006_);
v___x_1009_ = l_Lean_Syntax_node3(v___x_986_, v___x_1002_, v___x_1006_, v___x_1008_, v___x_1006_);
v_term_1010_ = lean_ctor_get(v_a_982_, 1);
lean_inc(v_term_1010_);
lean_dec(v_a_982_);
v___x_1011_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44));
v___x_1012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_986_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1014_ = l_Lean_Syntax_node5(v___x_986_, v___x_993_, v___x_995_, v___x_999_, v___x_1001_, v___x_1009_, v___x_1012_);
v___x_1015_ = l_Lean_Syntax_node2(v___x_986_, v___x_1013_, v___x_1014_, v_term_1010_);
v___x_1016_ = l_Lean_Syntax_node2(v___x_986_, v___x_987_, v___x_992_, v___x_1015_);
v___x_1017_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47);
v___x_1018_ = lean_box(0);
v___x_1019_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1016_, v___x_1017_, v_isMany_946_, v_isMany_946_, v___x_1018_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v___x_874_, v_a_862_);
lean_dec_ref_known(v___x_874_, 3);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_a_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1019_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1019_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref_known(v___x_874_, 3);
lean_dec(v_ref_873_);
v_a_1037_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_981_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_981_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref_known(v___x_874_, 3);
lean_dec(v_ref_873_);
v_a_1045_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_875_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_875_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___boxed(lean_object* v_stx_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_stx_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_stx_1053_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(lean_object* v_stx_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_1062_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___boxed(lean_object* v_stx_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(v_stx_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_stx_1071_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(lean_object* v_k_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_1081_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___boxed(lean_object* v_k_1090_, lean_object* v_x_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(v_k_1090_, v_x_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v_x_1091_);
lean_dec(v_k_1090_);
return v_res_1099_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1));
v___x_1106_ = l_Lean_Expr_const___override(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4));
v___x_1113_ = l_Lean_Expr_const___override(v___x_1112_, v___x_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(lean_object* v_as_1114_, size_t v_sz_1115_, size_t v_i_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_a_1126_; lean_object* v_pairType_1130_; uint8_t v___x_1131_; 
v_pairType_1130_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1131_ = lean_usize_dec_lt(v_i_1116_, v_sz_1115_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_b_1117_);
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1134_; 
v_a_1133_ = lean_array_uget_borrowed(v_as_1114_, v_i_1116_);
v___x_1134_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_a_1133_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
if (lean_obj_tag(v_a_1135_) == 0)
{
lean_object* v_val_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_val_1136_ = lean_ctor_get(v_a_1135_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v_a_1135_, 1);
v___x_1137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2);
v___x_1138_ = l_Lean_mkApp3(v___x_1137_, v_pairType_1130_, v_b_1117_, v_val_1136_);
v_a_1126_ = v___x_1138_;
goto v___jp_1125_;
}
else
{
lean_object* v_val_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_val_1139_ = lean_ctor_get(v_a_1135_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v_a_1135_, 1);
v___x_1140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5);
v___x_1141_ = l_Lean_mkApp3(v___x_1140_, v_pairType_1130_, v_b_1117_, v_val_1139_);
v_a_1126_ = v___x_1141_;
goto v___jp_1125_;
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_b_1117_);
v_a_1142_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1134_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1134_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
v___jp_1125_:
{
size_t v___x_1127_; size_t v___x_1128_; 
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1116_, v___x_1127_);
v_i_1116_ = v___x_1128_;
v_b_1117_ = v_a_1126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___boxed(lean_object* v_as_1150_, lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_as_1150_, v_sz_boxed_1161_, v_i_boxed_1162_, v_b_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_as_1150_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(lean_object* v_stxs_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v_pairType_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_box(0);
v_pairType_1173_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1174_ = l_Lean_Meta_mkArrayLit(v_pairType_1173_, v___x_1172_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; size_t v_sz_1176_; size_t v___x_1177_; lean_object* v___x_1178_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v_sz_1176_ = lean_array_size(v_stxs_1164_);
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_stxs_1164_, v_sz_1176_, v___x_1177_, v_a_1175_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
return v___x_1178_;
}
else
{
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs___boxed(lean_object* v_stxs_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_stxs_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec_ref(v_stxs_1179_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(lean_object* v___x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1188_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed(lean_object* v___x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(v___x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(lean_object* v_stx_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___y_1216_; lean_object* v_k_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
lean_inc(v_stx_1207_);
v_k_1226_ = l_Lean_Syntax_getKind(v_stx_1207_);
v___x_1227_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_1228_ = lean_name_eq(v_k_1226_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_1230_ = lean_name_eq(v_k_1226_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1232_ = lean_name_eq(v_k_1226_, v___x_1231_);
lean_dec(v_k_1226_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0));
v___y_1216_ = v___x_1233_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1234_; lean_object* v___f_1235_; 
lean_inc(v_stx_1207_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_stx_1207_);
v___f_1235_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1235_, 0, v___x_1234_);
v___y_1216_ = v___f_1235_;
goto v___jp_1215_;
}
}
else
{
lean_object* v___x_1236_; lean_object* v___f_1237_; 
lean_dec(v_k_1226_);
lean_inc(v_stx_1207_);
v___x_1236_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1236_, 0, v_stx_1207_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*1, v___x_1230_);
v___f_1237_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1237_, 0, v___x_1236_);
v___y_1216_ = v___f_1237_;
goto v___jp_1215_;
}
}
else
{
uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; 
lean_dec(v_k_1226_);
v___x_1238_ = 0;
lean_inc(v_stx_1207_);
v___x_1239_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1239_, 0, v_stx_1207_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*1, v___x_1238_);
v___f_1240_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1240_, 0, v___x_1239_);
v___y_1216_ = v___f_1240_;
goto v___jp_1215_;
}
v___jp_1215_:
{
lean_object* v_toCold_1217_; lean_object* v_currRecDepth_1218_; lean_object* v_ref_1219_; uint16_t v_optionFlags_1220_; uint8_t v_suppressElabErrors_1221_; uint8_t v_isRecordingDeps_1222_; lean_object* v_ref_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_toCold_1217_ = lean_ctor_get(v___y_1212_, 0);
v_currRecDepth_1218_ = lean_ctor_get(v___y_1212_, 1);
v_ref_1219_ = lean_ctor_get(v___y_1212_, 2);
v_optionFlags_1220_ = lean_ctor_get_uint16(v___y_1212_, sizeof(void*)*3);
v_suppressElabErrors_1221_ = lean_ctor_get_uint8(v___y_1212_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1222_ = lean_ctor_get_uint8(v___y_1212_, sizeof(void*)*3 + 3);
v_ref_1223_ = l_Lean_replaceRef(v_stx_1207_, v_ref_1219_);
lean_dec(v_stx_1207_);
lean_inc(v_currRecDepth_1218_);
lean_inc_ref(v_toCold_1217_);
v___x_1224_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1224_, 0, v_toCold_1217_);
lean_ctor_set(v___x_1224_, 1, v_currRecDepth_1218_);
lean_ctor_set(v___x_1224_, 2, v_ref_1223_);
lean_ctor_set_uint16(v___x_1224_, sizeof(void*)*3, v_optionFlags_1220_);
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*3 + 2, v_suppressElabErrors_1221_);
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*3 + 3, v_isRecordingDeps_1222_);
lean_inc(v___y_1213_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc_ref(v___y_1208_);
v___x_1225_ = lean_apply_7(v___y_1216_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___x_1224_, v___y_1213_, lean_box(0));
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___boxed(lean_object* v_stx_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_stx_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(lean_object* v_as_1264_, size_t v_sz_1265_, size_t v_i_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_a_1276_; uint8_t v___x_1280_; 
v___x_1280_ = lean_usize_dec_lt(v_i_1266_, v_sz_1265_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_b_1267_);
return v___x_1281_;
}
else
{
lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1320_; 
v_fst_1282_ = lean_ctor_get(v_b_1267_, 0);
v_snd_1283_ = lean_ctor_get(v_b_1267_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_b_1267_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1285_ = v_b_1267_;
v_isShared_1286_ = v_isSharedCheck_1320_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_inc(v_fst_1282_);
lean_dec(v_b_1267_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1320_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_a_1287_ = lean_array_uget_borrowed(v_as_1264_, v_i_1266_);
lean_inc(v_a_1287_);
v___x_1288_ = l_Lean_Syntax_getKind(v_a_1287_);
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1));
v___x_1290_ = lean_name_eq(v___x_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3));
v___x_1292_ = lean_name_eq(v___x_1288_, v___x_1291_);
lean_dec(v___x_1288_);
if (v___x_1292_ == 0)
{
lean_object* v_tcs_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_tcs_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4));
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_snd_1283_);
v___x_1295_ = lean_array_push(v_fst_1282_, v___x_1294_);
lean_inc(v_a_1287_);
v___x_1296_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_a_1287_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = lean_array_push(v___x_1295_, v_a_1297_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_tcs_1293_);
lean_ctor_set(v___x_1285_, 0, v___x_1298_);
v___x_1300_ = v___x_1285_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_tcs_1293_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
v_a_1276_ = v___x_1300_;
goto v___jp_1275_;
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v___x_1295_);
lean_del_object(v___x_1285_);
v_a_1302_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1296_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1296_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_inc(v_a_1287_);
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v_a_1287_);
v___x_1311_ = lean_array_push(v_snd_1283_, v___x_1310_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1311_);
v___x_1313_ = v___x_1285_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_fst_1282_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
v_a_1276_ = v___x_1313_;
goto v___jp_1275_;
}
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec(v___x_1288_);
lean_inc(v_a_1287_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_a_1287_);
v___x_1316_ = lean_array_push(v_snd_1283_, v___x_1315_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1316_);
v___x_1318_ = v___x_1285_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_fst_1282_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v_a_1276_ = v___x_1318_;
goto v___jp_1275_;
}
}
}
}
v___jp_1275_:
{
size_t v___x_1277_; size_t v___x_1278_; 
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_add(v_i_1266_, v___x_1277_);
v_i_1266_ = v___x_1278_;
v_b_1267_ = v_a_1276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___boxed(lean_object* v_as_1321_, lean_object* v_sz_1322_, lean_object* v_i_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1322_);
lean_dec(v_sz_1322_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1323_);
lean_dec(v_i_1323_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v_as_1321_, v_sz_boxed_1332_, v_i_boxed_1333_, v_b_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v_as_1321_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(lean_object* v_c_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = l_Lean_Syntax_getArgs(v_c_1339_);
v___x_1349_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1));
v_sz_1350_ = lean_array_size(v___x_1348_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v___x_1348_, v_sz_1350_, v___x_1351_, v___x_1349_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___x_1348_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1369_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1369_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1369_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_fst_1357_; lean_object* v_snd_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_fst_1357_ = lean_ctor_get(v_a_1353_, 0);
lean_inc(v_fst_1357_);
v_snd_1358_ = lean_ctor_get(v_a_1353_, 1);
lean_inc(v_snd_1358_);
lean_dec(v_a_1353_);
v___x_1359_ = lean_array_get_size(v_snd_1358_);
v___x_1360_ = lean_nat_dec_eq(v___x_1359_, v___x_1347_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v_items_1362_; lean_object* v___x_1364_; 
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_snd_1358_);
v_items_1362_ = lean_array_push(v_fst_1357_, v___x_1361_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_items_1362_);
v___x_1364_ = v___x_1355_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_items_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
else
{
lean_object* v___x_1367_; 
lean_dec(v_snd_1358_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_fst_1357_);
v___x_1367_ = v___x_1355_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1357_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1352_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1352_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___boxed(lean_object* v_c_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_c_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v_c_1378_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(lean_object* v_stx_1387_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
lean_inc(v_stx_1387_);
v___x_1389_ = l_Lean_Syntax_getKind(v_stx_1387_);
v___x_1390_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1391_ = lean_name_eq(v___x_1389_, v___x_1390_);
lean_dec(v___x_1389_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
lean_dec(v_stx_1387_);
v___x_1392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; size_t v_sz_1396_; size_t v___x_1397_; lean_object* v_attrs_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_startTag_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1393_ = lean_unsigned_to_nat(2u);
v___x_1394_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1393_);
v___x_1395_ = l_Lean_Syntax_getArgs(v___x_1394_);
lean_dec(v___x_1394_);
v_sz_1396_ = lean_array_size(v___x_1395_);
v___x_1397_ = ((size_t)0ULL);
v_attrs_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_1396_, v___x_1397_, v___x_1395_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1399_);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1401_);
v___x_1403_ = lean_unsigned_to_nat(3u);
v___x_1404_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1403_);
v_startTag_1405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_1405_, 0, v___x_1400_);
lean_ctor_set(v_startTag_1405_, 1, v___x_1402_);
lean_ctor_set(v_startTag_1405_, 2, v_attrs_1398_);
lean_ctor_set(v_startTag_1405_, 3, v___x_1404_);
v___x_1406_ = l_Lean_Syntax_getNumArgs(v_stx_1387_);
v___x_1407_ = lean_unsigned_to_nat(4u);
v___x_1408_ = lean_nat_dec_eq(v___x_1406_, v___x_1407_);
lean_dec(v___x_1406_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_endTag_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1409_ = lean_unsigned_to_nat(5u);
v___x_1410_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1409_);
v___x_1411_ = lean_unsigned_to_nat(6u);
v___x_1412_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1411_);
v___x_1413_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5));
v___x_1414_ = lean_unsigned_to_nat(7u);
v___x_1415_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1414_);
v_endTag_1416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_1416_, 0, v___x_1410_);
lean_ctor_set(v_endTag_1416_, 1, v___x_1412_);
lean_ctor_set(v_endTag_1416_, 2, v___x_1413_);
lean_ctor_set(v_endTag_1416_, 3, v___x_1415_);
v___x_1417_ = l_Lean_Syntax_getArg(v_stx_1387_, v___x_1407_);
lean_dec(v_stx_1387_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_endTag_1416_);
v___x_1420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1420_, 0, v_startTag_1405_);
lean_ctor_set(v___x_1420_, 1, v___x_1418_);
lean_ctor_set(v___x_1420_, 2, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec(v_stx_1387_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1423_, 0, v_startTag_1405_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
lean_ctor_set(v___x_1423_, 2, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg___boxed(lean_object* v_stx_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1425_);
return v_res_1427_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0));
v___x_1433_ = l_Lean_Expr_const___override(v___x_1432_, v___x_1431_);
return v___x_1433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(uint8_t v___x_1436_, lean_object* v_b_1437_, lean_object* v_tm_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2);
v___x_1447_ = lean_box(0);
v___x_1448_ = l_Lean_Elab_Term_elabTermEnsuringType(v_tm_1438_, v___x_1446_, v___x_1436_, v___x_1436_, v___x_1447_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1459_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1453_ = lean_array_push(v_b_1437_, v_a_1449_);
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1453_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1455_);
v___x_1457_ = v___x_1451_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v_b_1437_);
v_a_1460_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1448_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1448_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___boxed(lean_object* v___x_1468_, lean_object* v_b_1469_, lean_object* v_tm_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v___x_18099__boxed_1478_; lean_object* v_res_1479_; 
v___x_18099__boxed_1478_ = lean_unbox(v___x_1468_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_18099__boxed_1478_, v_b_1469_, v_tm_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1479_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_box(0);
v___x_1488_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2));
v___x_1489_ = l_Lean_Expr_const___override(v___x_1488_, v___x_1487_);
return v___x_1489_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5));
v___x_1497_ = l_Lean_Expr_const___override(v___x_1496_, v___x_1495_);
return v___x_1497_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_box(0);
v___x_1503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0));
v___x_1504_ = l_Lean_Expr_const___override(v___x_1503_, v___x_1502_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2));
v___x_1511_ = l_Lean_Expr_const___override(v___x_1510_, v___x_1509_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6));
v___x_1518_ = l_String_toRawSubstring_x27(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(lean_object* v_as_1529_, size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_a_1541_; lean_object* v___y_1546_; uint8_t v___x_1557_; 
v___x_1557_ = lean_usize_dec_lt(v_i_1531_, v_sz_1530_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_b_1532_);
return v___x_1558_;
}
else
{
lean_object* v_a_1559_; 
v_a_1559_ = lean_array_uget_borrowed(v_as_1529_, v_i_1531_);
switch(lean_obj_tag(v_a_1559_))
{
case 0:
{
lean_object* v_stx_1560_; lean_object* v_toCold_1561_; lean_object* v_currRecDepth_1562_; lean_object* v_ref_1563_; uint16_t v_optionFlags_1564_; uint8_t v_suppressElabErrors_1565_; uint8_t v_isRecordingDeps_1566_; lean_object* v_ref_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_stx_1560_ = lean_ctor_get(v_a_1559_, 0);
v_toCold_1561_ = lean_ctor_get(v___y_1537_, 0);
v_currRecDepth_1562_ = lean_ctor_get(v___y_1537_, 1);
v_ref_1563_ = lean_ctor_get(v___y_1537_, 2);
v_optionFlags_1564_ = lean_ctor_get_uint16(v___y_1537_, sizeof(void*)*3);
v_suppressElabErrors_1565_ = lean_ctor_get_uint8(v___y_1537_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1566_ = lean_ctor_get_uint8(v___y_1537_, sizeof(void*)*3 + 3);
v_ref_1567_ = l_Lean_replaceRef(v_stx_1560_, v_ref_1563_);
lean_inc(v_currRecDepth_1562_);
lean_inc_ref(v_toCold_1561_);
v___x_1568_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1568_, 0, v_toCold_1561_);
lean_ctor_set(v___x_1568_, 1, v_currRecDepth_1562_);
lean_ctor_set(v___x_1568_, 2, v_ref_1567_);
lean_ctor_set_uint16(v___x_1568_, sizeof(void*)*3, v_optionFlags_1564_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*3 + 2, v_suppressElabErrors_1565_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*3 + 3, v_isRecordingDeps_1566_);
lean_inc(v_stx_1560_);
v___x_1569_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_1560_, v___x_1568_, v___y_1538_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; 
lean_dec_ref_known(v___x_1569_, 1);
lean_inc(v_stx_1560_);
v___x_1570_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_1560_, v___x_1568_, v___y_1538_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref_known(v___x_1570_, 1);
lean_inc(v_stx_1560_);
v___x_1571_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1560_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v_startTag_1573_; lean_object* v_children_x3f_1574_; lean_object* v_name_1575_; lean_object* v_attrs_1576_; lean_object* v___x_1577_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v_startTag_1573_ = lean_ctor_get(v_a_1572_, 0);
lean_inc_ref(v_startTag_1573_);
v_children_x3f_1574_ = lean_ctor_get(v_a_1572_, 1);
lean_inc(v_children_x3f_1574_);
lean_dec(v_a_1572_);
v_name_1575_ = lean_ctor_get(v_startTag_1573_, 1);
lean_inc(v_name_1575_);
v_attrs_1576_ = lean_ctor_get(v_startTag_1573_, 2);
lean_inc_ref(v_attrs_1576_);
lean_dec_ref(v_startTag_1573_);
v___x_1577_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_1575_);
lean_dec(v_name_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_attrs_1576_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___x_1568_, v___y_1538_);
lean_dec_ref(v_attrs_1576_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v_a_1588_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
if (lean_obj_tag(v_children_x3f_1574_) == 0)
{
lean_object* v___x_1593_; 
lean_dec_ref_known(v___x_1568_, 3);
v___x_1593_ = lean_box(0);
v_a_1588_ = v___x_1593_;
goto v___jp_1587_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1611_; 
v_val_1594_ = lean_ctor_get(v_children_x3f_1574_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_children_x3f_1574_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1596_ = v_children_x3f_1574_;
v_isShared_1597_ = v_isSharedCheck_1611_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v_children_x3f_1574_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1611_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_val_1594_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___x_1568_, v___y_1538_);
lean_dec_ref_known(v___x_1568_, 3);
lean_dec(v_val_1594_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_a_1599_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
v_a_1588_ = v___x_1601_;
goto v___jp_1587_;
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1596_);
lean_dec(v_a_1580_);
lean_dec(v_a_1578_);
lean_dec_ref(v_b_1532_);
v_a_1603_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1598_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1598_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
v___jp_1581_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_inc_ref(v___y_1582_);
v___x_1585_ = l_Lean_mkApp3(v___y_1582_, v___y_1583_, v_a_1580_, v___y_1584_);
v___x_1586_ = lean_array_push(v_b_1532_, v___x_1585_);
v_a_1541_ = v___x_1586_;
goto v___jp_1540_;
}
v___jp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1);
v___x_1590_ = l_Lean_mkStrLit(v_a_1578_);
if (lean_obj_tag(v_a_1588_) == 0)
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
v___y_1582_ = v___x_1589_;
v___y_1583_ = v___x_1590_;
v___y_1584_ = v___x_1591_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v_a_1588_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_a_1588_, 1);
v___y_1582_ = v___x_1589_;
v___y_1583_ = v___x_1590_;
v___y_1584_ = v_val_1592_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1578_);
lean_dec(v_children_x3f_1574_);
lean_dec_ref_known(v___x_1568_, 3);
lean_dec_ref(v_b_1532_);
v_a_1612_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1579_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1579_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_attrs_1576_);
lean_dec(v_children_x3f_1574_);
lean_dec_ref_known(v___x_1568_, 3);
lean_dec_ref(v_b_1532_);
v_a_1620_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1577_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1577_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref_known(v___x_1568_, 3);
lean_dec_ref(v_b_1532_);
v_a_1628_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1571_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1571_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref_known(v___x_1568_, 3);
lean_dec_ref(v_b_1532_);
v_a_1636_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1570_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1570_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref_known(v___x_1568_, 3);
lean_dec_ref(v_b_1532_);
v_a_1644_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1569_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1569_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
case 1:
{
lean_object* v_stx_1652_; lean_object* v_toCold_1653_; lean_object* v_currRecDepth_1654_; lean_object* v_ref_1655_; uint16_t v_optionFlags_1656_; uint8_t v_suppressElabErrors_1657_; uint8_t v_isRecordingDeps_1658_; lean_object* v___x_1659_; lean_object* v_ref_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_stx_1652_ = lean_ctor_get(v_a_1559_, 0);
v_toCold_1653_ = lean_ctor_get(v___y_1537_, 0);
v_currRecDepth_1654_ = lean_ctor_get(v___y_1537_, 1);
v_ref_1655_ = lean_ctor_get(v___y_1537_, 2);
v_optionFlags_1656_ = lean_ctor_get_uint16(v___y_1537_, sizeof(void*)*3);
v_suppressElabErrors_1657_ = lean_ctor_get_uint8(v___y_1537_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1658_ = lean_ctor_get_uint8(v___y_1537_, sizeof(void*)*3 + 3);
lean_inc_ref(v_stx_1652_);
v___x_1659_ = l_Lean_Html_Syntax_TextCommentsView_getSyntax(v_stx_1652_);
v_ref_1660_ = l_Lean_replaceRef(v___x_1659_, v_ref_1655_);
lean_dec(v___x_1659_);
lean_inc(v_currRecDepth_1654_);
lean_inc_ref(v_toCold_1653_);
v___x_1661_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1661_, 0, v_toCold_1653_);
lean_ctor_set(v___x_1661_, 1, v_currRecDepth_1654_);
lean_ctor_set(v___x_1661_, 2, v_ref_1660_);
lean_ctor_set_uint16(v___x_1661_, sizeof(void*)*3, v_optionFlags_1656_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*3 + 2, v_suppressElabErrors_1657_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*3 + 3, v_isRecordingDeps_1658_);
v___x_1662_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_stx_1652_, v___x_1661_, v___y_1538_);
lean_dec_ref_known(v___x_1661_, 3);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v___x_1664_ = lean_string_utf8_byte_size(v_a_1663_);
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_nat_dec_eq(v___x_1664_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1667_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3);
v___x_1668_ = l_Lean_mkStrLit(v_a_1663_);
v___x_1669_ = l_Lean_Expr_app___override(v___x_1667_, v___x_1668_);
v___x_1670_ = lean_array_push(v_b_1532_, v___x_1669_);
v_a_1541_ = v___x_1670_;
goto v___jp_1540_;
}
else
{
lean_dec(v_a_1663_);
v_a_1541_ = v_b_1532_;
goto v___jp_1540_;
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v_b_1532_);
v_a_1671_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1662_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1662_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
default: 
{
uint8_t v_isMany_1679_; lean_object* v_stx_1680_; lean_object* v_toCold_1681_; lean_object* v_currRecDepth_1682_; lean_object* v_ref_1683_; uint16_t v_optionFlags_1684_; uint8_t v_suppressElabErrors_1685_; uint8_t v_isRecordingDeps_1686_; lean_object* v_ref_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_isMany_1679_ = lean_ctor_get_uint8(v_a_1559_, sizeof(void*)*1);
v_stx_1680_ = lean_ctor_get(v_a_1559_, 0);
v_toCold_1681_ = lean_ctor_get(v___y_1537_, 0);
v_currRecDepth_1682_ = lean_ctor_get(v___y_1537_, 1);
v_ref_1683_ = lean_ctor_get(v___y_1537_, 2);
v_optionFlags_1684_ = lean_ctor_get_uint16(v___y_1537_, sizeof(void*)*3);
v_suppressElabErrors_1685_ = lean_ctor_get_uint8(v___y_1537_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1686_ = lean_ctor_get_uint8(v___y_1537_, sizeof(void*)*3 + 3);
v_ref_1687_ = l_Lean_replaceRef(v_stx_1680_, v_ref_1683_);
lean_inc(v_ref_1687_);
lean_inc(v_currRecDepth_1682_);
lean_inc_ref(v_toCold_1681_);
v___x_1688_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1688_, 0, v_toCold_1681_);
lean_ctor_set(v___x_1688_, 1, v_currRecDepth_1682_);
lean_ctor_set(v___x_1688_, 2, v_ref_1687_);
lean_ctor_set_uint16(v___x_1688_, sizeof(void*)*3, v_optionFlags_1684_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*3 + 2, v_suppressElabErrors_1685_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*3 + 3, v_isRecordingDeps_1686_);
lean_inc(v_stx_1680_);
v___x_1689_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_1679_, v_stx_1680_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___x_1688_, v___y_1538_);
if (lean_obj_tag(v___x_1689_) == 0)
{
if (v_isMany_1679_ == 0)
{
lean_object* v_a_1690_; lean_object* v_term_1691_; lean_object* v___x_1692_; 
lean_dec(v_ref_1687_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v_term_1691_ = lean_ctor_get(v_a_1690_, 1);
lean_inc(v_term_1691_);
lean_dec(v_a_1690_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1557_, v_b_1532_, v_term_1691_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___x_1688_, v___y_1538_);
lean_dec_ref_known(v___x_1688_, 3);
v___y_1546_ = v___x_1692_;
goto v___jp_1545_;
}
else
{
lean_object* v_a_1693_; lean_object* v_quotContext_1694_; lean_object* v_currMacroScope_1695_; lean_object* v_term_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1693_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1689_, 1);
v_quotContext_1694_ = lean_ctor_get(v_toCold_1681_, 8);
v_currMacroScope_1695_ = lean_ctor_get(v_toCold_1681_, 9);
v_term_1696_ = lean_ctor_get(v_a_1693_, 1);
lean_inc(v_term_1696_);
lean_dec(v_a_1693_);
v___x_1697_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5));
v___x_1699_ = 0;
v___x_1700_ = l_Lean_SourceInfo_fromRef(v_ref_1687_, v___x_1699_);
lean_dec(v_ref_1687_);
v___x_1701_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7);
lean_inc(v_currMacroScope_1695_);
lean_inc(v_quotContext_1694_);
v___x_1702_ = l_Lean_addMacroScope(v_quotContext_1694_, v___x_1698_, v_currMacroScope_1695_);
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10));
lean_inc_n(v___x_1700_, 2);
v___x_1704_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1700_);
lean_ctor_set(v___x_1704_, 1, v___x_1701_);
lean_ctor_set(v___x_1704_, 2, v___x_1702_);
lean_ctor_set(v___x_1704_, 3, v___x_1703_);
v___x_1705_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1706_ = l_Lean_Syntax_node1(v___x_1700_, v___x_1705_, v_term_1696_);
v___x_1707_ = l_Lean_Syntax_node2(v___x_1700_, v___x_1697_, v___x_1704_, v___x_1706_);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1557_, v_b_1532_, v___x_1707_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___x_1688_, v___y_1538_);
lean_dec_ref_known(v___x_1688_, 3);
v___y_1546_ = v___x_1708_;
goto v___jp_1545_;
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref_known(v___x_1688_, 3);
lean_dec(v_ref_1687_);
lean_dec_ref(v_b_1532_);
v_a_1709_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1689_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1689_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
v___jp_1540_:
{
size_t v___x_1542_; size_t v___x_1543_; 
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_add(v_i_1531_, v___x_1542_);
v_i_1531_ = v___x_1543_;
v_b_1532_ = v_a_1541_;
goto _start;
}
v___jp_1545_:
{
if (lean_obj_tag(v___y_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_snd_1548_; 
v_a_1547_ = lean_ctor_get(v___y_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___y_1546_, 1);
v_snd_1548_ = lean_ctor_get(v_a_1547_, 1);
lean_inc(v_snd_1548_);
lean_dec(v_a_1547_);
v_a_1541_ = v_snd_1548_;
goto v___jp_1540_;
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___y_1546_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___y_1546_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___y_1546_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___y_1546_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(lean_object* v_stx_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_toCold_1725_; lean_object* v_currRecDepth_1726_; lean_object* v_ref_1727_; uint16_t v_optionFlags_1728_; uint8_t v_suppressElabErrors_1729_; uint8_t v_isRecordingDeps_1730_; lean_object* v___x_1731_; lean_object* v_es_1732_; lean_object* v_ref_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_toCold_1725_ = lean_ctor_get(v_a_1722_, 0);
v_currRecDepth_1726_ = lean_ctor_get(v_a_1722_, 1);
v_ref_1727_ = lean_ctor_get(v_a_1722_, 2);
v_optionFlags_1728_ = lean_ctor_get_uint16(v_a_1722_, sizeof(void*)*3);
v_suppressElabErrors_1729_ = lean_ctor_get_uint8(v_a_1722_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1730_ = lean_ctor_get_uint8(v_a_1722_, sizeof(void*)*3 + 3);
v___x_1731_ = lean_unsigned_to_nat(0u);
v_es_1732_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0));
v_ref_1733_ = l_Lean_replaceRef(v_stx_1717_, v_ref_1727_);
lean_inc(v_currRecDepth_1726_);
lean_inc_ref(v_toCold_1725_);
v___x_1734_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1734_, 0, v_toCold_1725_);
lean_ctor_set(v___x_1734_, 1, v_currRecDepth_1726_);
lean_ctor_set(v___x_1734_, 2, v_ref_1733_);
lean_ctor_set_uint16(v___x_1734_, sizeof(void*)*3, v_optionFlags_1728_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*3 + 2, v_suppressElabErrors_1729_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*3 + 3, v_isRecordingDeps_1730_);
v___x_1735_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_stx_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v___x_1734_, v_a_1723_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; size_t v_sz_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v_sz_1737_ = lean_array_size(v_a_1736_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_a_1736_, v_sz_1737_, v___x_1738_, v_es_1732_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v___x_1734_, v_a_1723_);
lean_dec(v_a_1736_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1763_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1763_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1763_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = lean_array_get_size(v_a_1740_);
v___x_1745_ = lean_nat_dec_eq(v___x_1744_, v___x_1731_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_del_object(v___x_1742_);
v___x_1746_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1747_ = lean_array_to_list(v_a_1740_);
v___x_1748_ = l_Lean_Meta_mkArrayLit(v___x_1746_, v___x_1747_, v_a_1720_, v_a_1721_, v___x_1734_, v_a_1723_);
lean_dec_ref_known(v___x_1734_, 3);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1758_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1753_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3);
v___x_1754_ = l_Lean_Expr_app___override(v___x_1753_, v_a_1749_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1754_);
v___x_1756_ = v___x_1751_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
return v___x_1748_;
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec(v_a_1740_);
lean_dec_ref_known(v___x_1734_, 3);
v___x_1759_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1759_);
v___x_1761_ = v___x_1742_;
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
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref_known(v___x_1734_, 3);
v_a_1764_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1739_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1739_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref_known(v___x_1734_, 3);
v_a_1772_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1735_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1735_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___boxed(lean_object* v_stx_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_stx_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_stx_1780_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___boxed(lean_object* v_as_1789_, lean_object* v_sz_1790_, lean_object* v_i_1791_, lean_object* v_b_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1790_);
lean_dec(v_sz_1790_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1791_);
lean_dec(v_i_1791_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_as_1789_, v_sz_boxed_1800_, v_i_boxed_1801_, v_b_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v_as_1789_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(lean_object* v_stx_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1803_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___boxed(lean_object* v_stx_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(v_stx_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg___boxed(lean_object* v_a_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(v_a_1824_);
lean_dec(v_a_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(lean_object* v_a_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1827_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___boxed(lean_object* v_a_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(v_a_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v_a_1836_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(lean_object* v_stx_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1));
lean_inc(v_stx_1857_);
v___x_1866_ = l_Lean_Syntax_isOfKind(v_stx_1857_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec(v_stx_1857_);
v___x_1867_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v_h_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1868_ = lean_unsigned_to_nat(2u);
v_h_1869_ = l_Lean_Syntax_getArg(v_stx_1857_, v___x_1868_);
lean_dec(v_stx_1857_);
v___x_1870_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3));
lean_inc(v_h_1869_);
v___x_1871_ = l_Lean_Syntax_isOfKind(v_h_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec(v_h_1869_);
v___x_1872_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; 
v___x_1873_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_h_1869_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_h_1869_);
return v___x_1873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___boxed(lean_object* v_stx_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(lean_object* v_stx_1883_, lean_object* v_x_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1883_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___boxed(lean_object* v_stx_1893_, lean_object* v_x_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(v_stx_1893_, v_x_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_x_1894_);
return v_res_1902_;
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
