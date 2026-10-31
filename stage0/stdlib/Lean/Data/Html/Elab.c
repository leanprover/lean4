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
lean_object* v_toCold_176_; lean_object* v_currRecDepth_177_; lean_object* v_ref_178_; uint16_t v_optionFlags_179_; uint8_t v_suppressElabErrors_180_; uint8_t v_checkDeprecated_181_; uint8_t v_isRecordingDeps_182_; lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_toCold_176_ = lean_ctor_get(v___y_173_, 0);
v_currRecDepth_177_ = lean_ctor_get(v___y_173_, 1);
v_ref_178_ = lean_ctor_get(v___y_173_, 2);
v_optionFlags_179_ = lean_ctor_get_uint16(v___y_173_, sizeof(void*)*3);
v_suppressElabErrors_180_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*3 + 2);
v_checkDeprecated_181_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*3 + 3);
v_isRecordingDeps_182_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*3 + 4);
v_ref_183_ = l_Lean_replaceRef(v_ref_171_, v_ref_178_);
lean_inc(v_currRecDepth_177_);
lean_inc_ref(v_toCold_176_);
v___x_184_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_184_, 0, v_toCold_176_);
lean_ctor_set(v___x_184_, 1, v_currRecDepth_177_);
lean_ctor_set(v___x_184_, 2, v_ref_183_);
lean_ctor_set_uint16(v___x_184_, sizeof(void*)*3, v_optionFlags_179_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 2, v_suppressElabErrors_180_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 3, v_checkDeprecated_181_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 4, v_isRecordingDeps_182_);
v___x_185_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_172_, v___x_184_, v___y_174_);
lean_dec_ref_known(v___x_184_, 3);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg___boxed(lean_object* v_ref_186_, lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_ref_186_, v_msg_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v_ref_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(lean_object* v_x_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
if (lean_obj_tag(v_x_192_) == 1)
{
lean_object* v_args_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_args_196_ = lean_ctor_get(v_x_192_, 2);
v___x_197_ = lean_array_get_size(v_args_196_);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_array_fget_borrowed(v_args_196_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 2)
{
lean_object* v_val_203_; lean_object* v___x_204_; 
v_val_203_ = lean_ctor_get(v___x_202_, 1);
lean_inc_ref(v_val_203_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_val_203_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_205_;
}
}
}
else
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg___boxed(lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_x_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v_x_207_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(lean_object* v_a_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_a_212_, v___y_213_, v___y_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1___boxed(lean_object* v_a_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1(v_a_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v_a_217_);
return v_res_221_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__0));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__2));
v___x_227_ = l_Lean_stringToMessageData(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__4));
v___x_230_ = l_Lean_stringToMessageData(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNamesMatch___closed__6));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch(lean_object* v_stx_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0(v_stx_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_321_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_321_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_321_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_321_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_endTag_x3f_243_; 
v_endTag_x3f_243_ = lean_ctor_get(v_a_239_, 2);
lean_inc(v_endTag_x3f_243_);
if (lean_obj_tag(v_endTag_x3f_243_) == 1)
{
lean_object* v_startTag_244_; lean_object* v_val_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_316_; 
lean_del_object(v___x_241_);
v_startTag_244_ = lean_ctor_get(v_a_239_, 0);
lean_inc_ref(v_startTag_244_);
lean_dec(v_a_239_);
v_val_245_ = lean_ctor_get(v_endTag_x3f_243_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_endTag_x3f_243_);
if (v_isSharedCheck_316_ == 0)
{
v___x_247_ = v_endTag_x3f_243_;
v_isShared_248_ = v_isSharedCheck_316_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_val_245_);
lean_dec(v_endTag_x3f_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_316_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_name_249_; lean_object* v___x_250_; 
v_name_249_ = lean_ctor_get(v_startTag_244_, 1);
lean_inc(v_name_249_);
lean_dec_ref(v_startTag_244_);
v___x_250_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_249_, v_a_235_, v_a_236_);
lean_dec(v_name_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v_name_252_; lean_object* v___x_253_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v_name_252_ = lean_ctor_get(v_val_245_, 1);
lean_inc(v_name_252_);
lean_dec(v_val_245_);
v___x_253_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_name_252_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_299_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_299_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_299_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_299_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_258_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_254_);
v___x_259_ = l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(v_a_254_, v___x_258_);
lean_inc(v_a_251_);
v___x_260_ = l_String_mapAux___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__2(v_a_251_, v___x_258_);
v___x_261_ = lean_string_dec_eq(v___x_259_, v___x_260_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_259_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_del_object(v___x_256_);
v___x_262_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__1);
lean_inc(v_a_251_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_a_251_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
lean_ctor_set(v___x_265_, 2, v___x_264_);
lean_ctor_set(v___x_265_, 3, v___x_264_);
lean_ctor_set(v___x_265_, 4, v___x_264_);
lean_ctor_set(v___x_265_, 5, v___x_264_);
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_264_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*3, v___x_266_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_mk_empty_array_with_capacity(v___x_268_);
v___x_270_ = lean_array_push(v___x_269_, v___x_267_);
lean_inc(v_name_252_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_name_252_);
v___x_272_ = v___x_247_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_name_252_);
v___x_272_ = v_reuseFailAlloc_294_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_MessageData_hint(v___x_262_, v___x_270_, v___x_272_, v___x_264_, v___x_261_, v_a_235_, v_a_236_);
lean_dec_ref(v___x_270_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v___x_275_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__3);
v___x_276_ = l_Lean_stringToMessageData(v_a_251_);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__5);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_stringToMessageData(v_a_254_);
v___x_281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_obj_once(&l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7, &l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7_once, _init_l_Lean_Html_Syntax_Element_checkNamesMatch___closed__7);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_a_274_);
v___x_285_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_name_252_, v___x_284_, v_a_235_, v_a_236_);
lean_dec(v_name_252_);
return v___x_285_;
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec(v_a_254_);
lean_dec(v_name_252_);
lean_dec(v_a_251_);
v_a_286_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_273_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_273_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_297_; 
lean_dec(v_a_254_);
lean_dec(v_name_252_);
lean_dec(v_a_251_);
lean_del_object(v___x_247_);
v___x_295_ = lean_box(0);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_295_);
v___x_297_ = v___x_256_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_name_252_);
lean_dec(v_a_251_);
lean_del_object(v___x_247_);
v_a_300_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_253_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_253_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
v_a_308_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_250_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_250_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_dec(v_endTag_x3f_243_);
lean_dec(v_a_239_);
v___x_317_ = lean_box(0);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_317_);
v___x_319_ = v___x_241_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_238_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_238_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNamesMatch___boxed(lean_object* v_stx_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(lean_object* v_00_u03b1_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg();
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b1_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0(v_00_u03b1_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(lean_object* v_00_u03b1_345_, lean_object* v_ref_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___redArg(v_ref_346_, v_msg_347_, v___y_348_, v___y_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3___boxed(lean_object* v_00_u03b1_352_, lean_object* v_ref_353_, lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3(v_00_u03b1_352_, v_ref_353_, v_msg_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v_ref_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3(lean_object* v_k_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___redArg(v_x_360_, v___y_361_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3___boxed(lean_object* v_k_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_TagName_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__1_spec__3(v_k_365_, v_x_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v_x_366_);
lean_dec(v_k_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6(lean_object* v_00_u03b1_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__3_spec__6___redArg(v_msg_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
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
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren(lean_object* v_stx_398_, lean_object* v_a_399_, lean_object* v_a_400_){
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
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_checkNoVoidChildren___boxed(lean_object* v_stx_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__0___redArg___closed__0);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg___boxed(lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(uint8_t v_isMany_522_, lean_object* v_stx_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; lean_object* v___y_533_; 
lean_inc(v_stx_523_);
v___x_531_ = l_Lean_Syntax_getKind(v_stx_523_);
if (v_isMany_522_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___y_533_ = v___x_544_;
goto v___jp_532_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___y_533_ = v___x_545_;
goto v___jp_532_;
}
v___jp_532_:
{
uint8_t v___x_534_; 
v___x_534_ = lean_name_eq(v___x_531_, v___y_533_);
lean_dec(v___x_531_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec(v_stx_523_);
v___x_535_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_535_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = l_Lean_Syntax_getArg(v_stx_523_, v___x_536_);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = l_Lean_Syntax_getArg(v_stx_523_, v___x_538_);
v___x_540_ = lean_unsigned_to_nat(2u);
v___x_541_ = l_Lean_Syntax_getArg(v_stx_523_, v___x_540_);
lean_dec(v_stx_523_);
v___x_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_542_, 0, v___x_537_);
lean_ctor_set(v___x_542_, 1, v___x_539_);
lean_ctor_set(v___x_542_, 2, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___boxed(lean_object* v_isMany_546_, lean_object* v_stx_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v_isMany_boxed_555_; lean_object* v_res_556_; 
v_isMany_boxed_555_ = lean_unbox(v_isMany_546_);
v_res_556_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_boxed_555_, v_stx_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(lean_object* v_stx_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; lean_object* v_c_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v_c_569_ = l_Lean_Syntax_getArg(v_stx_560_, v___x_568_);
lean_inc(v_c_569_);
v___x_570_ = l_Lean_Syntax_getKind(v_c_569_);
v___x_571_ = ((lean_object*)(l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___closed__1));
v___x_572_ = lean_name_eq(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_574_ = lean_name_eq(v___x_570_, v___x_573_);
lean_dec(v___x_570_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v_c_569_);
v___x_575_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v_c_569_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_570_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_c_569_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0___boxed(lean_object* v_stx_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v_stx_580_);
return v_res_588_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_box(0);
v___x_593_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_594_ = l_Lean_Expr_const___override(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(lean_object* v_stx_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_toCold_605_; lean_object* v_currRecDepth_606_; lean_object* v_ref_607_; uint16_t v_optionFlags_608_; uint8_t v_suppressElabErrors_609_; uint8_t v_checkDeprecated_610_; uint8_t v_isRecordingDeps_611_; lean_object* v_ref_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_toCold_605_ = lean_ctor_get(v_a_602_, 0);
v_currRecDepth_606_ = lean_ctor_get(v_a_602_, 1);
v_ref_607_ = lean_ctor_get(v_a_602_, 2);
v_optionFlags_608_ = lean_ctor_get_uint16(v_a_602_, sizeof(void*)*3);
v_suppressElabErrors_609_ = lean_ctor_get_uint8(v_a_602_, sizeof(void*)*3 + 2);
v_checkDeprecated_610_ = lean_ctor_get_uint8(v_a_602_, sizeof(void*)*3 + 3);
v_isRecordingDeps_611_ = lean_ctor_get_uint8(v_a_602_, sizeof(void*)*3 + 4);
v_ref_612_ = l_Lean_replaceRef(v_stx_597_, v_ref_607_);
lean_inc(v_currRecDepth_606_);
lean_inc_ref(v_toCold_605_);
v___x_613_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_613_, 0, v_toCold_605_);
lean_ctor_set(v___x_613_, 1, v_currRecDepth_606_);
lean_ctor_set(v___x_613_, 2, v_ref_612_);
lean_ctor_set_uint16(v___x_613_, sizeof(void*)*3, v_optionFlags_608_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 2, v_suppressElabErrors_609_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 3, v_checkDeprecated_610_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 4, v_isRecordingDeps_611_);
v___x_614_ = l_Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0(v_stx_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v___x_613_, v_a_603_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
if (lean_obj_tag(v_a_615_) == 0)
{
lean_object* v_stx_616_; lean_object* v___x_617_; 
v_stx_616_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_stx_616_);
lean_dec_ref_known(v_a_615_, 1);
v___x_617_ = l_Lean_Html_Syntax_decodeCharacterReferences(v_stx_616_, v___x_613_, v_a_603_);
lean_dec_ref_known(v___x_613_, 3);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_626_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = l_Lean_mkStrLit(v_a_618_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_617_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v_stx_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
v_stx_635_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_stx_635_);
lean_dec_ref_known(v_a_615_, 1);
v___x_636_ = 0;
v___x_637_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v___x_636_, v_stx_635_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v___x_613_, v_a_603_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v_term_639_; lean_object* v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v_term_639_ = lean_ctor_get(v_a_638_, 1);
lean_inc(v_term_639_);
lean_dec(v_a_638_);
v___x_640_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__3);
v___x_641_ = 1;
v___x_642_ = lean_box(0);
v___x_643_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_639_, v___x_640_, v___x_641_, v___x_641_, v___x_642_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v___x_613_, v_a_603_);
lean_dec_ref_known(v___x_613_, 3);
return v___x_643_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref_known(v___x_613_, 3);
v_a_644_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_637_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_637_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref_known(v___x_613_, 3);
v_a_652_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_614_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_614_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___boxed(lean_object* v_stx_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_stx_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_stx_660_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(lean_object* v_00_u03b1_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___boxed(lean_object* v_00_u03b1_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0(v_00_u03b1_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(lean_object* v_stx_693_){
_start:
{
lean_object* v___x_695_; lean_object* v_c_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_695_ = lean_unsigned_to_nat(0u);
v_c_696_ = l_Lean_Syntax_getArg(v_stx_693_, v___x_695_);
lean_inc(v_c_696_);
v___x_697_ = l_Lean_Syntax_getKind(v_c_696_);
v___x_698_ = ((lean_object*)(l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___closed__1));
v___x_699_ = lean_name_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_701_ = lean_name_eq(v___x_697_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_703_ = lean_name_eq(v___x_697_, v___x_702_);
lean_dec(v___x_697_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
lean_dec(v_c_696_);
v___x_704_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_705_, 0, v_c_696_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_701_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v___x_697_);
v___x_707_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_707_, 0, v_c_696_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v___x_701_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
else
{
lean_object* v___x_709_; lean_object* v_val_x3f_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
lean_dec(v___x_697_);
v___x_709_ = lean_unsigned_to_nat(1u);
v_val_x3f_710_ = l_Lean_Syntax_getArg(v_stx_693_, v___x_709_);
v___x_711_ = l_Lean_Syntax_getNumArgs(v_val_x3f_710_);
v___x_712_ = lean_nat_dec_eq(v___x_711_, v___x_695_);
lean_dec(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_713_ = l_Lean_Syntax_getArg(v_val_x3f_710_, v___x_695_);
v___x_714_ = l_Lean_Syntax_getArg(v_val_x3f_710_, v___x_709_);
lean_dec(v_val_x3f_710_);
v___x_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_715_, 0, v_c_696_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_714_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v_val_x3f_710_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v_c_696_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg___boxed(lean_object* v_stx_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_720_);
lean_dec(v_stx_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_723_) == 1)
{
lean_object* v_args_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_args_725_ = lean_ctor_get(v_x_723_, 2);
v___x_726_ = lean_array_get_size(v_args_725_);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_dec_eq(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = lean_array_fget_borrowed(v_args_725_, v___x_730_);
if (lean_obj_tag(v___x_731_) == 2)
{
lean_object* v_val_732_; lean_object* v___x_733_; 
v_val_732_ = lean_ctor_get(v___x_731_, 1);
lean_inc_ref(v_val_732_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_val_732_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_734_;
}
}
}
else
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg___boxed(lean_object* v_x_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_736_);
lean_dec(v_x_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(lean_object* v_a_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_739_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1___boxed(lean_object* v_a_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1(v_a_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v_a_748_);
return v_res_756_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = l_Lean_Level_ofNat(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_box(0);
v___x_763_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_762_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_766_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__2);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_769_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__1));
v___x_770_ = l_Lean_Expr_const___override(v___x_769_, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6(void){
_start:
{
lean_object* v_strType_771_; lean_object* v___x_772_; lean_object* v_pairType_773_; 
v_strType_771_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v___x_772_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__5);
v_pairType_773_ = l_Lean_mkAppB(v___x_772_, v_strType_771_, v_strType_771_);
return v_pairType_773_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_778_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__8));
v___x_779_ = l_Lean_Expr_const___override(v___x_778_, v___x_777_);
return v___x_779_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10(void){
_start:
{
lean_object* v_pairType_780_; lean_object* v___x_781_; lean_object* v_arrayType_782_; 
v_pairType_780_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_781_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__9);
v_arrayType_782_ = l_Lean_Expr_app___override(v___x_781_, v_pairType_780_);
return v_arrayType_782_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__4);
v___x_788_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__12));
v___x_789_ = l_Lean_Expr_const___override(v___x_788_, v___x_787_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Html_Syntax_Element_checkNoVoidChildren___closed__8));
v___x_791_ = l_Lean_mkStrLit(v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15(void){
_start:
{
lean_object* v_pairType_792_; lean_object* v___x_793_; 
v_pairType_792_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v_pairType_792_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__20));
v___x_804_ = l_String_toRawSubstring_x27(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__30));
v___x_825_ = l_String_toRawSubstring_x27(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__0));
v___x_833_ = l_String_toRawSubstring_x27(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47(void){
_start:
{
lean_object* v_arrayType_856_; lean_object* v___x_857_; 
v_arrayType_856_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__10);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_arrayType_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(lean_object* v_stx_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_strType_868_; lean_object* v_toCold_869_; lean_object* v_currRecDepth_870_; lean_object* v_ref_871_; uint16_t v_optionFlags_872_; uint8_t v_suppressElabErrors_873_; uint8_t v_checkDeprecated_874_; uint8_t v_isRecordingDeps_875_; lean_object* v_ref_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__1));
v___x_867_ = lean_box(0);
v_strType_868_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal___closed__2);
v_toCold_869_ = lean_ctor_get(v_a_863_, 0);
v_currRecDepth_870_ = lean_ctor_get(v_a_863_, 1);
v_ref_871_ = lean_ctor_get(v_a_863_, 2);
v_optionFlags_872_ = lean_ctor_get_uint16(v_a_863_, sizeof(void*)*3);
v_suppressElabErrors_873_ = lean_ctor_get_uint8(v_a_863_, sizeof(void*)*3 + 2);
v_checkDeprecated_874_ = lean_ctor_get_uint8(v_a_863_, sizeof(void*)*3 + 3);
v_isRecordingDeps_875_ = lean_ctor_get_uint8(v_a_863_, sizeof(void*)*3 + 4);
v_ref_876_ = l_Lean_replaceRef(v_stx_858_, v_ref_871_);
lean_inc(v_ref_876_);
lean_inc(v_currRecDepth_870_);
lean_inc_ref(v_toCold_869_);
v___x_877_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_877_, 0, v_toCold_869_);
lean_ctor_set(v___x_877_, 1, v_currRecDepth_870_);
lean_ctor_set(v___x_877_, 2, v_ref_876_);
lean_ctor_set_uint16(v___x_877_, sizeof(void*)*3, v_optionFlags_872_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 2, v_suppressElabErrors_873_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 3, v_checkDeprecated_874_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 4, v_isRecordingDeps_875_);
v___x_878_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_858_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
switch(lean_obj_tag(v_a_879_))
{
case 0:
{
lean_object* v_stx_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_ref_876_);
v_stx_880_ = lean_ctor_get(v_a_879_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_919_ == 0)
{
v___x_882_ = v_a_879_;
v_isShared_883_ = v_isSharedCheck_919_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_stx_880_);
lean_dec(v_a_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_919_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_name_884_; lean_object* v_val_885_; lean_object* v___x_886_; 
v_name_884_ = lean_ctor_get(v_stx_880_, 0);
lean_inc(v_name_884_);
v_val_885_ = lean_ctor_get(v_stx_880_, 2);
lean_inc(v_val_885_);
lean_dec_ref(v_stx_880_);
v___x_886_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_name_884_);
lean_dec(v_name_884_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal(v_val_885_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v___x_877_, v_a_864_);
lean_dec_ref_known(v___x_877_, 3);
lean_dec(v_val_885_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_902_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_902_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_902_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_902_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_894_ = l_Lean_mkStrLit(v_a_887_);
v___x_895_ = l_Lean_mkApp4(v___x_893_, v_strType_868_, v_strType_868_, v___x_894_, v_a_889_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_895_);
v___x_897_ = v___x_882_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_897_);
v___x_899_ = v___x_891_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_887_);
lean_del_object(v___x_882_);
v_a_903_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_888_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_888_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_val_885_);
lean_del_object(v___x_882_);
lean_dec_ref_known(v___x_877_, 3);
v_a_911_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_886_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_886_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
case 1:
{
lean_object* v_stx_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref_known(v___x_877_, 3);
lean_dec(v_ref_876_);
v_stx_920_ = lean_ctor_get(v_a_879_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_948_ == 0)
{
v___x_922_ = v_a_879_;
v_isShared_923_ = v_isSharedCheck_948_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_stx_920_);
lean_dec(v_a_879_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_948_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_stx_920_);
lean_dec(v_stx_920_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_939_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_939_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_929_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__13);
v___x_930_ = l_Lean_mkStrLit(v_a_925_);
v___x_931_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__14);
v___x_932_ = l_Lean_mkApp4(v___x_929_, v_strType_868_, v_strType_868_, v___x_930_, v___x_931_);
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 0);
lean_ctor_set(v___x_922_, 0, v___x_932_);
v___x_934_ = v___x_922_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_934_);
v___x_936_ = v___x_927_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_del_object(v___x_922_);
v_a_940_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_924_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_924_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
default: 
{
uint8_t v_isMany_949_; 
v_isMany_949_ = lean_ctor_get_uint8(v_a_879_, sizeof(void*)*1);
if (v_isMany_949_ == 0)
{
lean_object* v_stx_950_; lean_object* v___x_951_; 
lean_dec(v_ref_876_);
v_stx_950_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_stx_950_);
lean_dec_ref_known(v_a_879_, 1);
v___x_951_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_949_, v_stx_950_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v___x_877_, v_a_864_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_term_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v_term_953_ = lean_ctor_get(v_a_952_, 1);
lean_inc(v_term_953_);
lean_dec(v_a_952_);
v___x_954_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__15);
v___x_955_ = 1;
v___x_956_ = lean_box(0);
v___x_957_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_953_, v___x_954_, v___x_955_, v___x_955_, v___x_956_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v___x_877_, v_a_864_);
lean_dec_ref_known(v___x_877_, 3);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_a_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_957_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_957_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref_known(v___x_877_, 3);
v_a_975_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_951_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_951_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_stx_983_; lean_object* v___x_984_; 
v_stx_983_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_stx_983_);
lean_dec_ref_known(v_a_879_, 1);
v___x_984_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_949_, v_stx_983_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v___x_877_, v_a_864_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_quotContext_986_; lean_object* v_currMacroScope_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_term_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v_quotContext_986_ = lean_ctor_get(v_toCold_869_, 8);
v_currMacroScope_987_ = lean_ctor_get(v_toCold_869_, 9);
v___x_988_ = 0;
v___x_989_ = l_Lean_SourceInfo_fromRef(v_ref_876_, v___x_988_);
lean_dec(v_ref_876_);
v___x_990_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_991_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__21);
v___x_992_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__24));
lean_inc_n(v_currMacroScope_987_, 3);
lean_inc_n(v_quotContext_986_, 3);
v___x_993_ = l_Lean_addMacroScope(v_quotContext_986_, v___x_992_, v_currMacroScope_987_);
v___x_994_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__26));
lean_inc_n(v___x_989_, 10);
v___x_995_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_995_, 0, v___x_989_);
lean_ctor_set(v___x_995_, 1, v___x_991_);
lean_ctor_set(v___x_995_, 2, v___x_993_);
lean_ctor_set(v___x_995_, 3, v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__28));
v___x_997_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__29));
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_989_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__31);
v___x_1000_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__32));
v___x_1001_ = l_Lean_addMacroScope(v_quotContext_986_, v___x_1000_, v_currMacroScope_987_);
v___x_1002_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1002_, 0, v___x_989_);
lean_ctor_set(v___x_1002_, 1, v___x_999_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
lean_ctor_set(v___x_1002_, 3, v___x_867_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__33));
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_989_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__35));
v___x_1006_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__36);
v___x_1007_ = l_Lean_addMacroScope(v_quotContext_986_, v___x_866_, v_currMacroScope_987_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__42));
v___x_1009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1009_, 0, v___x_989_);
lean_ctor_set(v___x_1009_, 1, v___x_1006_);
lean_ctor_set(v___x_1009_, 2, v___x_1007_);
lean_ctor_set(v___x_1009_, 3, v___x_1008_);
v___x_1010_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__43));
v___x_1011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_989_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
lean_inc_ref(v___x_1009_);
v___x_1012_ = l_Lean_Syntax_node3(v___x_989_, v___x_1005_, v___x_1009_, v___x_1011_, v___x_1009_);
v_term_1013_ = lean_ctor_get(v_a_985_, 1);
lean_inc(v_term_1013_);
lean_dec(v_a_985_);
v___x_1014_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__44));
v___x_1015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_989_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1017_ = l_Lean_Syntax_node5(v___x_989_, v___x_996_, v___x_998_, v___x_1002_, v___x_1004_, v___x_1012_, v___x_1015_);
v___x_1018_ = l_Lean_Syntax_node2(v___x_989_, v___x_1016_, v___x_1017_, v_term_1013_);
v___x_1019_ = l_Lean_Syntax_node2(v___x_989_, v___x_990_, v___x_995_, v___x_1018_);
v___x_1020_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__47);
v___x_1021_ = lean_box(0);
v___x_1022_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1019_, v___x_1020_, v_isMany_949_, v_isMany_949_, v___x_1021_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v___x_877_, v_a_864_);
lean_dec_ref_known(v___x_877_, 3);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1022_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1022_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref_known(v___x_877_, 3);
lean_dec(v_ref_876_);
v_a_1040_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_984_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_984_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref_known(v___x_877_, 3);
lean_dec(v_ref_876_);
v_a_1048_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_878_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_878_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___boxed(lean_object* v_stx_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_stx_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_stx_1056_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(lean_object* v_stx_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___redArg(v_stx_1065_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0___boxed(lean_object* v_stx_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Html_Syntax_Attr_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__0(v_stx_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_stx_1074_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(lean_object* v_k_1083_, lean_object* v_x_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_x_1084_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___boxed(lean_object* v_k_1093_, lean_object* v_x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1(v_k_1093_, v_x_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v_x_1094_);
lean_dec(v_k_1093_);
return v_res_1102_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__1));
v___x_1109_ = l_Lean_Expr_const___override(v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__3);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__4));
v___x_1116_ = l_Lean_Expr_const___override(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(lean_object* v_as_1117_, size_t v_sz_1118_, size_t v_i_1119_, lean_object* v_b_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_a_1129_; lean_object* v_pairType_1133_; uint8_t v___x_1134_; 
v_pairType_1133_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1134_ = lean_usize_dec_lt(v_i_1119_, v_sz_1118_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_b_1120_);
return v___x_1135_;
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_array_uget_borrowed(v_as_1117_, v_i_1119_);
v___x_1137_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr(v_a_1136_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
if (lean_obj_tag(v_a_1138_) == 0)
{
lean_object* v_val_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_val_1139_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v_a_1138_, 1);
v___x_1140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__2);
v___x_1141_ = l_Lean_mkApp3(v___x_1140_, v_pairType_1133_, v_b_1120_, v_val_1139_);
v_a_1129_ = v___x_1141_;
goto v___jp_1128_;
}
else
{
lean_object* v_val_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_val_1142_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_val_1142_);
lean_dec_ref_known(v_a_1138_, 1);
v___x_1143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___closed__5);
v___x_1144_ = l_Lean_mkApp3(v___x_1143_, v_pairType_1133_, v_b_1120_, v_val_1142_);
v_a_1129_ = v___x_1144_;
goto v___jp_1128_;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v_b_1120_);
v_a_1145_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1137_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1137_);
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
v___jp_1128_:
{
size_t v___x_1130_; size_t v___x_1131_; 
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_add(v_i_1119_, v___x_1130_);
v_i_1119_ = v___x_1131_;
v_b_1120_ = v_a_1129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0___boxed(lean_object* v_as_1153_, lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
size_t v_sz_boxed_1164_; size_t v_i_boxed_1165_; lean_object* v_res_1166_; 
v_sz_boxed_1164_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1165_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_as_1153_, v_sz_boxed_1164_, v_i_boxed_1165_, v_b_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_as_1153_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(lean_object* v_stxs_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_pairType_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_box(0);
v_pairType_1176_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__6);
v___x_1177_ = l_Lean_Meta_mkArrayLit(v_pairType_1176_, v___x_1175_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; size_t v_sz_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v_sz_1179_ = lean_array_size(v_stxs_1167_);
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs_spec__0(v_stxs_1167_, v_sz_1179_, v___x_1180_, v_a_1178_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1181_;
}
else
{
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs___boxed(lean_object* v_stxs_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_stxs_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec_ref(v_stxs_1182_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(lean_object* v___x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1191_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed(lean_object* v___x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0(v___x_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(lean_object* v_stx_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___y_1219_; lean_object* v_k_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
lean_inc(v_stx_1210_);
v_k_1230_ = l_Lean_Syntax_getKind(v_stx_1210_);
v___x_1231_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__1));
v___x_1232_ = lean_name_eq(v_k_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1___closed__3));
v___x_1234_ = lean_name_eq(v_k_1230_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1236_ = lean_name_eq(v_k_1230_, v___x_1235_);
lean_dec(v_k_1230_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___closed__0));
v___y_1219_ = v___x_1237_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1238_; lean_object* v___f_1239_; 
lean_inc(v_stx_1210_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_stx_1210_);
v___f_1239_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1239_, 0, v___x_1238_);
v___y_1219_ = v___f_1239_;
goto v___jp_1218_;
}
}
else
{
lean_object* v___x_1240_; lean_object* v___f_1241_; 
lean_dec(v_k_1230_);
lean_inc(v_stx_1210_);
v___x_1240_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1240_, 0, v_stx_1210_);
lean_ctor_set_uint8(v___x_1240_, sizeof(void*)*1, v___x_1234_);
v___f_1241_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1241_, 0, v___x_1240_);
v___y_1219_ = v___f_1241_;
goto v___jp_1218_;
}
}
else
{
uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___f_1244_; 
lean_dec(v_k_1230_);
v___x_1242_ = 0;
lean_inc(v_stx_1210_);
v___x_1243_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_1243_, 0, v_stx_1210_);
lean_ctor_set_uint8(v___x_1243_, sizeof(void*)*1, v___x_1242_);
v___f_1244_ = lean_alloc_closure((void*)(l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1244_, 0, v___x_1243_);
v___y_1219_ = v___f_1244_;
goto v___jp_1218_;
}
v___jp_1218_:
{
lean_object* v_toCold_1220_; lean_object* v_currRecDepth_1221_; lean_object* v_ref_1222_; uint16_t v_optionFlags_1223_; uint8_t v_suppressElabErrors_1224_; uint8_t v_checkDeprecated_1225_; uint8_t v_isRecordingDeps_1226_; lean_object* v_ref_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_toCold_1220_ = lean_ctor_get(v___y_1215_, 0);
v_currRecDepth_1221_ = lean_ctor_get(v___y_1215_, 1);
v_ref_1222_ = lean_ctor_get(v___y_1215_, 2);
v_optionFlags_1223_ = lean_ctor_get_uint16(v___y_1215_, sizeof(void*)*3);
v_suppressElabErrors_1224_ = lean_ctor_get_uint8(v___y_1215_, sizeof(void*)*3 + 2);
v_checkDeprecated_1225_ = lean_ctor_get_uint8(v___y_1215_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1226_ = lean_ctor_get_uint8(v___y_1215_, sizeof(void*)*3 + 4);
v_ref_1227_ = l_Lean_replaceRef(v_stx_1210_, v_ref_1222_);
lean_dec(v_stx_1210_);
lean_inc(v_currRecDepth_1221_);
lean_inc_ref(v_toCold_1220_);
v___x_1228_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1228_, 0, v_toCold_1220_);
lean_ctor_set(v___x_1228_, 1, v_currRecDepth_1221_);
lean_ctor_set(v___x_1228_, 2, v_ref_1227_);
lean_ctor_set_uint16(v___x_1228_, sizeof(void*)*3, v_optionFlags_1223_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*3 + 2, v_suppressElabErrors_1224_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*3 + 3, v_checkDeprecated_1225_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*3 + 4, v_isRecordingDeps_1226_);
lean_inc(v___y_1216_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
v___x_1229_ = lean_apply_7(v___y_1219_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___x_1228_, v___y_1216_, lean_box(0));
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2___boxed(lean_object* v_stx_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_stx_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(lean_object* v_as_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_a_1280_; uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_b_1271_);
return v___x_1285_;
}
else
{
lean_object* v_fst_1286_; lean_object* v_snd_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1324_; 
v_fst_1286_ = lean_ctor_get(v_b_1271_, 0);
v_snd_1287_ = lean_ctor_get(v_b_1271_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_b_1271_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1289_ = v_b_1271_;
v_isShared_1290_ = v_isSharedCheck_1324_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_snd_1287_);
lean_inc(v_fst_1286_);
lean_dec(v_b_1271_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1324_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_a_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_a_1291_ = lean_array_uget_borrowed(v_as_1268_, v_i_1270_);
lean_inc(v_a_1291_);
v___x_1292_ = l_Lean_Syntax_getKind(v_a_1291_);
v___x_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__1));
v___x_1294_ = lean_name_eq(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__3));
v___x_1296_ = lean_name_eq(v___x_1292_, v___x_1295_);
lean_dec(v___x_1292_);
if (v___x_1296_ == 0)
{
lean_object* v_tcs_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_tcs_1297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___closed__4));
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_snd_1287_);
v___x_1299_ = lean_array_push(v_fst_1286_, v___x_1298_);
lean_inc(v_a_1291_);
v___x_1300_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_Content_view_viewItem___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__2(v_a_1291_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = lean_array_push(v___x_1299_, v_a_1301_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v_tcs_1297_);
lean_ctor_set(v___x_1289_, 0, v___x_1302_);
v___x_1304_ = v___x_1289_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_tcs_1297_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
v_a_1280_ = v___x_1304_;
goto v___jp_1279_;
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v___x_1299_);
lean_del_object(v___x_1289_);
v_a_1306_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1300_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1300_);
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
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_inc(v_a_1291_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_a_1291_);
v___x_1315_ = lean_array_push(v_snd_1287_, v___x_1314_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v___x_1315_);
v___x_1317_ = v___x_1289_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_fst_1286_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
v_a_1280_ = v___x_1317_;
goto v___jp_1279_;
}
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec(v___x_1292_);
lean_inc(v_a_1291_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_a_1291_);
v___x_1320_ = lean_array_push(v_snd_1287_, v___x_1319_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v___x_1320_);
v___x_1322_ = v___x_1289_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_fst_1286_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
v_a_1280_ = v___x_1322_;
goto v___jp_1279_;
}
}
}
}
v___jp_1279_:
{
size_t v___x_1281_; size_t v___x_1282_; 
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_add(v_i_1270_, v___x_1281_);
v_i_1270_ = v___x_1282_;
v_b_1271_ = v_a_1280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3___boxed(lean_object* v_as_1325_, lean_object* v_sz_1326_, lean_object* v_i_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
size_t v_sz_boxed_1336_; size_t v_i_boxed_1337_; lean_object* v_res_1338_; 
v_sz_boxed_1336_ = lean_unbox_usize(v_sz_1326_);
lean_dec(v_sz_1326_);
v_i_boxed_1337_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_res_1338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v_as_1325_, v_sz_boxed_1336_, v_i_boxed_1337_, v_b_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec_ref(v_as_1325_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(lean_object* v_c_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = l_Lean_Syntax_getArgs(v_c_1343_);
v___x_1353_ = ((lean_object*)(l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___closed__1));
v_sz_1354_ = lean_array_size(v___x_1352_);
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2_spec__3(v___x_1352_, v_sz_1354_, v___x_1355_, v___x_1353_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec_ref(v___x_1352_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1373_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_fst_1361_ = lean_ctor_get(v_a_1357_, 0);
lean_inc(v_fst_1361_);
v_snd_1362_ = lean_ctor_get(v_a_1357_, 1);
lean_inc(v_snd_1362_);
lean_dec(v_a_1357_);
v___x_1363_ = lean_array_get_size(v_snd_1362_);
v___x_1364_ = lean_nat_dec_eq(v___x_1363_, v___x_1351_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v_items_1366_; lean_object* v___x_1368_; 
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_snd_1362_);
v_items_1366_ = lean_array_push(v_fst_1361_, v___x_1365_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_items_1366_);
v___x_1368_ = v___x_1359_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_items_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_object* v___x_1371_; 
lean_dec(v_snd_1362_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_fst_1361_);
v___x_1371_ = v___x_1359_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_fst_1361_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1356_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1356_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2___boxed(lean_object* v_c_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_c_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v_c_1382_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(lean_object* v_stx_1391_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
lean_inc(v_stx_1391_);
v___x_1393_ = l_Lean_Syntax_getKind(v_stx_1391_);
v___x_1394_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__4));
v___x_1395_ = lean_name_eq(v___x_1393_, v___x_1394_);
lean_dec(v___x_1393_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec(v_stx_1391_);
v___x_1396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; size_t v_sz_1400_; size_t v___x_1401_; lean_object* v_attrs_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_startTag_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1397_ = lean_unsigned_to_nat(2u);
v___x_1398_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1397_);
v___x_1399_ = l_Lean_Syntax_getArgs(v___x_1398_);
lean_dec(v___x_1398_);
v_sz_1400_ = lean_array_size(v___x_1399_);
v___x_1401_ = ((size_t)0ULL);
v_attrs_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0_spec__1(v_sz_1400_, v___x_1401_, v___x_1399_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1403_);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1405_);
v___x_1407_ = lean_unsigned_to_nat(3u);
v___x_1408_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1407_);
v_startTag_1409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_startTag_1409_, 0, v___x_1404_);
lean_ctor_set(v_startTag_1409_, 1, v___x_1406_);
lean_ctor_set(v_startTag_1409_, 2, v_attrs_1402_);
lean_ctor_set(v_startTag_1409_, 3, v___x_1408_);
v___x_1410_ = l_Lean_Syntax_getNumArgs(v_stx_1391_);
v___x_1411_ = lean_unsigned_to_nat(4u);
v___x_1412_ = lean_nat_dec_eq(v___x_1410_, v___x_1411_);
lean_dec(v___x_1410_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_endTag_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1413_ = lean_unsigned_to_nat(5u);
v___x_1414_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1413_);
v___x_1415_ = lean_unsigned_to_nat(6u);
v___x_1416_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Html_Syntax_Element_view___at___00Lean_Html_Syntax_Element_checkNamesMatch_spec__0___closed__5));
v___x_1418_ = lean_unsigned_to_nat(7u);
v___x_1419_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1418_);
v_endTag_1420_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_endTag_1420_, 0, v___x_1414_);
lean_ctor_set(v_endTag_1420_, 1, v___x_1416_);
lean_ctor_set(v_endTag_1420_, 2, v___x_1417_);
lean_ctor_set(v_endTag_1420_, 3, v___x_1419_);
v___x_1421_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1411_);
lean_dec(v_stx_1391_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_endTag_1420_);
v___x_1424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1424_, 0, v_startTag_1409_);
lean_ctor_set(v___x_1424_, 1, v___x_1422_);
lean_ctor_set(v___x_1424_, 2, v___x_1423_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v_stx_1391_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1427_, 0, v_startTag_1409_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
lean_ctor_set(v___x_1427_, 2, v___x_1426_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg___boxed(lean_object* v_stx_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1429_);
return v_res_1431_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_box(0);
v___x_1436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__0));
v___x_1437_ = l_Lean_Expr_const___override(v___x_1436_, v___x_1435_);
return v___x_1437_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(uint8_t v___x_1440_, lean_object* v_b_1441_, lean_object* v_tm_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__2);
v___x_1451_ = lean_box(0);
v___x_1452_ = l_Lean_Elab_Term_elabTermEnsuringType(v_tm_1442_, v___x_1450_, v___x_1440_, v___x_1440_, v___x_1451_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1463_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1463_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1463_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1457_ = lean_array_push(v_b_1441_, v_a_1453_);
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___x_1457_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1459_);
v___x_1461_ = v___x_1455_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_b_1441_);
v_a_1464_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1452_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1452_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___boxed(lean_object* v___x_1472_, lean_object* v_b_1473_, lean_object* v_tm_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v___x_17909__boxed_1482_; lean_object* v_res_1483_; 
v___x_17909__boxed_1482_ = lean_unbox(v___x_1472_);
v_res_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_17909__boxed_1482_, v_b_1473_, v_tm_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1483_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__2));
v___x_1493_ = l_Lean_Expr_const___override(v___x_1492_, v___x_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_box(0);
v___x_1500_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__5));
v___x_1501_ = l_Lean_Expr_const___override(v___x_1500_, v___x_1499_);
return v___x_1501_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__0));
v___x_1508_ = l_Lean_Expr_const___override(v___x_1507_, v___x_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__2));
v___x_1515_ = l_Lean_Expr_const___override(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__6));
v___x_1522_ = l_String_toRawSubstring_x27(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(lean_object* v_as_1533_, size_t v_sz_1534_, size_t v_i_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_a_1545_; lean_object* v___y_1550_; uint8_t v___x_1561_; 
v___x_1561_ = lean_usize_dec_lt(v_i_1535_, v_sz_1534_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_b_1536_);
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; 
v_a_1563_ = lean_array_uget_borrowed(v_as_1533_, v_i_1535_);
switch(lean_obj_tag(v_a_1563_))
{
case 0:
{
lean_object* v_stx_1564_; lean_object* v_toCold_1565_; lean_object* v_currRecDepth_1566_; lean_object* v_ref_1567_; uint16_t v_optionFlags_1568_; uint8_t v_suppressElabErrors_1569_; uint8_t v_checkDeprecated_1570_; uint8_t v_isRecordingDeps_1571_; lean_object* v_ref_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_stx_1564_ = lean_ctor_get(v_a_1563_, 0);
v_toCold_1565_ = lean_ctor_get(v___y_1541_, 0);
v_currRecDepth_1566_ = lean_ctor_get(v___y_1541_, 1);
v_ref_1567_ = lean_ctor_get(v___y_1541_, 2);
v_optionFlags_1568_ = lean_ctor_get_uint16(v___y_1541_, sizeof(void*)*3);
v_suppressElabErrors_1569_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 2);
v_checkDeprecated_1570_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1571_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 4);
v_ref_1572_ = l_Lean_replaceRef(v_stx_1564_, v_ref_1567_);
lean_inc(v_currRecDepth_1566_);
lean_inc_ref(v_toCold_1565_);
v___x_1573_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1573_, 0, v_toCold_1565_);
lean_ctor_set(v___x_1573_, 1, v_currRecDepth_1566_);
lean_ctor_set(v___x_1573_, 2, v_ref_1572_);
lean_ctor_set_uint16(v___x_1573_, sizeof(void*)*3, v_optionFlags_1568_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*3 + 2, v_suppressElabErrors_1569_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*3 + 3, v_checkDeprecated_1570_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*3 + 4, v_isRecordingDeps_1571_);
lean_inc(v_stx_1564_);
v___x_1574_ = l_Lean_Html_Syntax_Element_checkNamesMatch(v_stx_1564_, v___x_1573_, v___y_1542_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1574_, 1);
lean_inc(v_stx_1564_);
v___x_1575_ = l_Lean_Html_Syntax_Element_checkNoVoidChildren(v_stx_1564_, v___x_1573_, v___y_1542_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref_known(v___x_1575_, 1);
lean_inc(v_stx_1564_);
v___x_1576_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1564_);
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
v___x_1584_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrs(v_attrs_1581_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___x_1573_, v___y_1542_);
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
v___x_1603_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_val_1599_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___x_1573_, v___y_1542_);
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
lean_dec_ref(v_b_1536_);
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
v___x_1591_ = lean_array_push(v_b_1536_, v___x_1590_);
v_a_1545_ = v___x_1591_;
goto v___jp_1544_;
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
lean_dec_ref(v_b_1536_);
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
lean_dec_ref(v_b_1536_);
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
lean_dec_ref(v_b_1536_);
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
lean_dec_ref(v_b_1536_);
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
lean_dec_ref(v_b_1536_);
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
lean_object* v_stx_1657_; lean_object* v_toCold_1658_; lean_object* v_currRecDepth_1659_; lean_object* v_ref_1660_; uint16_t v_optionFlags_1661_; uint8_t v_suppressElabErrors_1662_; uint8_t v_checkDeprecated_1663_; uint8_t v_isRecordingDeps_1664_; lean_object* v___x_1665_; lean_object* v_ref_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_stx_1657_ = lean_ctor_get(v_a_1563_, 0);
v_toCold_1658_ = lean_ctor_get(v___y_1541_, 0);
v_currRecDepth_1659_ = lean_ctor_get(v___y_1541_, 1);
v_ref_1660_ = lean_ctor_get(v___y_1541_, 2);
v_optionFlags_1661_ = lean_ctor_get_uint16(v___y_1541_, sizeof(void*)*3);
v_suppressElabErrors_1662_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 2);
v_checkDeprecated_1663_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1664_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 4);
lean_inc_ref(v_stx_1657_);
v___x_1665_ = l_Lean_Html_Syntax_TextCommentsView_getSyntax(v_stx_1657_);
v_ref_1666_ = l_Lean_replaceRef(v___x_1665_, v_ref_1660_);
lean_dec(v___x_1665_);
lean_inc(v_currRecDepth_1659_);
lean_inc_ref(v_toCold_1658_);
v___x_1667_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1667_, 0, v_toCold_1658_);
lean_ctor_set(v___x_1667_, 1, v_currRecDepth_1659_);
lean_ctor_set(v___x_1667_, 2, v_ref_1666_);
lean_ctor_set_uint16(v___x_1667_, sizeof(void*)*3, v_optionFlags_1661_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*3 + 2, v_suppressElabErrors_1662_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*3 + 3, v_checkDeprecated_1663_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*3 + 4, v_isRecordingDeps_1664_);
v___x_1668_ = l_Lean_Html_Syntax_TextCommentsView_getText(v_stx_1657_, v___x_1667_, v___y_1542_);
lean_dec_ref_known(v___x_1667_, 3);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = lean_string_utf8_byte_size(v_a_1669_);
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = lean_nat_dec_eq(v___x_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__3);
v___x_1674_ = l_Lean_mkStrLit(v_a_1669_);
v___x_1675_ = l_Lean_Expr_app___override(v___x_1673_, v___x_1674_);
v___x_1676_ = lean_array_push(v_b_1536_, v___x_1675_);
v_a_1545_ = v___x_1676_;
goto v___jp_1544_;
}
else
{
lean_dec(v_a_1669_);
v_a_1545_ = v_b_1536_;
goto v___jp_1544_;
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec_ref(v_b_1536_);
v_a_1677_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1668_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1668_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
default: 
{
uint8_t v_isMany_1685_; lean_object* v_stx_1686_; lean_object* v_toCold_1687_; lean_object* v_currRecDepth_1688_; lean_object* v_ref_1689_; uint16_t v_optionFlags_1690_; uint8_t v_suppressElabErrors_1691_; uint8_t v_checkDeprecated_1692_; uint8_t v_isRecordingDeps_1693_; lean_object* v_ref_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_isMany_1685_ = lean_ctor_get_uint8(v_a_1563_, sizeof(void*)*1);
v_stx_1686_ = lean_ctor_get(v_a_1563_, 0);
v_toCold_1687_ = lean_ctor_get(v___y_1541_, 0);
v_currRecDepth_1688_ = lean_ctor_get(v___y_1541_, 1);
v_ref_1689_ = lean_ctor_get(v___y_1541_, 2);
v_optionFlags_1690_ = lean_ctor_get_uint16(v___y_1541_, sizeof(void*)*3);
v_suppressElabErrors_1691_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 2);
v_checkDeprecated_1692_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1693_ = lean_ctor_get_uint8(v___y_1541_, sizeof(void*)*3 + 4);
v_ref_1694_ = l_Lean_replaceRef(v_stx_1686_, v_ref_1689_);
lean_inc(v_ref_1694_);
lean_inc(v_currRecDepth_1688_);
lean_inc_ref(v_toCold_1687_);
v___x_1695_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1695_, 0, v_toCold_1687_);
lean_ctor_set(v___x_1695_, 1, v_currRecDepth_1688_);
lean_ctor_set(v___x_1695_, 2, v_ref_1694_);
lean_ctor_set_uint16(v___x_1695_, sizeof(void*)*3, v_optionFlags_1690_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*3 + 2, v_suppressElabErrors_1691_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*3 + 3, v_checkDeprecated_1692_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*3 + 4, v_isRecordingDeps_1693_);
lean_inc(v_stx_1686_);
v___x_1696_ = l_Lean_Html_Syntax_Interp_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__1(v_isMany_1685_, v_stx_1686_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___x_1695_, v___y_1542_);
if (lean_obj_tag(v___x_1696_) == 0)
{
if (v_isMany_1685_ == 0)
{
lean_object* v_a_1697_; lean_object* v_term_1698_; lean_object* v___x_1699_; 
lean_dec(v_ref_1694_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v_term_1698_ = lean_ctor_get(v_a_1697_, 1);
lean_inc(v_term_1698_);
lean_dec(v_a_1697_);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1561_, v_b_1536_, v_term_1698_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___x_1695_, v___y_1542_);
lean_dec_ref_known(v___x_1695_, 3);
v___y_1550_ = v___x_1699_;
goto v___jp_1549_;
}
else
{
lean_object* v_a_1700_; lean_object* v_quotContext_1701_; lean_object* v_currMacroScope_1702_; lean_object* v_term_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_a_1700_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1696_, 1);
v_quotContext_1701_ = lean_ctor_get(v_toCold_1687_, 8);
v_currMacroScope_1702_ = lean_ctor_get(v_toCold_1687_, 9);
v_term_1703_ = lean_ctor_get(v_a_1700_, 1);
lean_inc(v_term_1703_);
lean_dec(v_a_1700_);
v___x_1704_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__19));
v___x_1705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__5));
v___x_1706_ = 0;
v___x_1707_ = l_Lean_SourceInfo_fromRef(v_ref_1694_, v___x_1706_);
lean_dec(v_ref_1694_);
v___x_1708_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__7);
lean_inc(v_currMacroScope_1702_);
lean_inc(v_quotContext_1701_);
v___x_1709_ = l_Lean_addMacroScope(v_quotContext_1701_, v___x_1705_, v_currMacroScope_1702_);
v___x_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___closed__10));
lean_inc_n(v___x_1707_, 2);
v___x_1711_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1707_);
lean_ctor_set(v___x_1711_, 1, v___x_1708_);
lean_ctor_set(v___x_1711_, 2, v___x_1709_);
lean_ctor_set(v___x_1711_, 3, v___x_1710_);
v___x_1712_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr___closed__46));
v___x_1713_ = l_Lean_Syntax_node1(v___x_1707_, v___x_1712_, v_term_1703_);
v___x_1714_ = l_Lean_Syntax_node2(v___x_1707_, v___x_1704_, v___x_1711_, v___x_1713_);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0(v___x_1561_, v_b_1536_, v___x_1714_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___x_1695_, v___y_1542_);
lean_dec_ref_known(v___x_1695_, 3);
v___y_1550_ = v___x_1715_;
goto v___jp_1549_;
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref_known(v___x_1695_, 3);
lean_dec(v_ref_1694_);
lean_dec_ref(v_b_1536_);
v_a_1716_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1696_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1696_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
v___jp_1544_:
{
size_t v___x_1546_; size_t v___x_1547_; 
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1535_, v___x_1546_);
v_i_1535_ = v___x_1547_;
v_b_1536_ = v_a_1545_;
goto _start;
}
v___jp_1549_:
{
if (lean_obj_tag(v___y_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v_snd_1552_; 
v_a_1551_ = lean_ctor_get(v___y_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___y_1550_, 1);
v_snd_1552_ = lean_ctor_get(v_a_1551_, 1);
lean_inc(v_snd_1552_);
lean_dec(v_a_1551_);
v_a_1545_ = v_snd_1552_;
goto v___jp_1544_;
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v_a_1553_ = lean_ctor_get(v___y_1550_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___y_1550_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___y_1550_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___y_1550_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(lean_object* v_stx_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_toCold_1732_; lean_object* v_currRecDepth_1733_; lean_object* v_ref_1734_; uint16_t v_optionFlags_1735_; uint8_t v_suppressElabErrors_1736_; uint8_t v_checkDeprecated_1737_; uint8_t v_isRecordingDeps_1738_; lean_object* v___x_1739_; lean_object* v_es_1740_; lean_object* v_ref_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_toCold_1732_ = lean_ctor_get(v_a_1729_, 0);
v_currRecDepth_1733_ = lean_ctor_get(v_a_1729_, 1);
v_ref_1734_ = lean_ctor_get(v_a_1729_, 2);
v_optionFlags_1735_ = lean_ctor_get_uint16(v_a_1729_, sizeof(void*)*3);
v_suppressElabErrors_1736_ = lean_ctor_get_uint8(v_a_1729_, sizeof(void*)*3 + 2);
v_checkDeprecated_1737_ = lean_ctor_get_uint8(v_a_1729_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1738_ = lean_ctor_get_uint8(v_a_1729_, sizeof(void*)*3 + 4);
v___x_1739_ = lean_unsigned_to_nat(0u);
v_es_1740_ = ((lean_object*)(l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__0));
v_ref_1741_ = l_Lean_replaceRef(v_stx_1724_, v_ref_1734_);
lean_inc(v_currRecDepth_1733_);
lean_inc_ref(v_toCold_1732_);
v___x_1742_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1742_, 0, v_toCold_1732_);
lean_ctor_set(v___x_1742_, 1, v_currRecDepth_1733_);
lean_ctor_set(v___x_1742_, 2, v_ref_1741_);
lean_ctor_set_uint16(v___x_1742_, sizeof(void*)*3, v_optionFlags_1735_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*3 + 2, v_suppressElabErrors_1736_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*3 + 3, v_checkDeprecated_1737_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*3 + 4, v_isRecordingDeps_1738_);
v___x_1743_ = l_Lean_Html_Syntax_Content_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__2(v_stx_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___x_1742_, v_a_1730_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; size_t v_sz_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v_sz_1745_ = lean_array_size(v_a_1744_);
v___x_1746_ = ((size_t)0ULL);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_a_1744_, v_sz_1745_, v___x_1746_, v_es_1740_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v___x_1742_, v_a_1730_);
lean_dec(v_a_1744_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1771_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1771_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1771_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = lean_array_get_size(v_a_1748_);
v___x_1753_ = lean_nat_dec_eq(v___x_1752_, v___x_1739_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_del_object(v___x_1750_);
v___x_1754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___lam__0___closed__1);
v___x_1755_ = lean_array_to_list(v_a_1748_);
v___x_1756_ = l_Lean_Meta_mkArrayLit(v___x_1754_, v___x_1755_, v_a_1727_, v_a_1728_, v___x_1742_, v_a_1730_);
lean_dec_ref_known(v___x_1742_, 3);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1766_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1761_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__3);
v___x_1762_ = l_Lean_Expr_app___override(v___x_1761_, v_a_1757_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1762_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
return v___x_1756_;
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
lean_dec(v_a_1748_);
lean_dec_ref_known(v___x_1742_, 3);
v___x_1767_ = lean_obj_once(&l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6, &l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6_once, _init_l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___closed__6);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1767_);
v___x_1769_ = v___x_1750_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
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
lean_dec_ref_known(v___x_1742_, 3);
v_a_1772_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1747_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1747_);
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
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref_known(v___x_1742_, 3);
v_a_1780_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1743_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1743_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent___boxed(lean_object* v_stx_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_stx_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_stx_1788_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3___boxed(lean_object* v_as_1797_, lean_object* v_sz_1798_, lean_object* v_i_1799_, lean_object* v_b_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
size_t v_sz_boxed_1808_; size_t v_i_boxed_1809_; lean_object* v_res_1810_; 
v_sz_boxed_1808_ = lean_unbox_usize(v_sz_1798_);
lean_dec(v_sz_1798_);
v_i_boxed_1809_ = lean_unbox_usize(v_i_1799_);
lean_dec(v_i_1799_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__3(v_as_1797_, v_sz_boxed_1808_, v_i_boxed_1809_, v_b_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_as_1797_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(lean_object* v_stx_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___redArg(v_stx_1811_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0___boxed(lean_object* v_stx_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Html_Syntax_Element_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__0(v_stx_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg___boxed(lean_object* v_a_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___redArg(v_a_1832_);
lean_dec(v_a_1832_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(lean_object* v_a_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l___private_Lean_Data_Html_Syntax_0__Lean_Html_Syntax_viewNodeAtom___at___00Lean_Html_Syntax_AttrName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttr_spec__1_spec__1___redArg(v_a_1835_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1___boxed(lean_object* v_a_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Html_Syntax_TagName_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent_spec__1(v_a_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v_a_1844_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(lean_object* v_stx_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__1));
lean_inc(v_stx_1865_);
v___x_1874_ = l_Lean_Syntax_isOfKind(v_stx_1865_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
lean_dec(v_stx_1865_);
v___x_1875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; lean_object* v_h_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1876_ = lean_unsigned_to_nat(2u);
v_h_1877_ = l_Lean_Syntax_getArg(v_stx_1865_, v___x_1876_);
lean_dec(v_stx_1865_);
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___closed__3));
lean_inc(v_h_1877_);
v___x_1879_ = l_Lean_Syntax_isOfKind(v_h_1877_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec(v_h_1877_);
v___x_1880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Html_Syntax_AttrVal_view___at___00__private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabAttrVal_spec__0_spec__0___redArg();
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = l___private_Lean_Data_Html_Elab_0__Lean_Elab_Html_elabContent(v_h_1877_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_h_1877_);
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg___boxed(lean_object* v_stx_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(lean_object* v_stx_1891_, lean_object* v_x_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___redArg(v_stx_1891_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1___boxed(lean_object* v_stx_1901_, lean_object* v_x_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Elab_Html___aux__Lean__Data__Html__Elab______elabRules__Lean__Html__Syntax__html_x25__1(v_stx_1901_, v_x_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_x_1902_);
return v_res_1910_;
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
